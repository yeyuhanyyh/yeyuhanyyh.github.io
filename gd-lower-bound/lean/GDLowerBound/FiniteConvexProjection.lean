import Mathlib

/-!
# Projection onto a finite convex hull

This file develops the convex-analytic fact needed for the Ma--Chen support-envelope
hard instance without using an external Moreau-envelope theorem.
-/

namespace GDLowerBound

noncomputable section

open scoped BigOperators InnerProductSpace
open Set Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact convex set presented as the convex hull of finitely many vertices and containing zero. -/
structure FiniteConvexSet (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vertices : Finset E
  zero_mem : (0 : E) ∈ vertices

namespace FiniteConvexSet

variable (K : FiniteConvexSet E)

/-- The convex hull of the listed vertices. -/
def carrier : Set E := convexHull ℝ (K.vertices : Set E)

lemma carrier_nonempty : K.carrier.Nonempty := by
  refine ⟨0, ?_⟩
  exact subset_convexHull ℝ (K.vertices : Set E) (by simpa using K.zero_mem)

lemma zero_mem_carrier : (0 : E) ∈ K.carrier := K.carrier_nonempty.some_mem

lemma carrier_convex : Convex ℝ K.carrier := convex_convexHull ℝ _

lemma carrier_compact : IsCompact K.carrier := by
  exact K.vertices.finite_toSet.isCompact_convexHull ℝ

lemma carrier_complete : IsComplete K.carrier := K.carrier_compact.isComplete

/-- The metric projection onto the finite convex hull. -/
def proj (x : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex K.carrier_nonempty K.carrier_complete
      K.carrier_convex x)

lemma proj_mem (x : E) : K.proj x ∈ K.carrier :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.carrier_nonempty K.carrier_complete
      K.carrier_convex x)).1

lemma proj_minimal (x : E) :
    ‖x - K.proj x‖ = ⨅ y : K.carrier, ‖x - y‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.carrier_nonempty K.carrier_complete
      K.carrier_convex x)).2

/-- Variational characterization of the projection. -/
lemma proj_variational (x : E) :
    ∀ y ∈ K.carrier, inner ℝ (x - K.proj x) (y - K.proj x) ≤ 0 := by
  exact
    (norm_eq_iInf_iff_real_inner_le_zero K.carrier_convex (K.proj_mem x)).1
      (K.proj_minimal x)

lemma proj_zero : K.proj 0 = 0 := by
  have hzero := K.zero_mem_carrier
  have h := K.proj_minimal (0 : E)
  have hle : (⨅ y : K.carrier, ‖(0 : E) - y‖) ≤ 0 := by
    exact ciInf_le_of_le ⟨0, hzero⟩ (by simp)
  have hnorm : ‖K.proj 0‖ = 0 := by
    have hnonneg : 0 ≤ (⨅ y : K.carrier, ‖(0 : E) - y‖) := by
      exact le_ciInf fun y => norm_nonneg _
    have : (⨅ y : K.carrier, ‖(0 : E) - y‖) = 0 := le_antisymm hle hnonneg
    simpa [this] using h
  exact norm_eq_zero.mp hnorm

/-- Firm nonexpansiveness inequality for metric projection onto a convex set. -/
lemma norm_proj_sub_sq_le_inner (x y : E) :
    ‖K.proj x - K.proj y‖ ^ 2
      ≤ inner ℝ (K.proj x - K.proj y) (x - y) := by
  have hx := K.proj_variational x (K.proj y) (K.proj_mem y)
  have hy := K.proj_variational y (K.proj x) (K.proj_mem x)
  rw [← real_inner_comm] at hx hy
  have hsum :
      inner ℝ (K.proj x - K.proj y) (x - y)
        - inner ℝ (K.proj x - K.proj y) (K.proj x - K.proj y) ≥ 0 := by
    rw [inner_sub_right, inner_sub_left, inner_sub_right, inner_sub_left] at hx hy ⊢
    rw [real_inner_comm (K.proj x) x, real_inner_comm (K.proj x) y,
      real_inner_comm (K.proj y) x, real_inner_comm (K.proj y) y] at hx hy ⊢
    linarith
  rw [inner_self_eq_norm_sq_to_K] at hsum
  exact sub_nonneg.mp hsum

/-- Projection onto a finite convex hull is nonexpansive. -/
lemma norm_proj_sub_le (x y : E) : ‖K.proj x - K.proj y‖ ≤ ‖x - y‖ := by
  by_cases hxy : K.proj x = K.proj y
  · simp [hxy]
  have hp : 0 < ‖K.proj x - K.proj y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hfirm := K.norm_proj_sub_sq_le_inner x y
  have hcs :
      inner ℝ (K.proj x - K.proj y) (x - y)
        ≤ ‖K.proj x - K.proj y‖ * ‖x - y‖ := real_inner_le_norm _ _
  have hmul :
      ‖K.proj x - K.proj y‖ ^ 2
        ≤ ‖K.proj x - K.proj y‖ * ‖x - y‖ := hfirm.trans hcs
  nlinarith

/-- The support-envelope objective at a candidate gradient. -/
def affineValue (g x : E) : ℝ := inner ℝ g x - (1 / 2 : ℝ) * ‖g‖ ^ 2

/-- The support-envelope function, expressed using the unique projection maximizer. -/
def envelope (x : E) : ℝ := K.affineValue (K.proj x) x

lemma affineValue_le_envelope {g : E} (hg : g ∈ K.carrier) (x : E) :
    K.affineValue g x ≤ K.envelope x := by
  have hv := K.proj_variational x g hg
  have hid :
      K.affineValue g x - K.affineValue (K.proj x) x
        = inner ℝ (x - K.proj x) (g - K.proj x)
          - (1 / 2 : ℝ) * ‖g - K.proj x‖ ^ 2 := by
    simp only [affineValue]
    rw [real_inner_comm g x, real_inner_comm (K.proj x) x]
    rw [inner_sub_left, inner_sub_right, inner_sub_left]
    rw [inner_self_eq_norm_sq_to_K]
    rw [norm_sub_sq_real]
    ring
  rw [envelope, ← sub_nonneg]
  rw [hid]
  have hnorm : 0 ≤ ‖g - K.proj x‖ ^ 2 := sq_nonneg _
  linarith

lemma envelope_nonneg (x : E) : 0 ≤ K.envelope x := by
  have h := K.affineValue_le_envelope K.zero_mem_carrier x
  simpa [affineValue] using h

lemma envelope_zero : K.envelope 0 = 0 := by
  simp [envelope, proj_zero, affineValue]

/-- Convexity of the support envelope. -/
lemma convex_envelope : ConvexOn ℝ Set.univ K.envelope := by
  intro x _ y _ a b ha hb hab
  have hp := K.proj_mem (a • x + b • y)
  calc
    K.envelope (a • x + b • y)
        = a * K.affineValue (K.proj (a • x + b • y)) x
          + b * K.affineValue (K.proj (a • x + b • y)) y := by
            simp only [envelope, affineValue, inner_add_right, real_inner_smul_right,
              norm_smul]
            rw [abs_of_nonneg ha, abs_of_nonneg hb]
            nlinarith [hab]
    _ ≤ a * K.envelope x + b * K.envelope y := by
      gcongr
      · exact K.affineValue_le_envelope hp x
      · exact K.affineValue_le_envelope hp y

/-- First-order error bound.  It implies differentiability with gradient `proj x`. -/
lemma envelope_first_order_error (x h : E) :
    0 ≤ K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h ∧
    K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h ≤ ‖h‖ ^ 2 := by
  constructor
  · have hlow := K.affineValue_le_envelope (K.proj_mem x) (x + h)
    simp only [envelope, affineValue, inner_add_right] at hlow ⊢
    linarith
  · have hupp := K.affineValue_le_envelope (K.proj_mem (x + h)) x
    have hdiff :
        K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h
          ≤ inner ℝ (K.proj (x + h) - K.proj x) h := by
      simp only [envelope, affineValue, inner_add_right] at hupp ⊢
      rw [inner_sub_left]
      linarith
    calc
      K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h
          ≤ inner ℝ (K.proj (x + h) - K.proj x) h := hdiff
      _ ≤ ‖K.proj (x + h) - K.proj x‖ * ‖h‖ := real_inner_le_norm _ _
      _ ≤ ‖h‖ * ‖h‖ := by
        gcongr
        simpa only [add_sub_cancel_left] using K.norm_proj_sub_le (x + h) x
      _ = ‖h‖ ^ 2 := by ring

/-- The support envelope is Fréchet differentiable and its gradient is the metric projection. -/
lemma hasFDerivAt_envelope (x : E) :
    HasFDerivAt K.envelope ((innerSL ℝ (K.proj x)).toContinuousLinearMap) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbound : ∀ h : E,
      ‖K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h‖ ≤ ‖h‖ ^ 2 := by
    intro h
    rcases K.envelope_first_order_error x h with ⟨h0, h1⟩
    rw [norm_of_nonneg h0]
    exact h1
  refine (isLittleO_norm_left.2 ?_).congr' ?_ (Eventually.of_forall fun _ => rfl)
  · exact isLittleO_pow_two_id
  · filter_upwards with h
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_toContinuousLinearMap,
      innerSL_apply_apply]
    exact congrArg id rfl

lemma differentiable_envelope : Differentiable ℝ K.envelope :=
  fun x => (K.hasFDerivAt_envelope x).differentiableAt

/-- The gradient of the support envelope is one-Lipschitz. -/
lemma gradient_lipschitz : LipschitzWith 1 K.proj := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simpa [dist_eq_norm] using K.norm_proj_sub_le x y

end FiniteConvexSet

end

end GDLowerBound
