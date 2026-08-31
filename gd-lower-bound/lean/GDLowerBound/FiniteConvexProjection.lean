import Mathlib

/-!
# Projection onto a finite convex hull

This file develops the metric-projection facts needed for the orthogonal
support-envelope hard instance.
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

lemma zero_mem_carrier : (0 : E) ∈ K.carrier := by
  exact subset_convexHull ℝ (K.vertices : Set E) (by simpa using K.zero_mem)

lemma carrier_convex : Convex ℝ K.carrier := convex_convexHull ℝ _

lemma carrier_compact : IsCompact K.carrier :=
  K.vertices.finite_toSet.isCompact_convexHull ℝ

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

/-- A point of the hull satisfying the projection variational inequality is the chosen projection. -/
lemma proj_eq_of_variational {x p : E} (hp : p ∈ K.carrier)
    (hvar : ∀ y ∈ K.carrier, inner ℝ (x - p) (y - p) ≤ 0) :
    K.proj x = p := by
  have h1 := K.proj_variational x p hp
  have h2 := hvar (K.proj x) (K.proj_mem x)
  have hid :
      inner ℝ (x - K.proj x) (p - K.proj x) +
          inner ℝ (x - p) (K.proj x - p)
        = inner ℝ (K.proj x - p) (K.proj x - p) := by
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm p (K.proj x)]
    ring
  have hinner : inner ℝ (K.proj x - p) (K.proj x - p) ≤ 0 := by
    rw [← hid]
    linarith
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖K.proj x - p‖ ^ 2 = 0 :=
    le_antisymm hinner (sq_nonneg _)
  have hnorm : ‖K.proj x - p‖ = 0 := by
    nlinarith [norm_nonneg (K.proj x - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- It suffices to check the variational inequality on the listed vertices. -/
lemma proj_eq_of_vertex_inequalities {x p : E} (hp : p ∈ K.carrier)
    (hvertices : ∀ g ∈ K.vertices, inner ℝ (x - p) (g - p) ≤ 0) :
    K.proj x = p := by
  let C : Set E := {g | inner ℝ (x - p) (g - p) ≤ 0}
  have hCconvex : Convex ℝ C := by
    intro a ha b hb u v hu hv huv
    change inner ℝ (x - p) (u • a + v • b - p) ≤ 0
    change inner ℝ (x - p) (a - p) ≤ 0 at ha
    change inner ℝ (x - p) (b - p) ≤ 0 at hb
    have hvec : u • a + v • b - p = u • (a - p) + v • (b - p) := by
      calc
        u • a + v • b - p = u • a + v • b - (u + v) • p := by rw [huv, one_smul]
        _ = u • (a - p) + v • (b - p) := by module
    rw [hvec, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu ha)
      (mul_nonpos_of_nonneg_of_nonpos hv hb)
  have hsub : K.carrier ⊆ C := by
    apply convexHull_min
    · intro g hg
      exact hvertices g hg
    · exact hCconvex
  apply K.proj_eq_of_variational hp
  intro y hy
  exact hsub hy

lemma proj_zero : K.proj 0 = 0 := by
  apply K.proj_eq_of_variational K.zero_mem_carrier
  intro y hy
  simp

/-- Firm nonexpansiveness inequality for metric projection onto a convex set. -/
lemma norm_proj_sub_sq_le_inner (x y : E) :
    ‖K.proj x - K.proj y‖ ^ 2
      ≤ inner ℝ (K.proj x - K.proj y) (x - y) := by
  let d := K.proj x - K.proj y
  have hx0 := K.proj_variational x (K.proj y) (K.proj_mem y)
  have hy0 := K.proj_variational y (K.proj x) (K.proj_mem x)
  have hx : 0 ≤ inner ℝ d (x - K.proj x) := by
    have : inner ℝ (x - K.proj x) (-d) ≤ 0 := by simpa [d] using hx0
    rw [real_inner_comm, inner_neg_left] at this
    linarith
  have hy : 0 ≤ inner ℝ d (K.proj y - y) := by
    have : inner ℝ (y - K.proj y) d ≤ 0 := by simpa [d] using hy0
    rw [real_inner_comm] at this
    have hneg : K.proj y - y = -(y - K.proj y) := by module
    rw [hneg, inner_neg_right]
    linarith
  have hdecomp : x - y = (x - K.proj x) + d + (K.proj y - y) := by
    simp [d]
    module
  rw [hdecomp, inner_add_right, inner_add_right]
  rw [show inner ℝ d d = ‖d‖ ^ 2 by simp [inner_self_eq_norm_sq_to_K]]
  linarith

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
def envelope (x : E) : ℝ := affineValue (K.proj x) x

lemma affineValue_le_envelope {g : E} (hg : g ∈ K.carrier) (x : E) :
    affineValue g x ≤ K.envelope x := by
  have hv := K.proj_variational x g hg
  have hid :
      affineValue g x - affineValue (K.proj x) x
        = inner ℝ (x - K.proj x) (g - K.proj x)
          - (1 / 2 : ℝ) * ‖g - K.proj x‖ ^ 2 := by
    simp only [affineValue, inner_sub_left, inner_sub_right]
    rw [norm_sub_sq_real]
    rw [real_inner_comm x g, real_inner_comm x (K.proj x),
      real_inner_comm (K.proj x) g]
    ring
  rw [envelope, ← sub_nonpos, hid]
  nlinarith [sq_nonneg ‖g - K.proj x‖]

lemma envelope_nonneg (x : E) : 0 ≤ K.envelope x := by
  have h := K.affineValue_le_envelope K.zero_mem_carrier x
  simpa [affineValue] using h

lemma envelope_zero : K.envelope 0 = 0 := by
  simp [envelope, K.proj_zero, affineValue]

/-- Squared-distance value formula for the support envelope. -/
lemma envelope_eq_norm_sub_dist (x : E) :
    K.envelope x = (1 / 2 : ℝ) * ‖x‖ ^ 2 - (1 / 2 : ℝ) * ‖x - K.proj x‖ ^ 2 := by
  simp only [envelope, affineValue]
  rw [norm_sub_sq_real, real_inner_comm x (K.proj x)]
  ring

/-- The projection, hence the gradient once differentiability is established, is one-Lipschitz. -/
lemma gradient_lipschitz : LipschitzWith 1 K.proj := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simpa [dist_eq_norm] using K.norm_proj_sub_le x y

end FiniteConvexSet

end

end GDLowerBound
