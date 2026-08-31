import GDLowerBound.FiniteConvexProjection
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Convexity and smoothness of the finite support envelope
-/

namespace GDLowerBound

noncomputable section

open scoped InnerProductSpace
open Set Real Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace FiniteConvexSet

variable (K : FiniteConvexSet E)

/-- The support envelope is convex because it is the pointwise supremum of affine functions. -/
lemma convex_envelope : ConvexOn ℝ Set.univ K.envelope := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let p := K.proj (a • x + b • y)
  have hp : p ∈ K.carrier := K.proj_mem _
  have hid :
      K.envelope (a • x + b • y)
        = a * affineValue p x + b * affineValue p y := by
    simp only [envelope, p, affineValue, inner_add_right, real_inner_smul_right]
    nlinarith [hab]
  rw [hid]
  have hx' := mul_le_mul_of_nonneg_left (K.affineValue_le_envelope hp x) ha
  have hy' := mul_le_mul_of_nonneg_left (K.affineValue_le_envelope hp y) hb
  simpa [smul_eq_mul] using add_le_add hx' hy'

/-- Quadratic first-order error estimate for the support envelope. -/
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

/-- The support envelope has gradient equal to the metric projection. -/
lemma hasGradientAt_envelope (x : E) : HasGradientAt K.envelope (K.proj x) x := by
  rw [hasGradientAt_iff_tendsto]
  let err : E → ℝ := fun h =>
    K.envelope (x + h) - K.envelope x - inner ℝ (K.proj x) h
  have hbound : ∀ h : E, ‖h‖⁻¹ * ‖err h‖ ≤ ‖h‖ := by
    intro h
    by_cases hz : h = 0
    · subst h
      simp [err]
    · have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
      rcases K.envelope_first_order_error x h with ⟨he0, he1⟩
      have hnormerr : ‖err h‖ = err h := norm_of_nonneg he0
      rw [hnormerr]
      have hmul := mul_le_mul_of_nonneg_left he1 (inv_nonneg.mpr hn.le)
      calc
        ‖h‖⁻¹ * err h ≤ ‖h‖⁻¹ * ‖h‖ ^ 2 := hmul
        _ = ‖h‖ := by field_simp [ne_of_gt hn]
  let g : E → ℝ := fun y => ‖y - x‖
  apply squeeze_zero'
  · exact Eventually.of_forall fun y =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg (y - x))) (norm_nonneg _)
  · exact Eventually.of_forall fun y => by
      simpa [err, g, add_sub_cancel_left] using hbound (y - x)
  · have hsub : Tendsto (fun y : E => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub tendsto_const_nhds :
        Tendsto (fun y : E => y - x) (𝓝 x) (𝓝 (x - x)))
    exact tendsto_norm_zero.comp hsub

lemma differentiable_envelope : Differentiable ℝ K.envelope :=
  fun x => (K.hasGradientAt_envelope x).differentiableAt

lemma gradient_envelope (x : E) : gradient K.envelope x = K.proj x :=
  (K.hasGradientAt_envelope x).gradient

/-- The support envelope is convex and one-smooth. -/
theorem envelope_convex_one_smooth :
    ConvexOn ℝ Set.univ K.envelope ∧
      Differentiable ℝ K.envelope ∧
      LipschitzWith 1 (gradient K.envelope) := by
  refine ⟨K.convex_envelope, K.differentiable_envelope, ?_⟩
  have hfun : gradient K.envelope = K.proj := funext K.gradient_envelope
  rw [hfun]
  exact K.gradient_lipschitz

end FiniteConvexSet

end

end GDLowerBound
