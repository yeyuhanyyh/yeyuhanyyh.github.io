import YeGDLowerBound.Definitions

/-!
# Scalar optimizer representation of `Gamma_lambda`
-/

namespace YeGDLowerBound

noncomputable section

open Real Set Filter Topology

/-- Positive solution of `x (w+x)=w tau`. -/
def optX (w tau : ℝ) : ℝ :=
  (Real.sqrt (w ^ 2 + 4 * w * tau) - w) / 2

/-- `w + optX w tau`. -/
def optA (w tau : ℝ) : ℝ :=
  (w + Real.sqrt (w ^ 2 + 4 * w * tau)) / 2

lemma optA_eq_add_optX (w tau : ℝ) : optA w tau = w + optX w tau := by
  simp only [optA, optX]
  ring

lemma radicand_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < w ^ 2 + 4 * w * tau := by
  nlinarith [sq_nonneg w, mul_pos hw ht]

lemma optX_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < optX w tau := by
  let R := w ^ 2 + 4 * w * tau
  have hR : 0 ≤ R := (radicand_pos hw ht).le
  have hsquare : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hsnonneg : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  unfold optX
  change 0 < (Real.sqrt R - w) / 2
  nlinarith [mul_pos hw ht]

lemma optA_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < optA w tau := by
  rw [optA_eq_add_optX]
  exact add_pos hw (optX_pos hw ht)

lemma optX_mul_optA {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    optX w tau * optA w tau = w * tau := by
  have hR : 0 ≤ w ^ 2 + 4 * w * tau := (radicand_pos hw ht).le
  have hsquare :
      Real.sqrt (w ^ 2 + 4 * w * tau) ^ 2 = w ^ 2 + 4 * w * tau :=
    Real.sq_sqrt hR
  unfold optX optA
  nlinarith

/-- The scalar first-order equation. -/
def rootEq (lam w z tau : ℝ) : ℝ :=
  1 / (2 * tau) + 1 / (optA w tau + optA z tau) - lam

/-- The elementary identity converting the quadratic parameterization to the FOC. -/
lemma inv_optX_sub_inv_optA {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    1 / (2 * optX w tau) - 1 / (2 * optA w tau) = 1 / (2 * tau) := by
  have hx : 0 < optX w tau := optX_pos hw ht
  have hA : 0 < optA w tau := optA_pos hw ht
  have hprod := optX_mul_optA hw ht
  have hadd := optA_eq_add_optX w tau
  field_simp [hx.ne', hA.ne', ht.ne']
  nlinarith

/-- The two first-order equations at a root of the scalar equation. -/
lemma scalar_FOC {lam w z tau : ℝ}
    (hw : 0 < w) (hz : 0 < z) (ht : 0 < tau)
    (hroot : rootEq lam w z tau = 0) :
    1 / (2 * optX w tau) + 1 / (optA w tau + optA z tau) -
        1 / (2 * optA w tau) - lam = 0 ∧
    1 / (2 * optX z tau) + 1 / (optA w tau + optA z tau) -
        1 / (2 * optA z tau) - lam = 0 := by
  have hwid := inv_optX_sub_inv_optA hw ht
  have hzid := inv_optX_sub_inv_optA hz ht
  unfold rootEq at hroot
  constructor <;> linarith

end

end YeGDLowerBound
