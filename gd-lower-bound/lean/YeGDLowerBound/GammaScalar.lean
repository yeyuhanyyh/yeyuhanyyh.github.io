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

/-- `w + optX w tau`, in the cancellation-free form used in the certificate. -/
def optA (w tau : ℝ) : ℝ :=
  (w + Real.sqrt (w ^ 2 + 4 * w * tau)) / 2

lemma optA_eq_add_optX (w tau : ℝ) : optA w tau = w + optX w tau := by
  simp only [optA, optX]
  ring

lemma radicand_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < w ^ 2 + 4 * w * tau := by positivity

lemma optX_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < optX w tau := by
  have hrad : 0 ≤ w ^ 2 + 4 * w * tau := (radicand_pos hw ht).le
  have hsq : w ^ 2 < w ^ 2 + 4 * w * tau := by positivity
  have hsqrt : w < Real.sqrt (w ^ 2 + 4 * w * tau) := by
    rw [Real.lt_sqrt (sq_nonneg w) hrad]
    simpa using hsq
  unfold optX
  linarith

lemma optA_pos {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    0 < optA w tau := by
  rw [optA_eq_add_optX]
  exact add_pos hw (optX_pos hw ht)

lemma optX_mul_optA {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    optX w tau * optA w tau = w * tau := by
  have hrad : 0 ≤ w ^ 2 + 4 * w * tau := (radicand_pos hw ht).le
  unfold optX optA
  rw [show Real.sqrt (w ^ 2 + 4 * w * tau) ^ 2 =
      w ^ 2 + 4 * w * tau by exact Real.sq_sqrt hrad]
  ring

lemma optX_eq_two_mul_div {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    optX w tau = 2 * tau /
      (Real.sqrt (1 + 4 * tau / w) + 1) := by
  have hrad : 0 ≤ w ^ 2 + 4 * w * tau := (radicand_pos hw ht).le
  have hw0 : w ≠ 0 := hw.ne'
  have hden : Real.sqrt (1 + 4 * tau / w) + 1 ≠ 0 := by positivity
  have hscale : Real.sqrt (w ^ 2 + 4 * w * tau) =
      w * Real.sqrt (1 + 4 * tau / w) := by
    have hinner : 0 ≤ 1 + 4 * tau / w := by positivity
    apply (mul_left_cancel₀ hw0)
    have hleft_nonneg : 0 ≤ Real.sqrt (w ^ 2 + 4 * w * tau) := Real.sqrt_nonneg _
    have hright_nonneg : 0 ≤ w * Real.sqrt (1 + 4 * tau / w) :=
      mul_nonneg hw.le (Real.sqrt_nonneg _)
    apply (sq_eq_sq₀ hleft_nonneg hright_nonneg).mp
    rw [sq_sqrt hrad, mul_pow, sq_sqrt hinner]
    field_simp [hw0]
    ring
  rw [optX, hscale]
  field_simp [hw0, hden]
  ring

/-- The scalar first-order equation. -/
def rootEq (lam w z tau : ℝ) : ℝ :=
  1 / (2 * tau) + 1 / (optA w tau + optA z tau) - lam

lemma rootEq_continuousOn {lam w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    ContinuousOn (rootEq lam w z) (Set.Ioi 0) := by
  intro tau htau
  have ht : 0 < tau := htau
  have hA : 0 < optA w tau + optA z tau :=
    add_pos (optA_pos hw ht) (optA_pos hz ht)
  unfold rootEq optA
  fun_prop

lemma optA_strictMono {w : ℝ} (hw : 0 < w) :
    StrictMonoOn (optA w) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold optA
  have hrad : w ^ 2 + 4 * w * a < w ^ 2 + 4 * w * b := by
    nlinarith
  have hsqrt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ w ^ 2 + 4 * w * a) hrad
  linarith

lemma rootEq_strictAnti {lam w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    StrictAntiOn (rootEq lam w z) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hfirst : 1 / (2 * b) < 1 / (2 * a) := by
    rw [one_div_lt_one_div₀ (mul_pos (by norm_num) ha0) (mul_pos (by norm_num) hb0)]
    nlinarith
  have hAw : optA w a < optA w b := optA_strictMono hw ha hb hab
  have hAz : optA z a < optA z b := optA_strictMono hz ha hb hab
  have hsum : optA w a + optA z a < optA w b + optA z b := add_lt_add hAw hAz
  have hA0 : 0 < optA w a + optA z a := add_pos (optA_pos hw ha0) (optA_pos hz ha0)
  have hB0 : 0 < optA w b + optA z b := add_pos (optA_pos hw hb0) (optA_pos hz hb0)
  have hsecond : 1 / (optA w b + optA z b) < 1 / (optA w a + optA z a) := by
    rw [one_div_lt_one_div₀ hA0 hB0]
    exact hsum
  unfold rootEq
  linarith

/-- The two first-order equations at the scalar optimizer. -/
lemma scalar_FOC {lam w z tau : ℝ}
    (hw : 0 < w) (hz : 0 < z) (ht : 0 < tau)
    (hroot : rootEq lam w z tau = 0) :
    1 / (2 * optX w tau) + 1 / (optA w tau + optA z tau) -
        1 / (2 * optA w tau) - lam = 0 ∧
    1 / (2 * optX z tau) + 1 / (optA w tau + optA z tau) -
        1 / (2 * optA z tau) - lam = 0 := by
  have hx := optX_mul_optA hw ht
  have hy := optX_mul_optA hz ht
  have hxp := optX_pos hw ht
  have hyp := optX_pos hz ht
  have hAp := optA_pos hw ht
  have hBp := optA_pos hz ht
  constructor
  · unfold rootEq at hroot
    field_simp [hxp.ne', hAp.ne', ht.ne', hw.ne'] at hroot ⊢
    nlinarith
  · unfold rootEq at hroot
    field_simp [hyp.ne', hBp.ne', ht.ne', hz.ne'] at hroot ⊢
    nlinarith

end

end YeGDLowerBound
