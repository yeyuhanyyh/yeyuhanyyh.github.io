import YeGDLowerBound.GammaMaximum

/-!
# Explicit evaluation of `Gamma_lambda`
-/

namespace YeGDLowerBound

noncomputable section

open Real

lemma kernel_pos {w z x y : ℝ}
    (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) (hy : 0 < y) :
    0 < kernel w z x y := by
  unfold kernel
  exact div_pos
    (mul_pos (Real.sqrt_pos.2 (mul_pos hx hy)) (by positivity))
    (Real.sqrt_pos.2 (by positivity))

lemma kernel_sq {w z x y : ℝ}
    (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) (hy : 0 < y) :
    kernel w z x y ^ 2 =
      x * y * (w + z + x + y) ^ 2 /
        (w * z * (w + x) * (z + y)) := by
  have hxy : 0 ≤ x * y := (mul_pos hx hy).le
  have hden : 0 ≤ w * z * (w + x) * (z + y) := by positivity
  unfold kernel
  rw [div_pow, mul_pow, Real.sq_sqrt hxy, Real.sq_sqrt hden]
  ring

/-- Kernel value at the scalar optimizer, in the stable form used by Arb. -/
theorem kernel_at_scalar_optimizer {w z tau : ℝ}
    (hw : 0 < w) (hz : 0 < z) (ht : 0 < tau) :
    kernel w z (optX w tau) (optX z tau) =
      tau * (1 / optA w tau + 1 / optA z tau) := by
  let X := optX w tau
  let Y := optX z tau
  let A := optA w tau
  let B := optA z tau
  have hX : 0 < X := optX_pos hw ht
  have hY : 0 < Y := optX_pos hz ht
  have hA : 0 < A := optA_pos hw ht
  have hB : 0 < B := optA_pos hz ht
  have hXA : X * A = w * tau := optX_mul_optA hw ht
  have hYB : Y * B = z * tau := optX_mul_optA hz ht
  have hsum : w + z + X + Y = A + B := by
    dsimp [X, Y, A, B]
    rw [optA_eq_add_optX, optA_eq_add_optX]
    ring
  have hleft : 0 ≤ kernel w z X Y := (kernel_pos hw hz hX hY).le
  have hright : 0 ≤ tau * (1 / A + 1 / B) := by positivity
  apply (sq_eq_sq₀ hleft hright).mp
  rw [kernel_sq hw hz hX hY, hsum]
  have hw0 := hw.ne'
  have hz0 := hz.ne'
  have hA0 := hA.ne'
  have hB0 := hB.ne'
  have hX0 := hX.ne'
  have hY0 := hY.ne'
  field_simp [hw0, hz0, hA0, hB0, hX0, hY0]
  nlinarith

/-- Cancellation-free scalar expression for the envelope. -/
theorem Gamma_eq_explicit {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    let tau := tauStar lam w z
    Gamma lam w z =
      Real.log (tau * (1 / optA w tau + 1 / optA z tau)) -
        lam * (optX w tau + optX z tau) := by
  dsimp
  let tau := tauStar lam w z
  have ht : 0 < tau := tauStar_pos hlam hw hz
  have hX := optX_pos hw ht
  have hY := optX_pos hz ht
  rw [Gamma_eq_optimizer hlam hw hz,
    gammaObjective_eq_log_kernel hw hz hX hY,
    kernel_at_scalar_optimizer hw hz ht]

end

end YeGDLowerBound
