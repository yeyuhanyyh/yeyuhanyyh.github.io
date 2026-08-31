import YeGDLowerBound.GammaRoot
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Concavity and maximization of the Gamma objective
-/

namespace YeGDLowerBound

noncomputable section

open Real Set

/-- The one-coordinate concave term in `log K`. -/
def phi (w x : ℝ) : ℝ := (Real.log x - Real.log (w + x)) / 2

lemma hasDerivAt_phi {w x : ℝ} (hw : 0 < w) (hx : 0 < x) :
    HasDerivAt (phi w) (w / (2 * x * (w + x))) x := by
  have hsum : w + x ≠ 0 := ne_of_gt (add_pos hw hx)
  have hadd : HasDerivAt (fun y : ℝ => w + y) 1 x :=
    (hasDerivAt_id x).const_add w
  have hlogx : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hlogsum :
      HasDerivAt (fun y : ℝ => Real.log (w + y)) (w + x)⁻¹ x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log hsum).comp x hadd
  have hsub : HasDerivAt
      (fun y : ℝ => Real.log y - Real.log (w + y))
      (x⁻¹ - (w + x)⁻¹) x :=
    hlogx.sub hlogsum
  have hraw : HasDerivAt
      (fun y : ℝ => (Real.log y - Real.log (w + y)) / 2)
      ((x⁻¹ - (w + x)⁻¹) / 2) x :=
    hsub.div_const 2
  have hcoef : (x⁻¹ - (w + x)⁻¹) / 2 = w / (2 * x * (w + x)) := by
    field_simp [hx.ne', hsum]
    ring
  rw [hcoef] at hraw
  simpa [phi] using hraw

lemma deriv_phi {w x : ℝ} (hw : 0 < w) (hx : 0 < x) :
    deriv (phi w) x = w / (2 * x * (w + x)) :=
  (hasDerivAt_phi hw hx).deriv

lemma continuousOn_phi {w : ℝ} (hw : 0 < w) :
    ContinuousOn (phi w) (Set.Ioi 0) := by
  intro x hx
  exact (hasDerivAt_phi hw hx).continuousAt.continuousWithinAt

lemma deriv_phi_strictAnti {w : ℝ} (hw : 0 < w) :
    StrictAntiOn (deriv (phi w)) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [deriv_phi hw ha, deriv_phi hw hb]
  have hda : 0 < 2 * a * (w + a) :=
    mul_pos (mul_pos (by norm_num) ha) (add_pos hw ha)
  have hdb : 0 < 2 * b * (w + b) :=
    mul_pos (mul_pos (by norm_num) hb) (add_pos hw hb)
  have hsum : 0 < w + a + b := add_pos (add_pos hw ha) hb
  have hfactor : 0 < (b - a) * (w + a + b) :=
    mul_pos (sub_pos.mpr hab) hsum
  have hden : 2 * a * (w + a) < 2 * b * (w + b) := by
    nlinarith
  rw [div_lt_div_iff₀ hdb hda]
  exact mul_lt_mul_of_pos_left hden hw

/-- The coordinate term is strictly concave on the positive half-line. -/
theorem strictConcaveOn_phi {w : ℝ} (hw : 0 < w) :
    StrictConcaveOn ℝ (Set.Ioi 0) (phi w) := by
  apply (show StrictAntiOn (deriv (phi w)) (interior (Set.Ioi 0)) by
      simpa using deriv_phi_strictAnti hw).strictConcaveOn_of_deriv (convex_Ioi 0)
  exact continuousOn_phi hw

/-- The additive representation of the optimized logarithmic objective. -/
def gammaObjective (lam w z x y : ℝ) : ℝ :=
  phi w x + phi z y + Real.log (w + z + x + y)
    - (Real.log w + Real.log z) / 2 - lam * (x + y)

lemma gammaObjective_eq_log_kernel {lam w z x y : ℝ}
    (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) (hy : 0 < y) :
    gammaObjective lam w z x y = Real.log (kernel w z x y) - lam * (x + y) := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hwz : w * z ≠ 0 := mul_ne_zero hw.ne' hz.ne'
  have hwzx : w * z * (w + x) ≠ 0 :=
    mul_ne_zero hwz (add_pos hw hx).ne'
  have hden : 0 < w * z * (w + x) * (z + y) := by positivity
  have hsum : 0 < w + z + x + y := by positivity
  have hsqrtxy : 0 < Real.sqrt (x * y) := Real.sqrt_pos.2 hxy
  have hsqrtd : 0 < Real.sqrt (w * z * (w + x) * (z + y)) := Real.sqrt_pos.2 hden
  unfold gammaObjective phi kernel
  rw [Real.log_div (mul_ne_zero hsqrtxy.ne' hsum.ne') hsqrtd.ne',
    Real.log_mul hsqrtxy.ne' hsum.ne', Real.log_sqrt hxy.le,
    Real.log_sqrt hden.le, Real.log_mul hx.ne' hy.ne',
    Real.log_mul hwzx (add_pos hz hy).ne',
    Real.log_mul hwz (add_pos hw hx).ne',
    Real.log_mul hw.ne' hz.ne']
  ring

end

end YeGDLowerBound
