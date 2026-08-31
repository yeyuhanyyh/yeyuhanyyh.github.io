import Mathlib

namespace GDLowerBound

noncomputable section

/-- The positive square-root factor used in the exact chain factorization. -/
def chainP (x u : ℝ) : ℝ := Real.sqrt (x * (1 + x * u))

/-- The companion factor, defined so that `chainP x u * chainQ x u = x*u`. -/
def chainQ (x u : ℝ) : ℝ := x * u / chainP x u

/-- The bilinear kernel before replacing reciprocal weights by `w,z`. -/
def kernelUV (x u y v : ℝ) : ℝ :=
  chainQ x u * chainP y v + chainP x u * chainQ y v

/-- The local reciprocal chain factor from the Ma--Chen/Tsai construction. -/
def chiInv (x u y v : ℝ) : ℝ :=
  x * u + x * v * (1 + x * u) / (1 + y * v)

lemma one_add_mul_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    0 < 1 + x * u := by positivity

lemma chainP_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    0 < chainP x u := by
  unfold chainP
  positivity

lemma chainP_ne_zero {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    chainP x u ≠ 0 := ne_of_gt (chainP_pos hx hu)

lemma chainP_sq {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    (chainP x u) ^ 2 = x * (1 + x * u) := by
  unfold chainP
  rw [sq_sqrt]
  positivity

lemma chainP_mul_chainQ {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    chainP x u * chainQ x u = x * u := by
  unfold chainQ
  field_simp [chainP_ne_zero hx hu]

lemma chainQ_mul_chainP {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    chainQ x u * chainP x u = x * u := by
  rw [mul_comm]
  exact chainP_mul_chainQ hx hu

lemma chainQ_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    0 < chainQ x u := by
  unfold chainQ
  positivity

lemma kernelUV_pos {x u y v : ℝ}
    (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) (hv : 0 < v) :
    0 < kernelUV x u y v := by
  unfold kernelUV
  positivity

lemma kernelUV_symm (x u y v : ℝ) :
    kernelUV x u y v = kernelUV y v x u := by
  unfold kernelUV
  ring

/-- Exact local factorization.  Multiplication over consecutive indices makes
    the ratio of the `chainP` factors telescope. -/
theorem chiInv_factorization {x u y v : ℝ}
    (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) (hv : 0 < v) :
    chiInv x u y v =
      (chainP x u / chainP y v) * kernelUV x u y v := by
  have hPx := chainP_ne_zero hx hu
  have hPy := chainP_ne_zero hy hv
  have hden : 1 + y * v ≠ 0 := ne_of_gt (one_add_mul_pos hy hv)
  have hPx2 := chainP_sq hx hu
  have hPy2 := chainP_sq hy hv
  unfold chiInv kernelUV chainQ
  field_simp [hPx, hPy, hden]
  nlinarith

/-- The kernel in the reciprocal-weight variables used in the blog. -/
def kernelW (w z x y : ℝ) : ℝ := kernelUV x (1 / w) y (1 / z)

lemma kernelW_symm (w z x y : ℝ) :
    kernelW w z x y = kernelW z w y x := by
  unfold kernelW
  exact kernelUV_symm _ _ _ _

lemma kernelW_pos {w z x y : ℝ}
    (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) (hy : 0 < y) :
    0 < kernelW w z x y := by
  unfold kernelW
  apply kernelUV_pos hx <;> positivity

end

end GDLowerBound
