import Mathlib

/-!
# Exact local factorization of the selected chain
-/

namespace GDLowerBound

noncomputable section

open Real

/-- The factor `P_i` used in the telescoping factorization. -/
def blockP (x u : ℝ) : ℝ := Real.sqrt (x * (1 + x * u))

/-- The factor `Q_i`, defined in a numerically stable algebraic form. -/
def blockQ (x u : ℝ) : ℝ := x * u / blockP x u

/-- The exact symmetric edge factor in reciprocal-weight coordinates. -/
def kernelU (x u y v : ℝ) : ℝ :=
  blockQ x u * blockP y v + blockP x u * blockQ y v

/-- The kernel in the blog's weight coordinates `w=1/u`, `z=1/v`. -/
def kernelW (w z x y : ℝ) : ℝ := kernelU x w⁻¹ y z⁻¹

/-- The reciprocal of the local chain multiplier. -/
def chiInv (x u y v : ℝ) : ℝ :=
  x * u + x * v * (1 + x * u) / (1 + y * v)

lemma blockP_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) : 0 < blockP x u := by
  apply Real.sqrt_pos.2
  positivity

lemma blockP_sq {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    blockP x u ^ 2 = x * (1 + x * u) := by
  rw [blockP, sq_sqrt]
  positivity

lemma blockP_mul_blockQ {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    blockP x u * blockQ x u = x * u := by
  rw [blockQ]
  field_simp [ne_of_gt (blockP_pos hx hu)]

lemma blockQ_mul_blockP {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    blockQ x u * blockP x u = x * u := by
  rw [mul_comm]
  exact blockP_mul_blockQ hx hu

lemma blockQ_div_blockP {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    blockQ x u / blockP x u = u / (1 + x * u) := by
  have hp := blockP_pos hx hu
  rw [blockQ, div_div]
  rw [← sq]
  rw [blockP_sq hx.le hu.le]
  field_simp
  ring

/-- Exact local factorization from the manuscript. -/
lemma exact_local_factorization
    {x u y v : ℝ} (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) (hv : 0 < v) :
    chiInv x u y v = blockP x u / blockP y v * kernelU x u y v := by
  have hpy : 0 < blockP y v := blockP_pos hy hv
  rw [kernelU]
  calc
    blockP x u / blockP y v *
        (blockQ x u * blockP y v + blockP x u * blockQ y v)
        = blockP x u * blockQ x u +
            blockP x u ^ 2 * (blockQ y v / blockP y v) := by
              field_simp [ne_of_gt hpy]
              ring
    _ = x * u + x * (1 + x * u) * (v / (1 + y * v)) := by
          rw [blockP_mul_blockQ hx hu, blockP_sq hx.le hu.le,
            blockQ_div_blockP hy hv]
    _ = chiInv x u y v := by
          rw [chiInv]
          ring

/-- A list form of the telescoping product of consecutive ratios. -/
lemma list_ratio_telescope
    {a : ℝ} {l : List ℝ} {z : ℝ}
    (ha : a ≠ 0) (hz : z ≠ 0) (hl : ∀ x ∈ l, x ≠ 0) :
    (List.zipWith (· / ·) (a :: l) (l ++ [z])).prod = a / z := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      have hb : b ≠ 0 := hl b (by simp)
      have hlt : ∀ x ∈ l, x ≠ 0 := by
        intro x hx
        exact hl x (by simp [hx])
      simp only [List.zipWith_cons_cons, List.prod_cons]
      rw [ih hb hz hlt]
      field_simp

end

end GDLowerBound
