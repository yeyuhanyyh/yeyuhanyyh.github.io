import Mathlib

/-!
# Exact definitions for the improved sequence argument
-/

namespace YeGDLowerBound

noncomputable section

open scoped BigOperators Interval
open Set Real MeasureTheory intervalIntegral

/-- The two-point kernel in equation (2) of the blog. -/
def kernel (w z x y : ℝ) : ℝ :=
  Real.sqrt (x * y) * (w + z + x + y) /
    Real.sqrt (w * z * (w + x) * (z + y))

/-- The terminal factor in equation (5). -/
def endpointFactor {q : ℕ} (x omega : Fin q → ℝ) : ℝ :=
  if hq : 0 < q then
    let first : Fin q := ⟨0, hq⟩
    let last : Fin q := ⟨q - 1, Nat.sub_lt hq Nat.zero_lt_one⟩
    Real.sqrt (x first * x last) *
      Real.sqrt ((1 + x first / omega first) / (1 + x last / omega last)) *
      (1 + (x last + 2 * ((q : ℝ) - ∑ i, x i)) / omega last)
  else 1

/-- The values whose supremum defines `Gamma`. -/
def gammaRange (lam w z : ℝ) : Set ℝ :=
  {r | ∃ x : ℝ, 0 < x ∧ ∃ y : ℝ, 0 < y ∧
    r = Real.log (kernel w z x y) - lam * (x + y)}

/-- The exact envelope from equation (6), totalized using the real supremum. -/
def Gamma (lam w z : ℝ) : ℝ := sSup (gammaRange lam w z)

/-- The reference power-law profile. -/
def W (alpha t : ℝ) : ℝ :=
  alpha * Real.rpow t (-(1 + alpha))

/-- The scalar functional from equation (17). -/
def scalarJ (alpha lam : ℝ) : ℝ :=
  2 * lam + 2 * ∫ t in (0 : ℝ)..(1 / 2 : ℝ),
    Gamma lam (W alpha t) (W alpha (1 - t))

@[simp] theorem kernel_swap (w z x y : ℝ) :
    kernel z w y x = kernel w z x y := by
  unfold kernel
  congr 2 <;> ring

lemma gammaRange_swap (lam w z : ℝ) :
    gammaRange lam z w = gammaRange lam w z := by
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, by simp [kernel_swap, add_comm]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, by simp [kernel_swap, add_comm]⟩

@[simp] theorem Gamma_swap (lam w z : ℝ) : Gamma lam z w = Gamma lam w z := by
  simp only [Gamma, gammaRange_swap]

end

end YeGDLowerBound
