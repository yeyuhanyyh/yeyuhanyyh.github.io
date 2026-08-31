import Mathlib

namespace GDLowerBound

noncomputable section

/-- A convenient positive realization of the real power `(n : ℝ)^α` for a positive rank. -/
def rankPower (α : ℝ) (n : ℕ) : ℝ := Real.exp (α * Real.log (n : ℝ))

/-- The scale ratio `(q/m)^α`, written so that no convention at rank zero is used. -/
def rankRatio (α : ℝ) (q m : ℕ) : ℝ :=
  Real.exp (α * Real.log ((q : ℝ) / (m : ℝ)))

lemma rankPower_pos (α : ℝ) (n : ℕ) : 0 < rankPower α n := by
  unfold rankPower
  exact Real.exp_pos _

lemma rankRatio_pos (α : ℝ) (q m : ℕ) : 0 < rankRatio α q m := by
  unfold rankRatio
  exact Real.exp_pos _

lemma rankPower_eq_mul_rankRatio (α : ℝ) {q m : ℕ}
    (hq : q ≠ 0) (hm : m ≠ 0) :
    rankPower α q = rankPower α m * rankRatio α q m := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold rankPower rankRatio
  rw [Real.log_div hqr hmr]
  rw [show α * Real.log (q : ℝ) =
      α * Real.log (m : ℝ) + α * (Real.log (q : ℝ) - Real.log (m : ℝ)) by ring]
  rw [Real.exp_add]

/-- The minimizing-rank inequality, in the multiplicative form used to obtain all tail bounds. -/
theorem rankRatio_le_residualRatio
    {α Dq Dm : ℝ} {q m : ℕ}
    (hq : q ≠ 0) (hm : m ≠ 0)
    (hmin : Dq * rankPower α q ≤ Dm * rankPower α m) :
    Dq * rankRatio α q m ≤ Dm := by
  rw [rankPower_eq_mul_rankRatio α hq hm] at hmin
  have hp := rankPower_pos α m
  have hrewrite :
      Dq * (rankPower α m * rankRatio α q m) =
        rankPower α m * (Dq * rankRatio α q m) := by ring
  have hrewrite' : Dm * rankPower α m = rankPower α m * Dm := by ring
  rw [hrewrite, hrewrite'] at hmin
  exact (mul_le_mul_left hp).mp hmin

/-- If `D_m-D_q` is the mass of the ranks `m+1,...,q`, minimizing
    `D_s s^α` gives exactly the cumulative power-law tail lower bound. -/
theorem tail_mass_of_minimizing_rank
    {α Dq Dm tail : ℝ} {q m : ℕ}
    (hq : q ≠ 0) (hm : m ≠ 0)
    (hmin : Dq * rankPower α q ≤ Dm * rankPower α m)
    (hD : Dm = Dq + tail) :
    Dq * (rankRatio α q m - 1) ≤ tail := by
  have h := rankRatio_le_residualRatio hq hm hmin
  rw [hD] at h
  linarith

/-- The normalized version used verbatim in the sequence problem. -/
theorem normalized_tail_of_minimizing_rank
    {α Dq Dm tail sumW : ℝ} {q m : ℕ}
    (hq : q ≠ 0) (hm : m ≠ 0)
    (hDq : 0 < Dq)
    (hmin : Dq * rankPower α q ≤ Dm * rankPower α m)
    (hD : Dm = Dq + tail)
    (hnorm : tail = Dq / (q : ℝ) * sumW) :
    (q : ℝ) * (rankRatio α q m - 1) ≤ sumW := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have htail := tail_mass_of_minimizing_rank hq hm hmin hD
  rw [hnorm] at htail
  have hscale : 0 < Dq / (q : ℝ) := div_pos hDq hqR
  have heq :
      Dq * (rankRatio α q m - 1) =
        (Dq / (q : ℝ)) * ((q : ℝ) * (rankRatio α q m - 1)) := by
    field_simp
    ring
  rw [heq] at htail
  exact (mul_le_mul_left hscale).mp htail

end

end GDLowerBound
