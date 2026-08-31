import Mathlib

/-!
# Minimizing rank and the power-law tail profile
-/

namespace GDLowerBound

noncomputable section

open scoped BigOperators
open Real

/-- The elementary division step behind the minimizing-rank argument. -/
lemma ratio_of_weighted_min
    {α Dq Dm q m : ℝ}
    (hα : 0 ≤ α) (hDq : 0 < Dq) (hDm : 0 ≤ Dm)
    (hq : 0 < q) (hm : 0 < m)
    (hmin : Dq * q ^ α ≤ Dm * m ^ α) :
    (q / m) ^ α ≤ Dm / Dq := by
  have hqa : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  have hma : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hdiv : q ^ α / m ^ α ≤ Dm / Dq := by
    rw [div_le_div_iff₀ hma hDq]
    nlinarith
  rw [Real.div_rpow hq.le hm.le]
  exact hdiv

/-- The form used in the blog: a minimizing rank gives the cumulative tail lower bound. -/
lemma tail_from_min_rank
    {α Dq Dm q m tail : ℝ}
    (hα : 0 ≤ α) (hDq : 0 < Dq) (hDm : 0 ≤ Dm)
    (hq : 0 < q) (hm : 0 < m)
    (hmin : Dq * q ^ α ≤ Dm * m ^ α)
    (htail : tail = q / Dq * (Dm - Dq)) :
    q * ((q / m) ^ α - 1) ≤ tail := by
  have hratio := ratio_of_weighted_min hα hDq hDm hq hm hmin
  rw [htail]
  have hqD : 0 ≤ q / Dq := (div_pos hq hDq).le
  have hbase : Dq * ((q / m) ^ α - 1) ≤ Dm - Dq := by
    nlinarith
  calc
    q * ((q / m) ^ α - 1)
        = (q / Dq) * (Dq * ((q / m) ^ α - 1)) := by field_simp; ring
    _ ≤ (q / Dq) * (Dm - Dq) := mul_le_mul_of_nonneg_left hbase hqD

/-- A useful lower bound for logarithms, proved from `log x ≤ x-1` by inversion. -/
lemma div_one_add_le_log_one_add {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hpos : 0 < 1 + t := by linarith
  have hinv : 0 < (1 + t)⁻¹ := inv_pos.mpr hpos
  have hlog := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at hlog
  have hid : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
    field_simp
    ring
  rw [hid] at hlog
  linarith

/-- `q log(q/(q-1)) ≥ 1`, the endpoint estimate used in Lemma 4. -/
lemma one_le_nat_mul_log_ratio {q : ℕ} (hq : 2 ≤ q) :
    (1 : ℝ) ≤ q * Real.log ((q : ℝ) / (q - 1 : ℕ)) := by
  have hqm1 : 0 < (q - 1 : ℕ) := Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.zero_lt_two hq)
  have hcast : (q : ℝ) / (q - 1 : ℕ) = 1 + 1 / (q - 1 : ℕ) := by
    have hne : ((q - 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_eq_iff hne]
    push_cast
    ring
  rw [hcast]
  have ht : 0 ≤ (1 : ℝ) / (q - 1 : ℕ) := by positivity
  have hlog := div_one_add_le_log_one_add ht
  have hden :
      ((1 : ℝ) / (q - 1 : ℕ)) / (1 + 1 / (q - 1 : ℕ)) = 1 / q := by
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hqm10 : ((q - 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  rw [hden] at hlog
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  nlinarith

/-- The bottom reference weight is at least `α`. -/
lemma alpha_le_bottom_reference
    {α : ℝ} (hα : 0 ≤ α) {q : ℕ} (hq : 2 ≤ q) :
    α ≤ (q : ℝ) * (((q : ℝ) / (q - 1 : ℕ)) ^ α - 1) := by
  have hratio : 0 < (q : ℝ) / (q - 1 : ℕ) := by positivity
  rw [Real.rpow_def_of_pos hratio]
  have hexp : α * Real.log ((q : ℝ) / (q - 1 : ℕ)) + 1
      ≤ Real.exp (α * Real.log ((q : ℝ) / (q - 1 : ℕ))) :=
    Real.add_one_le_exp _
  have hlog := one_le_nat_mul_log_ratio hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hlognonneg : 0 ≤ Real.log ((q : ℝ) / (q - 1 : ℕ)) := by
    have hratio1 : (1 : ℝ) ≤ (q : ℝ) / (q - 1 : ℕ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q - 1 : ℕ))]
      push_cast
      omega
    exact Real.log_nonneg hratio1
  nlinarith

/-- Exact telescoping of the discrete power-law reference tail. -/
lemma reference_tail_telescope
    {α : ℝ} {q m : ℕ} (hm : m ≤ q) :
    (∑ s ∈ Finset.Ioc m q,
        (q : ℝ) ^ (1 + α) *
          (((s - 1 : ℕ) : ℝ)⁻¹ ^ α - ((s : ℝ)⁻¹) ^ α))
      = (q : ℝ) ^ (1 + α) *
          (((m : ℝ)⁻¹) ^ α - ((q : ℝ)⁻¹) ^ α) := by
  let b : ℕ → ℝ := fun s => ((s : ℝ)⁻¹) ^ α
  have htel :
      (∑ s ∈ Finset.Ioc m q, (b (s - 1) - b s)) = b m - b q := by
    exact Finset.sum_Ioc_sub_eq_sub hm
  rw [← Finset.mul_sum]
  simpa [b, mul_sub] using congrArg (fun z : ℝ => (q : ℝ) ^ (1 + α) * z) htel

end

end GDLowerBound
