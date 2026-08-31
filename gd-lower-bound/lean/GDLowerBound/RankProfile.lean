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
    (hDq : 0 < Dq) (hq : 0 < q) (hm : 0 < m)
    (hmin : Dq * q ^ α ≤ Dm * m ^ α) :
    (q / m) ^ α ≤ Dm / Dq := by
  have hma : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hdiv : q ^ α / m ^ α ≤ Dm / Dq := by
    rw [div_le_div_iff₀ hma hDq]
    simpa [mul_comm] using hmin
  rw [Real.div_rpow hq.le hm.le]
  exact hdiv

/-- The form used in the blog: a minimizing rank gives the cumulative tail lower bound. -/
lemma tail_from_min_rank
    {α Dq Dm q m tail : ℝ}
    (hDq : 0 < Dq) (hq : 0 < q) (hm : 0 < m)
    (hmin : Dq * q ^ α ≤ Dm * m ^ α)
    (htail : tail = q / Dq * (Dm - Dq)) :
    q * ((q / m) ^ α - 1) ≤ tail := by
  have hratio := ratio_of_weighted_min hDq hq hm hmin
  have hmul := mul_le_mul_of_nonneg_left hratio hDq.le
  have hcancel : Dq * (Dm / Dq) = Dm := by
    field_simp [ne_of_gt hDq]
  rw [hcancel] at hmul
  have hbase : Dq * ((q / m) ^ α - 1) ≤ Dm - Dq := by
    linarith
  rw [htail]
  calc
    q * ((q / m) ^ α - 1)
        = (q / Dq) * (Dq * ((q / m) ^ α - 1)) := by
            field_simp [ne_of_gt hDq]
    _ ≤ (q / Dq) * (Dm - Dq) :=
      mul_le_mul_of_nonneg_left hbase (div_nonneg hq.le hDq.le)

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
  have hqm1 : 0 < q - 1 := by omega
  have hqm1R : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast hqm1
  have hqR : (0 : ℝ) < q := by positivity
  have hcast : (q : ℝ) / (q - 1 : ℕ) = 1 + 1 / (q - 1 : ℕ) := by
    rw [div_eq_iff (ne_of_gt hqm1R)]
    field_simp [ne_of_gt hqm1R]
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
  rw [hcast]
  have ht : 0 ≤ (1 : ℝ) / (q - 1 : ℕ) := by positivity
  have hlog := div_one_add_le_log_one_add ht
  have hden :
      ((1 : ℝ) / (q - 1 : ℕ)) / (1 + 1 / (q - 1 : ℕ)) = 1 / q := by
    field_simp [ne_of_gt hqm1R, ne_of_gt hqR]
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
  rw [hden] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hqR.le
  have hqinv : (q : ℝ) * (1 / q) = 1 := by
    field_simp [ne_of_gt hqR]
  simpa [hqinv] using hmul

/-- The bottom reference weight is at least `α`. -/
lemma alpha_le_bottom_reference
    {α : ℝ} (hα : 0 ≤ α) {q : ℕ} (hq : 2 ≤ q) :
    α ≤ (q : ℝ) * (((q : ℝ) / (q - 1 : ℕ)) ^ α - 1) := by
  have hqm1 : 0 < q - 1 := by omega
  have hqm1R : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast hqm1
  have hqR : (0 : ℝ) < q := by positivity
  have hratio : 0 < (q : ℝ) / (q - 1 : ℕ) := div_pos hqR hqm1R
  rw [Real.rpow_def_of_pos hratio]
  let L := Real.log ((q : ℝ) / (q - 1 : ℕ))
  have hexp : α * L + 1 ≤ Real.exp (α * L) := Real.add_one_le_exp _
  have hlog : (1 : ℝ) ≤ q * L := one_le_nat_mul_log_ratio hq
  have hfirst0 := mul_le_mul_of_nonneg_left hlog hα
  have hfirst : α ≤ (q : ℝ) * (α * L) := by
    convert hfirst0 using 1 <;> ring
  have hsecond0 : α * L ≤ Real.exp (α * L) - 1 := by linarith
  have hsecond := mul_le_mul_of_nonneg_left hsecond0 hqR.le
  calc
    α ≤ (q : ℝ) * (α * L) := hfirst
    _ ≤ (q : ℝ) * (Real.exp (α * L) - 1) := hsecond
    _ = (q : ℝ) * (Real.exp (L * α) - 1) := by rw [mul_comm L α]

/-- A generic finite telescoping identity. -/
lemma sum_range_sub_telescope (b : ℕ → ℝ) (m k : ℕ) :
    (∑ j ∈ Finset.range k, (b (m + j) - b (m + j + 1))) = b m - b (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Exact telescoping of the discrete power-law reference tail. -/
lemma reference_tail_telescope
    {α : ℝ} {q m : ℕ} (hm : m ≤ q) :
    (∑ j ∈ Finset.range (q - m),
        (q : ℝ) ^ (1 + α) *
          ((((m + j : ℕ) : ℝ)⁻¹) ^ α - (((m + j + 1 : ℕ) : ℝ)⁻¹) ^ α))
      = (q : ℝ) ^ (1 + α) *
          (((m : ℝ)⁻¹) ^ α - ((q : ℝ)⁻¹) ^ α) := by
  let b : ℕ → ℝ := fun s => ((s : ℝ)⁻¹) ^ α
  have htel := sum_range_sub_telescope b m (q - m)
  have hadd : m + (q - m) = q := Nat.add_sub_of_le hm
  rw [← Finset.mul_sum]
  simpa [b, hadd, mul_sub] using
    congrArg (fun z : ℝ => (q : ℝ) ^ (1 + α) * z) htel

end

end GDLowerBound
