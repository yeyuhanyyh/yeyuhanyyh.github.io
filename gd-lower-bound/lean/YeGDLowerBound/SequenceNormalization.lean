import GDLowerBound.Matching.Endpoint
import YeGDLowerBound.MinRank

/-!
# Schedule-to-sequence normalization
-/

namespace YeGDLowerBound

noncomputable section

open scoped BigOperators Real
open GDLowerBound
open GDLowerBound.Schedule
open GDLowerBound.Matching

/-- The normalized preceding-gap variables `x_i=q U_i/D_q`. -/
def topX {T q : ℕ} (h : StepSchedule T) (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  (q : ℝ) / unresolvedMass h q * chronologicalPrecedingMass h q hq i

/-- The selected excesses in chronological order, normalized by `D_q/q`. -/
def topOmega {T q : ℕ} (h : StepSchedule T) (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  (q : ℝ) / unresolvedMass h q * chronologicalExcess h q hq i

/-- The ranked version of the same normalized selected excesses. -/
def rankedOmega {T q : ℕ} (h : StepSchedule T) (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  (q : ℝ) / unresolvedMass h q *
    rankedExcessAt h ⟨i, i.isLt.trans_le hq⟩

lemma topX_pos {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) (i : Fin q) :
    0 < topX h hq i := by
  exact mul_pos (div_pos (by exact_mod_cast hq0) (unresolvedMass_pos hh q))
    (chronologicalPrecedingMass_pos hh q hq i)

lemma topOmega_pos {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) (i : Fin q) :
    0 < topOmega h hq i := by
  exact mul_pos (div_pos (by exact_mod_cast hq0) (unresolvedMass_pos hh q))
    (chronologicalExcess_pos h q hq i)

lemma rankedOmega_pos {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) (i : Fin q) :
    0 < rankedOmega h hq i := by
  exact mul_pos (div_pos (by exact_mod_cast hq0) (unresolvedMass_pos hh q))
    (rankedExcessAt_pos h ⟨i, i.isLt.trans_le hq⟩)

lemma rankedOmega_antitone {T q : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hq : q ≤ longCount h) :
    Antitone (rankedOmega h hq) := by
  intro i j hij
  unfold rankedOmega
  apply mul_le_mul_of_nonneg_left
  · exact rankedExcessAt_antitone h (Fin.mk_le_mk.mpr hij)
  · exact div_nonneg (Nat.cast_nonneg q) (unresolvedMass_nonneg hh q)

/-- The normalized preceding masses have total strictly below `q`. -/
theorem sum_topX_lt {T q : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hq0 : 0 < q) (hq : q ≤ longCount h) :
    (∑ i : Fin q, topX h hq i) < q := by
  have hD := unresolvedMass_pos hh q
  have hsumEq := chronologicalPrecedingMass_sum_eq h hq
  have hmass := topChain_mass_decomposition h hq
  rw [← hsumEq] at hmass
  have hV : 0 < (topChain h q).gapMass q := (topChain h q).gapMass_pos hh q
  have hsumlt :
      (∑ i : Fin q, chronologicalPrecedingMass h q hq i) < unresolvedMass h q := by
    linarith
  have hscale : 0 < (q : ℝ) / unresolvedMass h q :=
    div_pos (by exact_mod_cast hq0) hD
  calc
    (∑ i : Fin q, topX h hq i) =
        ((q : ℝ) / unresolvedMass h q) *
          ∑ i : Fin q, chronologicalPrecedingMass h q hq i := by
      simp only [topX, Finset.mul_sum]
    _ < ((q : ℝ) / unresolvedMass h q) * unresolvedMass h q :=
      mul_lt_mul_of_pos_left hsumlt hscale
    _ = q := by field_simp [hD.ne']

/-- Natural-number extension of the ranked positive excess sequence. -/
def rankedExcessNat {T : ℕ} (h : StepSchedule T) (j : ℕ) : ℝ :=
  if hj : j < longCount h then rankedExcessAt h ⟨j, hj⟩ else 0

lemma unresolvedMass_recurrence_nat {T : ℕ} (h : StepSchedule T) {j : ℕ}
    (hj : j < longCount h) :
    unresolvedMass h j = rankedExcessNat h j + unresolvedMass h (j + 1) := by
  rw [unresolvedMass_recurrence h hj]
  simp [rankedExcessNat, hj]

/-- The sum of ranks `[m,q)` is exactly the loss in unresolved mass. -/
theorem sum_rankedExcessNat_Ico {T m q : ℕ} (h : StepSchedule T)
    (hmq : m ≤ q) (hqr : q ≤ longCount h) :
    (∑ j ∈ Finset.Ico m q, rankedExcessNat h j) =
      unresolvedMass h m - unresolvedMass h q := by
  induction q, hmq using Nat.le_induction with
  | base => simp
  | succ q hmq ih =>
      have hqR : q < longCount h := lt_of_lt_of_le (Nat.lt_succ_self q) hqr
      rw [Finset.sum_Ico_succ_top hmq, ih hqr.le]
      rw [unresolvedMass_recurrence_nat h hqR]
      ring

/-- The ranked normalized tail has the exact residual-mass value. -/
theorem sum_rankedOmega_Ico {T m q : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hq0 : 0 < q)
    (hmq : m ≤ q) (hqr : q ≤ longCount h) :
    (∑ j ∈ Finset.Ico m q,
        (q : ℝ) / unresolvedMass h q * rankedExcessNat h j) =
      (q : ℝ) / unresolvedMass h q *
        (unresolvedMass h m - unresolvedMass h q) := by
  rw [← Finset.mul_sum, sum_rankedExcessNat_Ico h hmq hqr]

/-- At a minimizing rank, every ranked tail dominates the reference power-law tail. -/
theorem ranked_tail_condition_of_minimizing
    {T m q : ℕ} {alpha : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hm : 1 ≤ m) (hmq : m ≤ q)
    (hmin : rankScore alpha h q ≤ rankScore alpha h m) :
    (q : ℝ) * (Real.rpow ((q : ℝ) / m) alpha - 1) ≤
      (q : ℝ) / unresolvedMass h q *
        (unresolvedMass h m - unresolvedMass h q) := by
  have htail := residual_drop_of_minimizing_rank hh (Nat.one_le_iff_ne_zero.mpr hq0.ne') hm hmin
  have hD := unresolvedMass_pos hh q
  calc
    (q : ℝ) * (Real.rpow ((q : ℝ) / m) alpha - 1)
        = ((q : ℝ) / unresolvedMass h q) *
            (unresolvedMass h q *
              (Real.rpow ((q : ℝ) / m) alpha - 1)) := by
          field_simp [hD.ne']
    _ ≤ ((q : ℝ) / unresolvedMass h q) *
        (unresolvedMass h m - unresolvedMass h q) :=
      mul_le_mul_of_nonneg_left htail
        (div_nonneg (Nat.cast_nonneg q) hD.le)

end

end YeGDLowerBound
