import GDLowerBound.Schedule.TopChain
import YeGDLowerBound.RankProfile

/-!
# The minimizing rank
-/

namespace YeGDLowerBound

noncomputable section

open scoped BigOperators Real
open Set
open GDLowerBound
open GDLowerBound.Schedule

/-- The rank score `D_q q^alpha`. -/
def rankScore {T : ℕ} (alpha : ℝ) (h : StepSchedule T) (q : ℕ) : ℝ :=
  unresolvedMass h q * Real.rpow q alpha

/-- A positive minimizing rank exists whenever the schedule has a long step. -/
theorem exists_minimizing_rank {T : ℕ} (alpha : ℝ) (h : StepSchedule T)
    (hr : 0 < longCount h) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ longCount h ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ longCount h → rankScore alpha h q ≤ rankScore alpha h s := by
  let S : Set ℕ := Set.Icc 1 (longCount h)
  have hfinite : S.Finite := Set.finite_Icc 1 (longCount h)
  have hnonempty : S.Nonempty := ⟨1, by
    constructor
    · exact le_rfl
    · omega⟩
  obtain ⟨q, hqS, hqmin⟩ := Set.exists_min_image S (rankScore alpha h) hfinite hnonempty
  refine ⟨q, hqS.1, hqS.2, ?_⟩
  intro s hs1 hsr
  exact hqmin s ⟨hs1, hsr⟩

/-- The minimizing rank gives the exact power-law residual comparison. -/
theorem residual_ratio_of_minimizing_rank
    {T q m : ℕ} {alpha : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h)
    (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hmin : rankScore alpha h q ≤ rankScore alpha h m) :
    Real.rpow ((q : ℝ) / m) alpha ≤ unresolvedMass h m / unresolvedMass h q := by
  apply ratio_of_weighted_min
  · exact unresolvedMass_pos hh q
  · exact_mod_cast hq
  · exact_mod_cast hm
  · simpa [rankScore] using hmin

/-- Equivalent cumulative-mass form of the minimizing-rank inequality. -/
theorem residual_drop_of_minimizing_rank
    {T q m : ℕ} {alpha : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h)
    (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hmin : rankScore alpha h q ≤ rankScore alpha h m) :
    unresolvedMass h q *
        (Real.rpow ((q : ℝ) / m) alpha - 1)
      ≤ unresolvedMass h m - unresolvedMass h q := by
  have hratio := residual_ratio_of_minimizing_rank hh hq hm hmin
  have hDq := unresolvedMass_pos hh q
  have hmul := mul_le_mul_of_nonneg_left hratio hDq.le
  have hcancel : unresolvedMass h q *
      (unresolvedMass h m / unresolvedMass h q) = unresolvedMass h m := by
    field_simp [hDq.ne']
  rw [hcancel] at hmul
  nlinarith

/-- At a minimizing rank, comparison with the final rank controls its score by capped mass. -/
theorem minimizing_score_le_final
    {T q : ℕ} {alpha : ℝ} {h : StepSchedule T}
    (hq : 1 ≤ q) (hqr : q ≤ longCount h)
    (hmin : ∀ s : ℕ, 1 ≤ s → s ≤ longCount h →
      rankScore alpha h q ≤ rankScore alpha h s) :
    rankScore alpha h q ≤ cappedMass h * Real.rpow (longCount h) alpha := by
  have hr : 1 ≤ longCount h := hq.trans hqr
  simpa [rankScore, unresolvedMass_longCount] using hmin (longCount h) hr le_rfl

end

end YeGDLowerBound
