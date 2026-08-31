import YeGDLowerBound.Definitions

/-!
# Algebraic envelope and product reductions
-/

namespace YeGDLowerBound

noncomputable section

open Real

/-- A positive number whose logarithm is at most `v` is at most `exp v`. -/
lemma le_exp_of_log_le {u v : ℝ} (hu : 0 < u) (hlog : Real.log u ≤ v) :
    u ≤ Real.exp v := by
  rw [← Real.exp_log hu]
  exact Real.exp_le_exp.mpr hlog

/-- Positivity of the left list in a pointwise positive `Forall₂` relation. -/
lemma list_prod_nonneg_of_forall₂
    {u v : List ℝ}
    (h : List.Forall₂ (fun x y => 0 < x ∧ Real.log x ≤ y) u v) :
    0 ≤ u.prod := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
      simp only [List.prod_cons]
      exact mul_nonneg hxy.1.le ih

/-- Pointwise logarithmic bounds multiply to an exponential sum bound. -/
theorem list_prod_le_exp_sum
    {u v : List ℝ}
    (h : List.Forall₂ (fun x y => 0 < x ∧ Real.log x ≤ y) u v) :
    u.prod ≤ Real.exp v.sum := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
      rcases hxy with ⟨hx, hlog⟩
      have hxe : x ≤ Real.exp y := le_exp_of_log_le hx hlog
      have hprod : 0 ≤ xs.prod := list_prod_nonneg_of_forall₂ hrest
      calc
        (x :: xs).prod = x * xs.prod := rfl
        _ ≤ Real.exp y * Real.exp ys.sum :=
          mul_le_mul hxe ih hprod (Real.exp_pos y).le
        _ = Real.exp (y + ys.sum) := (Real.exp_add y ys.sum).symm
        _ = Real.exp (y :: ys).sum := rfl

/-- The exact double-counting identity in Lemma 4. -/
lemma endpoint_mass_identity
    {q sx xFirst xLast Delta : ℝ}
    (hDelta : Delta = q - sx) :
    2 * sx - xFirst - xLast =
      2 * q - (2 * Delta + xFirst + xLast) := by
  rw [hDelta]
  ring

/-- Additive form of the envelope reduction once the endpoint remainder is bounded. -/
theorem envelope_reduction_additive
    {q sx xFirst xLast Delta lam edgeCost endpointLog : ℝ}
    (hDelta : Delta = q - sx)
    (hendpoint : endpointLog - lam * (2 * Delta + xFirst + xLast) ≤ 0) :
    endpointLog + lam * (2 * sx - xFirst - xLast) + edgeCost
      ≤ 2 * lam * q + edgeCost := by
  rw [endpoint_mass_identity hDelta]
  nlinarith

/-- A nonpositive scalar exponent gives a uniform rank bound. -/
theorem exp_rank_mul_le_one {q : ℕ} {J : ℝ} (hJ : J ≤ 0) :
    Real.exp ((q : ℝ) * J) ≤ 1 := by
  have hqJ : (q : ℝ) * J ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) hJ
  simpa using Real.exp_le_exp.mpr hqJ

end

end YeGDLowerBound
