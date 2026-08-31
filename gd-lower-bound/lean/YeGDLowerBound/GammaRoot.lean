import YeGDLowerBound.GammaScalar
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence and uniqueness of the scalar optimizer
-/

namespace YeGDLowerBound

noncomputable section

open Real Set Filter Topology

lemma continuous_optA (w : ℝ) : Continuous (optA w) := by
  unfold optA
  fun_prop

lemma optA_strictMono {w : ℝ} (hw : 0 < w) :
    StrictMonoOn (optA w) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hrad0 : 0 ≤ w ^ 2 + 4 * w * a := by
    nlinarith [sq_nonneg w, mul_nonneg hw.le ha.le]
  have hradlt : w ^ 2 + 4 * w * a < w ^ 2 + 4 * w * b := by
    nlinarith
  have hsqrt := Real.sqrt_lt_sqrt hrad0 hradlt
  unfold optA
  linarith

lemma rootEq_continuousAt {lam w z tau : ℝ}
    (hw : 0 < w) (hz : 0 < z) (ht : 0 < tau) :
    ContinuousAt (rootEq lam w z) tau := by
  have htwo : (2 * tau : ℝ) ≠ 0 := by nlinarith
  have hsum : optA w tau + optA z tau ≠ 0 :=
    ne_of_gt (add_pos (optA_pos hw ht) (optA_pos hz ht))
  have hden1 : ContinuousAt (fun t : ℝ => 2 * t) tau :=
    continuousAt_const.mul continuousAt_id
  have hden2 : ContinuousAt (fun t : ℝ => optA w t + optA z t) tau :=
    (continuous_optA w).continuousAt.add (continuous_optA z).continuousAt
  have hfirst : ContinuousAt (fun t : ℝ => 1 / (2 * t)) tau :=
    continuousAt_const.div₀ hden1 htwo
  have hsecond : ContinuousAt (fun t : ℝ => 1 / (optA w t + optA z t)) tau :=
    continuousAt_const.div₀ hden2 hsum
  exact (hfirst.add hsecond).sub continuousAt_const

lemma rootEq_continuousOn {lam w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    ContinuousOn (rootEq lam w z) (Set.Ioi 0) := by
  intro tau ht
  exact (rootEq_continuousAt hw hz ht).continuousWithinAt

lemma rootEq_strictAnti {lam w z : ℝ} (hw : 0 < w) (hz : 0 < z) :
    StrictAntiOn (rootEq lam w z) (Set.Ioi 0) := by
  intro a ha b hb hab
  have h2a : 0 < 2 * a := by nlinarith
  have h2b : 0 < 2 * b := by nlinarith
  have hfirst : 1 / (2 * b) < 1 / (2 * a) := by
    rw [div_lt_div_iff₀ h2b h2a]
    nlinarith
  have hAw : optA w a < optA w b := optA_strictMono hw ha hb hab
  have hAz : optA z a < optA z b := optA_strictMono hz ha hb hab
  have hsum : optA w a + optA z a < optA w b + optA z b := add_lt_add hAw hAz
  have hsumA : 0 < optA w a + optA z a :=
    add_pos (optA_pos hw ha) (optA_pos hz ha)
  have hsumB : 0 < optA w b + optA z b :=
    add_pos (optA_pos hw hb) (optA_pos hz hb)
  have hsecond :
      1 / (optA w b + optA z b) < 1 / (optA w a + optA z a) := by
    rw [div_lt_div_iff₀ hsumB hsumA]
    simpa using hsum
  unfold rootEq
  linarith

/-- A convenient explicit lower bracket. -/
def rootLo (lam : ℝ) : ℝ := 1 / (2 * lam)

/-- A convenient explicit upper bracket. -/
def rootHi (lam w : ℝ) : ℝ := 2 / lam + 16 / (lam ^ 2 * w)

lemma rootLo_pos {lam : ℝ} (hlam : 0 < lam) : 0 < rootLo lam := by
  unfold rootLo
  exact one_div_pos.mpr (mul_pos (by norm_num) hlam)

lemma rootHi_pos {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    0 < rootHi lam w := by
  unfold rootHi
  exact add_pos (div_pos (by norm_num) hlam)
    (div_pos (by norm_num) (mul_pos (sq_pos_of_pos hlam) hw))

lemma sqrt_mul_le_optA {w tau : ℝ} (hw : 0 < w) (ht : 0 < tau) :
    Real.sqrt (w * tau) ≤ optA w tau := by
  have hX := optX_pos hw ht
  have hA := optA_pos hw ht
  have hXA := optX_mul_optA hw ht
  have hle : optX w tau ≤ optA w tau := by
    rw [optA_eq_add_optX]
    linarith
  rw [Real.sqrt_le_left hA.le]
  calc
    w * tau = optX w tau * optA w tau := hXA.symm
    _ ≤ optA w tau * optA w tau :=
      mul_le_mul_of_nonneg_right hle hA.le
    _ = optA w tau ^ 2 := by ring

lemma rootEq_rootLo_pos {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    0 < rootEq lam w z (rootLo lam) := by
  have hlo := rootLo_pos hlam
  have hsum : 0 < optA w (rootLo lam) + optA z (rootLo lam) :=
    add_pos (optA_pos hw hlo) (optA_pos hz hlo)
  have hfirst : 1 / (2 * rootLo lam) = lam := by
    unfold rootLo
    field_simp [hlam.ne']
  have hrecip : 0 < 1 / (optA w (rootLo lam) + optA z (rootLo lam)) :=
    one_div_pos.mpr hsum
  unfold rootEq
  rw [hfirst]
  linarith

lemma four_div_le_sqrt_at_rootHi {lam w : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) :
    4 / lam ≤ Real.sqrt (w * rootHi lam w) := by
  have hhi := rootHi_pos hlam hw
  have hleft : 0 ≤ 4 / lam := (div_pos (by norm_num) hlam).le
  have hright : 0 ≤ w * rootHi lam w := mul_nonneg hw.le hhi.le
  rw [Real.le_sqrt hleft hright]
  have hsquare : (4 / lam) ^ 2 = 16 / lam ^ 2 := by
    field_simp [hlam.ne']
    ring
  rw [hsquare]
  have heq :
      w * rootHi lam w = 2 * w / lam + 16 / lam ^ 2 := by
    unfold rootHi
    field_simp [hlam.ne', hw.ne']
    ring
  rw [heq]
  have hnonneg : 0 ≤ 2 * w / lam := (div_pos (mul_pos (by norm_num) hw) hlam).le
  linarith

lemma rootEq_rootHi_neg {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    rootEq lam w z (rootHi lam w) < 0 := by
  let hi := rootHi lam w
  have hhi : 0 < hi := rootHi_pos hlam hw
  have hAw : 4 / lam ≤ optA w hi :=
    (four_div_le_sqrt_at_rootHi hlam hw).trans (sqrt_mul_le_optA hw hhi)
  have hAz : 0 < optA z hi := optA_pos hz hhi
  have hsum : 0 < optA w hi + optA z hi := add_pos (optA_pos hw hhi) hAz
  have hterm : 0 < 16 / (lam ^ 2 * w) :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos hlam) hw)
  have hhiLower : 2 / lam < hi := by
    unfold hi rootHi
    linarith
  have hmulLower := mul_lt_mul_of_pos_left hhiLower hlam
  have hbase : lam * (2 / lam) = 2 := by field_simp [hlam.ne']
  rw [hbase] at hmulLower
  have hfirst : 1 / (2 * hi) < lam / 4 := by
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hhi) (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have hAwMul := mul_le_mul_of_nonneg_left hAw hlam.le
  have hAwEq : lam * (4 / lam) = 4 := by field_simp [hlam.ne']
  rw [hAwEq] at hAwMul
  have hfour : 4 ≤ lam * (optA w hi + optA z hi) := by
    nlinarith [mul_pos hlam hAz]
  have hsecond : 1 / (optA w hi + optA z hi) ≤ lam / 4 := by
    rw [div_le_div_iff₀ hsum (by norm_num : (0 : ℝ) < 4)]
    simpa [mul_comm] using hfour
  unfold rootEq
  change 1 / (2 * hi) + 1 / (optA w hi + optA z hi) - lam < 0
  linarith

/-- Existence and uniqueness of the positive scalar root. -/
theorem exists_unique_rootEq {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    ∃! tau : ℝ, 0 < tau ∧ rootEq lam w z tau = 0 := by
  let lo := rootLo lam
  let hi := rootHi lam w
  have hlo : 0 < lo := rootLo_pos hlam
  have hhi : 0 < hi := rootHi_pos hlam hw
  have hterm : 0 < 16 / (lam ^ 2 * w) :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos hlam) hw)
  have hlohi : lo ≤ hi := by
    unfold lo hi rootLo rootHi
    have hhalf : 1 / (2 * lam) ≤ 2 / lam := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hlam) hlam]
      nlinarith
    linarith
  have hcont : ContinuousOn (rootEq lam w z) (Set.Icc lo hi) :=
    (rootEq_continuousOn hw hz).mono fun tau ht => lt_of_lt_of_le hlo ht.1
  have hlow := rootEq_rootLo_pos hlam hw hz
  have hupp := rootEq_rootHi_neg hlam hw hz
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (rootEq lam w z hi) (rootEq lam w z lo) :=
    ⟨hupp.le, hlow.le⟩
  obtain ⟨tau, htau, hroot⟩ := intermediate_value_Icc' hlohi hcont hzeroMem
  refine ⟨tau, ⟨hlo.trans_le htau.1, hroot⟩, ?_⟩
  intro s hs
  apply (rootEq_strictAnti hw hz).injOn
  · exact hs.1
  · exact hlo.trans_le htau.1
  · exact hs.2.trans hroot.symm

/-- The unique positive optimizer parameter. -/
def tauStar (lam w z : ℝ) : ℝ :=
  if h : 0 < lam ∧ 0 < w ∧ 0 < z then
    Classical.choose (exists_unique_rootEq h.1 h.2.1 h.2.2)
  else 1

lemma tauStar_pos {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    0 < tauStar lam w z := by
  rw [tauStar, dif_pos ⟨hlam, hw, hz⟩]
  exact (Classical.choose_spec (exists_unique_rootEq hlam hw hz)).1.1

lemma rootEq_tauStar {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    rootEq lam w z (tauStar lam w z) = 0 := by
  rw [tauStar, dif_pos ⟨hlam, hw, hz⟩]
  exact (Classical.choose_spec (exists_unique_rootEq hlam hw hz)).1.2

lemma tauStar_unique {lam w z tau : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z)
    (ht : 0 < tau) (hroot : rootEq lam w z tau = 0) :
    tau = tauStar lam w z := by
  rw [tauStar, dif_pos ⟨hlam, hw, hz⟩]
  exact (Classical.choose_spec (exists_unique_rootEq hlam hw hz)).2 tau ⟨ht, hroot⟩

end

end YeGDLowerBound
