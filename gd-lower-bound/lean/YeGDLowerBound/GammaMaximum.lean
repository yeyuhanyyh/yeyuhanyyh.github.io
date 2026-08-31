import YeGDLowerBound.GammaObjective

/-!
# Global maximization of the Gamma objective
-/

namespace YeGDLowerBound

noncomputable section

open Real Set

/-- A differentiable concave function lies below every tangent line. -/
lemma concave_tangent_le {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ}
    (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivAt f d x) :
    f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | hxy | hxy
  · have hs := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at hs
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hmul := (le_div_iff₀ hpos).mp hs
    linarith
  · subst y
    simp
  · have hs := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at hs
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hmul := (div_le_iff₀ hpos).mp hs
    linarith

/-- Strict tangent inequality away from the tangent point. -/
lemma strictConcave_tangent_lt {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ}
    (hf : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : y ≠ x) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  rcases lt_or_gt_of_ne hxy with hyx | hxy
  · have hs := hf.lt_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at hs
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hmul := (lt_div_iff₀ hpos).mp hs
    linarith
  · have hs := hf.slope_lt_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at hs
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hmul := (div_lt_iff₀ hpos).mp hs
    linarith

lemma phi_deriv_inv_form {w x : ℝ} (hw : 0 < w) (hx : 0 < x) :
    w / (2 * x * (w + x)) = 1 / (2 * x) - 1 / (2 * (w + x)) := by
  field_simp [hw.ne', hx.ne', (add_pos hw hx).ne']
  ring

/-- The root parameter produces a stationary point of the two-dimensional objective. -/
lemma gammaObjective_stationary {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    let tau := tauStar lam w z
    let X := optX w tau
    let Y := optX z tau
    let Sigma := w + z + X + Y
    w / (2 * X * (w + X)) + 1 / Sigma - lam = 0 ∧
    z / (2 * Y * (z + Y)) + 1 / Sigma - lam = 0 := by
  dsimp
  have ht : 0 < tauStar lam w z := tauStar_pos hlam hw hz
  have hroot : rootEq lam w z (tauStar lam w z) = 0 :=
    rootEq_tauStar hlam hw hz
  rcases scalar_FOC hw hz ht hroot with ⟨hx, hy⟩
  have hAw := optA_eq_add_optX w (tauStar lam w z)
  have hAz := optA_eq_add_optX z (tauStar lam w z)
  have hdx := phi_deriv_inv_form hw (optX_pos hw ht)
  have hdy := phi_deriv_inv_form hz (optX_pos hz ht)
  constructor
  · rw [hdx, ← hAw, ← hAz]
    exact hx
  · rw [hdy, ← hAw, ← hAz]
    exact hy

/-- The scalar point globally maximizes the logarithmic objective. -/
theorem gammaObjective_le_optimizer {lam w z x y : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z)
    (hx : 0 < x) (hy : 0 < y) :
    let tau := tauStar lam w z
    let X := optX w tau
    let Y := optX z tau
    gammaObjective lam w z x y ≤ gammaObjective lam w z X Y := by
  dsimp
  let tau := tauStar lam w z
  let X := optX w tau
  let Y := optX z tau
  let Sigma := w + z + X + Y
  let dx := w / (2 * X * (w + X))
  let dy := z / (2 * Y * (z + Y))
  let c := 1 / Sigma
  have ht : 0 < tau := tauStar_pos hlam hw hz
  have hX : 0 < X := optX_pos hw ht
  have hY : 0 < Y := optX_pos hz ht
  have hSigma : 0 < Sigma := by
    dsimp [Sigma, X, Y]
    positivity
  have hphiX : phi w x ≤ phi w X + dx * (x - X) := by
    exact concave_tangent_le (strictConcaveOn_phi hw).concaveOn hX hx
      (hasDerivAt_phi hw hX)
  have hphiY : phi z y ≤ phi z Y + dy * (y - Y) := by
    exact concave_tangent_le (strictConcaveOn_phi hz).concaveOn hY hy
      (hasDerivAt_phi hz hY)
  have hsumxy : 0 < w + z + x + y := by positivity
  have hlog :
      Real.log (w + z + x + y) ≤
        Real.log Sigma + c * ((w + z + x + y) - Sigma) := by
    exact concave_tangent_le strictConcaveOn_log_Ioi.concaveOn hSigma hsumxy
      (Real.hasDerivAt_log hSigma.ne')
  have hstat := gammaObjective_stationary hlam hw hz
  dsimp only at hstat
  rcases hstat with ⟨hstatX, hstatY⟩
  have hdx : dx = lam - c := by
    dsimp [tau, X, Y, Sigma, dx, c] at hstatX ⊢
    linarith
  have hdy : dy = lam - c := by
    dsimp [tau, X, Y, Sigma, dy, c] at hstatY ⊢
    linarith
  have hcancel :
      dx * (x - X) + dy * (y - Y) +
          c * ((w + z + x + y) - Sigma)
        = lam * ((x - X) + (y - Y)) := by
    rw [hdx, hdy]
    dsimp [Sigma]
    ring
  unfold gammaObjective
  calc
    phi w x + phi z y + Real.log (w + z + x + y) -
          (Real.log w + Real.log z) / 2 - lam * (x + y)
        ≤ (phi w X + dx * (x - X)) +
            (phi z Y + dy * (y - Y)) +
            (Real.log Sigma + c * ((w + z + x + y) - Sigma)) -
            (Real.log w + Real.log z) / 2 - lam * (x + y) := by
              linarith
    _ = phi w X + phi z Y + Real.log (w + z + X + Y) -
          (Real.log w + Real.log z) / 2 - lam * (X + Y) := by
            rw [hcancel]
            dsimp [Sigma]
            ring

/-- The optimizer is unique. -/
theorem gammaObjective_lt_optimizer_of_ne {lam w z x y : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z)
    (hx : 0 < x) (hy : 0 < y)
    (hne : (x, y) ≠
      (optX w (tauStar lam w z), optX z (tauStar lam w z))) :
    gammaObjective lam w z x y <
      gammaObjective lam w z
        (optX w (tauStar lam w z)) (optX z (tauStar lam w z)) := by
  let tau := tauStar lam w z
  let X := optX w tau
  let Y := optX z tau
  let Sigma := w + z + X + Y
  let dx := w / (2 * X * (w + X))
  let dy := z / (2 * Y * (z + Y))
  let c := 1 / Sigma
  have ht : 0 < tau := tauStar_pos hlam hw hz
  have hX : 0 < X := optX_pos hw ht
  have hY : 0 < Y := optX_pos hz ht
  have hSigma : 0 < Sigma := by
    dsimp [Sigma, X, Y]
    positivity
  have hsumxy : 0 < w + z + x + y := by positivity
  have hlog :
      Real.log (w + z + x + y) ≤
        Real.log Sigma + c * ((w + z + x + y) - Sigma) := by
    exact concave_tangent_le strictConcaveOn_log_Ioi.concaveOn hSigma hsumxy
      (Real.hasDerivAt_log hSigma.ne')
  have hstat := gammaObjective_stationary hlam hw hz
  dsimp only at hstat
  rcases hstat with ⟨hstatX, hstatY⟩
  have hdx : dx = lam - c := by
    dsimp [tau, X, Y, Sigma, dx, c] at hstatX ⊢
    linarith
  have hdy : dy = lam - c := by
    dsimp [tau, X, Y, Sigma, dy, c] at hstatY ⊢
    linarith
  have hcancel :
      dx * (x - X) + dy * (y - Y) +
          c * ((w + z + x + y) - Sigma)
        = lam * ((x - X) + (y - Y)) := by
    rw [hdx, hdy]
    dsimp [Sigma]
    ring
  by_cases hxX : x = X
  · have hyY : y ≠ Y := by
      intro hyEq
      apply hne
      simpa [X, Y, tau, hxX, hyEq]
    have hphiX : phi w x ≤ phi w X + dx * (x - X) := by
      exact concave_tangent_le (strictConcaveOn_phi hw).concaveOn hX hx
        (hasDerivAt_phi hw hX)
    have hphiY : phi z y < phi z Y + dy * (y - Y) := by
      exact strictConcave_tangent_lt (strictConcaveOn_phi hz) hY hy hyY
        (hasDerivAt_phi hz hY)
    unfold gammaObjective
    calc
      phi w x + phi z y + Real.log (w + z + x + y) -
            (Real.log w + Real.log z) / 2 - lam * (x + y)
          < (phi w X + dx * (x - X)) +
              (phi z Y + dy * (y - Y)) +
              (Real.log Sigma + c * ((w + z + x + y) - Sigma)) -
              (Real.log w + Real.log z) / 2 - lam * (x + y) := by
                linarith
      _ = phi w X + phi z Y + Real.log (w + z + X + Y) -
            (Real.log w + Real.log z) / 2 - lam * (X + Y) := by
              rw [hcancel]
              dsimp [Sigma]
              ring
  · have hphiX : phi w x < phi w X + dx * (x - X) := by
      exact strictConcave_tangent_lt (strictConcaveOn_phi hw) hX hx hxX
        (hasDerivAt_phi hw hX)
    have hphiY : phi z y ≤ phi z Y + dy * (y - Y) := by
      exact concave_tangent_le (strictConcaveOn_phi hz).concaveOn hY hy
        (hasDerivAt_phi hz hY)
    unfold gammaObjective
    calc
      phi w x + phi z y + Real.log (w + z + x + y) -
            (Real.log w + Real.log z) / 2 - lam * (x + y)
          < (phi w X + dx * (x - X)) +
              (phi z Y + dy * (y - Y)) +
              (Real.log Sigma + c * ((w + z + x + y) - Sigma)) -
              (Real.log w + Real.log z) / 2 - lam * (x + y) := by
                linarith
      _ = phi w X + phi z Y + Real.log (w + z + X + Y) -
            (Real.log w + Real.log z) / 2 - lam * (X + Y) := by
              rw [hcancel]
              dsimp [Sigma]
              ring

lemma gammaRange_nonempty (lam w z : ℝ) : (gammaRange lam w z).Nonempty := by
  refine ⟨Real.log (kernel w z 1 1) - lam * 2, ?_⟩
  exact ⟨1, by norm_num, 1, by norm_num, by ring⟩

lemma gammaRange_bddAbove {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    BddAbove (gammaRange lam w z) := by
  refine ⟨gammaObjective lam w z
      (optX w (tauStar lam w z)) (optX z (tauStar lam w z)), ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, y, hy, rfl⟩
  rw [← gammaObjective_eq_log_kernel hw hz hx hy]
  exact gammaObjective_le_optimizer hlam hw hz hx hy

/-- Explicit formula for the supremum defining `Gamma`. -/
theorem Gamma_eq_optimizer {lam w z : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z) :
    Gamma lam w z = gammaObjective lam w z
      (optX w (tauStar lam w z)) (optX z (tauStar lam w z)) := by
  apply le_antisymm
  · apply csSup_le (gammaRange_nonempty lam w z)
    intro r hr
    rcases hr with ⟨x, hx, y, hy, rfl⟩
    rw [← gammaObjective_eq_log_kernel hw hz hx hy]
    exact gammaObjective_le_optimizer hlam hw hz hx hy
  · apply le_csSup (gammaRange_bddAbove hlam hw hz)
    let tau := tauStar lam w z
    have ht : 0 < tau := tauStar_pos hlam hw hz
    exact ⟨optX w tau, optX_pos hw ht, optX z tau, optX_pos hz ht,
      by rw [gammaObjective_eq_log_kernel hw hz (optX_pos hw ht) (optX_pos hz ht)]⟩

/-- The pair appearing in the scalar formula is the unique positive optimizer. -/
theorem unique_Gamma_optimizer {lam w z x y : ℝ}
    (hlam : 0 < lam) (hw : 0 < w) (hz : 0 < z)
    (hx : 0 < x) (hy : 0 < y)
    (hmax : Real.log (kernel w z x y) - lam * (x + y) = Gamma lam w z) :
    (x, y) =
      (optX w (tauStar lam w z), optX z (tauStar lam w z)) := by
  by_contra hne
  have hlt := gammaObjective_lt_optimizer_of_ne hlam hw hz hx hy hne
  rw [gammaObjective_eq_log_kernel hw hz hx hy, ← Gamma_eq_optimizer hlam hw hz] at hlt
  linarith

end

end YeGDLowerBound
