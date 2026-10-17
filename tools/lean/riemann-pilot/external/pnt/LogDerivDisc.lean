/-
# Round 513: the log-derivative of a function with no zero in a half-plane, by the disc step

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `F` be holomorphic on the disc of radius `2ρ` around `3/2 + it`, `ρ = 3/2 − θ`, with no zero
in `Re s > θ`. If `|F(3/2 + it + ρw)/F(3/2 + it)| ≤ B` for `|w| ≤ Rld θ θ'`, then `|F′/F(σ + it)| ≤ Kld θ θ' · log B`
on `θ' ≤ σ < 3/2`, where `Kld` and `Rld` depend on `θ < θ' < 3/2` only (`logDeriv_le_Kld`). For an entire `F` with
`|F(s)| ≤ c(|Im s| + 2)` on `θ ≤ Re s ≤ 3`, `1/|F(3/2 + it)| ≤ A` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`, this gives
`|F′/F(σ + it)| ≤ Kld θ θ' · (log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'` (`logDeriv_le_uniform_of`).

* `disc_point`: PNT+'s `FinalBound` (Borel–Carathéodory with the zeros divided out) for `locG`, the quotient
  `F(3/2 + it + ρw)/F(3/2 + it)`, on the unit disc, which holds no zero of `F`.
* `logDeriv_le_Kld`: `disc_point` at the radii `r' = (3/2 − θ')/ρ`, `r = r' + (1 − r')/4`, `R' = r' + (1 − r')/2`
  and `R = r' + 3(1 − r')/4` (`Rld`).
* `logDeriv_le_uniform_of`, `logDeriv_le_uniform`: `logDeriv_le_Kld` with `B = 2 + 2cA(|t| + 4)`.
* `disc_point_ball`, `logDeriv_le_Kld_ball`, `logDeriv_le_ball` (round 520): the same three steps with no zero of
  `F` in the disc of radius `3/2 − θ` about `3/2 + it` only, which is what a zero-free region of bounded height
  supplies (`Linnik.logDeriv_LFunction_le`). The half-plane forms above follow from them, since that disc lies
  in `Re s > θ` (`re_gt_of_mem_ball`).

History. Round 337 proved the disc step for `ζ` (`HalfPlanePNT.disc_point`); round 478 proved it for an entire `F`
with the same text (`ChiPNT.disc_point`); round 480 kept the constants (`ChiUniform.Kld`,
`ChiUniform.logDeriv_le_uniform_of`, `ChiUniform.logDeriv_le_uniform`), and the three files each repeated the
radii. Round 513 (STRUCTURAL-REVIEW §9.3, U3 and U4) moves the disc step here for an `F` holomorphic on the disc,
which covers `ζ` at `|t| > 3`, and states the radii once (`logDeriv_le_Kld`). The disc helpers (`ctr`, `re_ge`,
`one_lt_log_three`) come from round 337's `HalfPlanePNT`, `locG` and `disc_point` from round 478's `ChiPNT`, and
`Kld` and the two bounds from round 480's `ChiUniform`. Round 520 proves the disc step for a zero-free disc and
derives the half-plane forms from it, so the radii are still stated once.
-/
import Landau

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology

namespace LogDerivDisc

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- Real parts on a disc. -/
lemma re_ge {x ρ : ℝ} (w : ℂ) (hρ : 0 ≤ ρ) : x - ρ * ‖w‖ ≤ x + ρ * w.re := by
  have h : -‖w‖ ≤ w.re := by
    have := Complex.abs_re_le_norm w; linarith [neg_abs_le w.re]
  have := mul_le_mul_of_nonneg_left h hρ
  linarith

/-- The centre `3/2 + it` of the discs. -/
noncomputable def ctr (t : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I

lemma ctr_re (t : ℝ) : (ctr t).re = 3 / 2 := by simp [ctr]
lemma ctr_im (t : ℝ) : (ctr t).im = t := by simp [ctr]

lemma ctr_add_re (t ρ : ℝ) (w : ℂ) : (ctr t + ρ * w).re = 3 / 2 + ρ * w.re := by
  simp [ctr_re, mul_re]

lemma ctr_add_im (t ρ : ℝ) (w : ℂ) : (ctr t + ρ * w).im = t + ρ * w.im := by
  simp [ctr_im, mul_im]

/-- `F(s₀ + ρw)/F(s₀)`. -/
noncomputable def locG (F : ℂ → ℂ) (s₀ : ℂ) (ρ : ℝ) (w : ℂ) : ℂ := F (s₀ + ρ * w) / F s₀

lemma mem_ball_of_norm_lt {s₀ w : ℂ} {ρ a : ℝ} (hρ : 0 < ρ) (hw : ‖w‖ < a) :
    s₀ + ρ * w ∈ Metric.ball s₀ (a * ρ) := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hρ.le, mul_comm]
  exact mul_lt_mul_of_pos_right hw hρ

/-- `locG` is analytic on `|w| < 2` when `F` is holomorphic on the disc of radius `2ρ` around `s₀`. -/
lemma analyticOnNhd_locG {F : ℂ → ℂ} {s₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hFd : DifferentiableOn ℂ F (Metric.ball s₀ (2 * ρ))) :
    AnalyticOnNhd ℂ (locG F s₀ ρ) (Metric.ball (0 : ℂ) 2) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hA : AnalyticAt ℂ F (s₀ + ρ * w) :=
    hFd.analyticAt (Metric.isOpen_ball.mem_nhds (mem_ball_of_norm_lt hρ hw))
  have hlin : AnalyticAt ℂ (fun w : ℂ => s₀ + ρ * w) w := by fun_prop
  exact (AnalyticAt.fun_comp (f := fun w : ℂ => s₀ + ρ * w) hA hlin).div_const

lemma locG_logDeriv {F : ℂ → ℂ} {s₀ z : ℂ} {ρ : ℝ} (hF : DifferentiableAt ℂ F (s₀ + ρ * z))
    (hF0 : F s₀ ≠ 0) (hFz : F (s₀ + ρ * z) ≠ 0) :
    deriv (locG F s₀ ρ) z / locG F s₀ ρ z = ρ * (deriv F (s₀ + ρ * z) / F (s₀ + ρ * z)) := by
  have h1 : HasDerivAt F (deriv F (s₀ + ρ * z)) (s₀ + ρ * z) := hF.hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => s₀ + ρ * w) (ρ : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (ρ : ℂ)).const_add s₀
  have h2 := (h1.comp z hlin).div_const (F s₀)
  have hderiv : deriv (locG F s₀ ρ) z = ρ * deriv F (s₀ + ρ * z) / F s₀ := by
    rw [show locG F s₀ ρ = fun w => (F ∘ fun w : ℂ => s₀ + ρ * w) w / F s₀ by
      funext w; simp [locG], h2.deriv]
    ring
  rw [hderiv]; simp only [locG]; field_simp

/-- Points of the open disc of radius `3/2 − θ` about `3/2 + it` have real part `> θ`. -/
lemma re_gt_of_mem_ball {θ t : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (ctr t) (3 / 2 - θ)) : θ < s.re := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h := Complex.abs_re_le_norm (s - ctr t)
  rw [sub_re, ctr_re] at h
  have := neg_abs_le (s.re - 3 / 2)
  linarith

/-- Points of the open disc of radius `3/2 − θ ≤ 1` about `3/2 + it` have `|Im s − t| < 1`. -/
lemma im_sub_lt_of_mem_ball {θ t : ℝ} (hθ : 1 / 2 ≤ θ) {s : ℂ} (hs : s ∈ Metric.ball (ctr t) (3 / 2 - θ)) :
    |s.im - t| < 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h := Complex.abs_im_le_norm (s - ctr t)
  rw [sub_im, ctr_im] at h
  linarith

/-- **The disc step.** Let `F` be holomorphic on the disc of radius `2ρ`, `ρ = 3/2 − θ`, around `3/2 + it`, with
no zero in the disc of radius `ρ` around it. With radii `0 < r' < r < R' < R < 1`, at a point `σ + it` with
`θ < σ < 3/2` and `3/2 − σ ≤ ρr'`, if `|F(3/2 + it + ρw)/F(3/2 + it)| ≤ B` on `|w| ≤ R`, then
`ρ|F′/F(σ + it)| ≤ K log B` with the constant `K` of PNT+'s `FinalBound`. The zero-free hypothesis is used at the
centre, at the evaluation point and at the zeros of radius at most `r < 1` (round 520). -/
lemma disc_point_ball {F : ℂ → ℂ} {θ σ t r' r R' R B : ℝ}
    (hFd : DifferentiableOn ℂ F (Metric.ball (ctr t) (2 * (3 / 2 - θ)))) (hθσ : θ < σ)
    (hr'0 : 0 < r') (hr'r : r' < r) (hr1 : r < 1) (hrR' : r < R') (hR'R : R' < R) (hR1 : R < 1)
    (hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ)) (hσ32 : σ < 3 / 2)
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), F s ≠ 0) (hB : 1 < B)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG F (ctr t) (3 / 2 - θ) w‖ ≤ B) :
    (3 / 2 - θ) * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  have hin : ∀ w : ℂ, ‖w‖ < 1 → ctr t + ρ * w ∈ Metric.ball (ctr t) ρ := fun w hw => by
    simpa using mem_ball_of_norm_lt (s₀ := ctr t) hρ hw
  set f := locG F (ctr t) ρ with hfdef
  have hF0 : F (ctr t) ≠ 0 := hzf _ (Metric.mem_ball_self hρ)
  have hf0 : f 0 = 1 := by simp [hfdef, locG, hF0]
  have hfA2 : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 2) := analyticOnNhd_locG hρ hFd
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := fun w hw => hfA2 w (by
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]; linarith)
  have hfin : (SetOfZeros 1 f).Finite :=
    Landau.finiteZeros_of_analytic hfA2 (by rw [hf0]; exact one_ne_zero)
  set z : ℂ := (((σ - 3 / 2) / ρ : ℝ) : ℂ) with hzdef
  have hsz : ctr t + ρ * z = (σ : ℂ) + t * I := by
    apply Complex.ext
    · have e : ((σ : ℂ) + t * I).re = σ := by simp
      rw [ctr_add_re, hzdef, ofReal_re, e]; field_simp; ring
    · rw [ctr_add_im, hzdef, ofReal_im]; simp
  have hznorm : ‖z‖ ≤ r' := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hρ,
      abs_of_neg (by linarith), div_le_iff₀ hρ]
    linarith
  have hFdz : DifferentiableAt ℂ F (ctr t + ρ * z) :=
    hFd.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_of_norm_lt hρ (by linarith)))
  have hFz : F (ctr t + ρ * z) ≠ 0 := hzf _ (hin z (by linarith))
  have hfz : f z ≠ 0 := by
    simp only [hfdef, locG, div_ne_zero_iff]; exact ⟨hFz, hF0⟩
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f :=
    ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hznorm, fun h => hfz h.2⟩
  have FB := FinalBound (B := B) (r' := r') (r := r) (R' := R') (R := R) hB hr'0 hr'r hr1 hrR' hR'R hR1
    hfA hf0 hfin hfb hzmem
  have hsum : ∑ q ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
      (analyticOrderNatAt f q : ℂ) / (z - q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    exfalso
    rw [Set.Finite.mem_toFinset] at hq
    have hzero : F (ctr t + ρ * q) = 0 := by
      have := hq.2; simp only [hfdef, locG, div_eq_zero_iff, hF0, or_false] at this; exact this
    exact hzf _ (hin q (by linarith [hq.1])) hzero
  rw [hsum, sub_zero, locG_logDeriv hFdz hF0 hFz, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, hsz] at FB
  exact FB

/-- **The disc step** with no zero in `Re s > θ` (`disc_point_ball`, as that half-plane contains the disc). -/
lemma disc_point {F : ℂ → ℂ} {θ σ t r' r R' R B : ℝ}
    (hFd : DifferentiableOn ℂ F (Metric.ball (ctr t) (2 * (3 / 2 - θ)))) (hθσ : θ < σ)
    (hr'0 : 0 < r') (hr'r : r' < r) (hr1 : r < 1) (hrR' : r < R') (hR'R : R' < R) (hR1 : R < 1)
    (hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ)) (hσ32 : σ < 3 / 2)
    (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0) (hB : 1 < B)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG F (ctr t) (3 / 2 - θ) w‖ ≤ B) :
    (3 / 2 - θ) * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B :=
  disc_point_ball hFd hθσ hr'0 hr'r hr1 hrR' hR'R hR1 hz hσ32 (fun s hs => hzf s (re_gt_of_mem_ball hs)) hB hfb

/-- The constant of `logDeriv_le_Kld`. With `ρ = 3/2 − θ`, `r' = (3/2 − θ')/ρ`, `r = r' + (1 − r')/4`,
`R' = r' + (1 − r')/2` and `R = r' + 3(1 − r')/4`, it is `(16r²/(r − r')³ + 1/((R²/R' − R') log(R/R')))/ρ`. -/
noncomputable def Kld (θ θ' : ℝ) : ℝ :=
  let ρ := 3 / 2 - θ
  let r' := (3 / 2 - θ') / ρ
  let r := r' + (1 - r') / 4
  let R' := r' + (1 - r') / 2
  let R := r' + 3 * (1 - r') / 4
  (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) / ρ

/-- The outer radius `R = r' + 3(1 − r')/4` of `Kld`, `r' = (3/2 − θ')/(3/2 − θ)`. -/
noncomputable def Rld (θ θ' : ℝ) : ℝ :=
  let r' := (3 / 2 - θ') / (3 / 2 - θ)
  r' + 3 * (1 - r') / 4

lemma Rld_lt_one {θ θ' : ℝ} (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) : Rld θ θ' < 1 := by
  have hr'1 : (3 / 2 - θ') / (3 / 2 - θ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  simp only [Rld]; linarith

lemma Kld_pos {θ θ' : ℝ} (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) : 0 < Kld θ θ' := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  set r' : ℝ := (3 / 2 - θ') / ρ with hr'def
  have hr'0 : 0 < r' := div_pos (by linarith) hρ
  have hr'1 : r' < 1 := by rw [hr'def, div_lt_one hρ]; linarith
  set r : ℝ := r' + (1 - r') / 4 with hrdef
  set R' : ℝ := r' + (1 - r') / 2 with hR'def
  set R : ℝ := r' + 3 * (1 - r') / 4 with hRdef
  have hR'0 : 0 < R' := by linarith
  have h1 : 0 < R ^ 2 / R' - R' := by
    rw [sub_pos, lt_div_iff₀ hR'0]; nlinarith
  have h2 : 0 < Real.log (R / R') := Real.log_pos (by rw [one_lt_div hR'0]; linarith)
  have h3 : 0 < 16 * r ^ 2 / (r - r') ^ 3 := by
    have : 0 < r - r' := by linarith
    have : 0 < r := by linarith
    positivity
  have hKld : Kld θ θ' = (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) / ρ := rfl
  rw [hKld]
  have h4 : 0 < 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) := by positivity
  positivity

/-- **The log-derivative at the radii of `Kld`.** Let `F` be holomorphic on the disc of radius `2ρ`,
`ρ = 3/2 − θ`, around `3/2 + it`, with no zero in the disc of radius `ρ` around it, and
`|F(3/2 + it + ρw)/F(3/2 + it)| ≤ B` on `|w| ≤ Rld θ θ'`. Then `|F′/F(σ + it)| ≤ Kld θ θ' · log B` for
`θ' ≤ σ < 3/2`. -/
theorem logDeriv_le_Kld_ball {F : ℂ → ℂ} {θ θ' σ t B : ℝ} (hθθ' : θ < θ') (hσ : θ' ≤ σ) (hσ32 : σ < 3 / 2)
    (hFd : DifferentiableOn ℂ F (Metric.ball (ctr t) (2 * (3 / 2 - θ))))
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), F s ≠ 0) (hB : 1 < B)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ Rld θ θ' → ‖locG F (ctr t) (3 / 2 - θ) w‖ ≤ B) :
    ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ Kld θ θ' * Real.log B := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  set r' : ℝ := (3 / 2 - θ') / ρ with hr'def
  have hr'0 : 0 < r' := div_pos (by linarith) hρ
  have hr'1 : r' < 1 := by rw [hr'def, div_lt_one hρ]; linarith
  set r : ℝ := r' + (1 - r') / 4 with hrdef
  set R' : ℝ := r' + (1 - r') / 2 with hR'def
  set R : ℝ := r' + 3 * (1 - r') / 4 with hRdef
  have hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ) := by
    rw [hr'def, div_mul_cancel₀ _ hρ.ne']; linarith
  have FB := disc_point_ball hFd (by linarith) hr'0 (by linarith : r' < r) (by linarith : r < 1)
    (by linarith : r < R') (by linarith : R' < R) (by linarith : R < 1) hz hσ32 hzf hB hfb
  rw [← hρdef] at FB
  have hKld : Kld θ θ' = (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) / ρ := rfl
  rw [hKld, div_mul_eq_mul_div, le_div_iff₀ hρ]
  linarith

/-- **The log-derivative at the radii of `Kld`** with no zero in `Re s > θ` (`logDeriv_le_Kld_ball`). -/
theorem logDeriv_le_Kld {F : ℂ → ℂ} {θ θ' σ t B : ℝ} (hθθ' : θ < θ') (hσ : θ' ≤ σ) (hσ32 : σ < 3 / 2)
    (hFd : DifferentiableOn ℂ F (Metric.ball (ctr t) (2 * (3 / 2 - θ))))
    (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0) (hB : 1 < B)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ Rld θ θ' → ‖locG F (ctr t) (3 / 2 - θ) w‖ ≤ B) :
    ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ Kld θ θ' * Real.log B :=
  logDeriv_le_Kld_ball hθθ' hσ hσ32 hFd (fun s hs => hzf s (re_gt_of_mem_ball hs)) hB hfb

/-- **The log-derivative of an entire function with no zero in one disc** (round 520). Let `F` be entire with
`|F(s)| ≤ c(|Im s| + 2)` on `θ ≤ Re s ≤ 3` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`, `0 < θ < θ' < 3/2`. At a `t` with
`1/|F(3/2 + it)| ≤ A` and no zero of `F` in the disc of radius `3/2 − θ` about `3/2 + it`,
`|F′/F(σ + it)| ≤ Kld θ θ'(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'`. -/
theorem logDeriv_le_ball {θ θ' : ℝ} (hθ0 : 0 < θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c A C₀ : ℝ} (hc0 : 0 ≤ c) (hA0 : 0 ≤ A)
    (hgrowth : ∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2))
    (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀)
    {σ t : ℝ} (hσ : θ' ≤ σ) (hlow : ‖F (ctr t)‖⁻¹ ≤ A)
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), F s ≠ 0) :
    ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
      Kld θ θ' * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) + C₀ := by
  have hK := Kld_pos hθθ' hθ'32
  have hR1 := Rld_lt_one hθθ' hθ'32
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  have hρ32 : ρ ≤ 3 / 2 := by linarith
  have hl4 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have h2cA : 0 ≤ 2 * c * A := by positivity
  have hl2 : 0 ≤ Real.log (2 + 2 * c * A) := Real.log_nonneg (by linarith)
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (hright (ctr t) (by rw [ctr_re]))
  by_cases h32 : 3 / 2 ≤ σ
  · have h := hright (σ + t * I) (by simpa using h32)
    have : 0 ≤ Kld θ θ' * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) :=
      mul_nonneg hK.le (add_nonneg hl2 hl4)
    linarith
  push Not at h32
  set B : ℝ := 2 + 2 * c * A * (|t| + 4) with hBdef
  have hB : 1 < B := by
    have : 0 ≤ 2 * c * A * (|t| + 4) := by positivity
    linarith
  have hfb : ∀ w : ℂ, ‖w‖ ≤ Rld θ θ' → ‖locG F (ctr t) ρ w‖ ≤ B := by
    intro w hw
    have hre : θ ≤ (ctr t + ρ * w).re := by
      rw [ctr_add_re]
      have := re_ge (x := 3 / 2) w hρ.le
      have : ρ * ‖w‖ ≤ ρ * Rld θ θ' := mul_le_mul_of_nonneg_left hw hρ.le
      have : ρ * Rld θ θ' < ρ := mul_lt_of_lt_one_right hρ hR1
      linarith
    have hre3 : (ctr t + ρ * w).re ≤ 3 := by
      rw [ctr_add_re]
      have h1 : w.re ≤ ‖w‖ := Complex.re_le_norm w
      have h2 : ρ * w.re ≤ ρ * 1 := mul_le_mul_of_nonneg_left (h1.trans (hw.trans hR1.le)) hρ.le
      linarith
    have him : |(ctr t + ρ * w).im| ≤ |t| + 2 := by
      rw [ctr_add_im]
      have h1 : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans (hw.trans hR1.le)
      have h2 : |ρ * w.im| ≤ 2 := by
        rw [abs_mul, abs_of_pos hρ]
        calc ρ * |w.im| ≤ (3 / 2) * 1 := mul_le_mul hρ32 h1 (abs_nonneg _) (by norm_num)
          _ ≤ 2 := by norm_num
      calc |t + ρ * w.im| ≤ |t| + |ρ * w.im| := abs_add_le _ _
        _ ≤ |t| + 2 := by linarith
    have hgr := hgrowth _ hre hre3
    unfold locG
    rw [norm_div, div_eq_mul_inv]
    calc ‖F (ctr t + ρ * w)‖ * ‖F (ctr t)‖⁻¹ ≤ (c * (|t| + 4)) * A := by
          apply mul_le_mul _ hlow (by positivity) (by positivity)
          exact hgr.trans (mul_le_mul_of_nonneg_left (by linarith) hc0)
      _ ≤ B := by
          have : 0 ≤ c * (|t| + 4) * A := by positivity
          rw [hBdef]; linarith
  have h := logDeriv_le_Kld_ball hθθ' hσ h32 hF.differentiableOn hzf hB hfb
  have hlogB : Real.log B ≤ Real.log (2 + 2 * c * A) + Real.log (|t| + 4) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by linarith)
    rw [hBdef]
    linarith [abs_nonneg t]
  have := mul_le_mul_of_nonneg_left hlogB hK.le
  linarith

/-- **The log-derivative of an entire function in a zero-free half-plane, with its constants.** Let `F`
be entire with no zero in `Re s > θ`, `0 < θ < θ' < 3/2`, with `|F(s)| ≤ c(|Im s| + 2)` on
`θ ≤ Re s ≤ 3`, `1/|F(3/2 + it)| ≤ A` for every `t`, and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`. Then
`|F′/F(σ + it)| ≤ K(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'` and every `t`, with `K = Kld θ θ'`
(`logDeriv_le_ball`). -/
theorem logDeriv_le_uniform_of {θ θ' : ℝ} (hθ0 : 0 < θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) :
    0 < Kld θ θ' ∧ ∀ {F : ℂ → ℂ}, Differentiable ℂ F → (∀ s : ℂ, θ < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ σ t : ℝ, θ' ≤ σ →
        ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
          Kld θ θ' * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) + C₀ :=
  ⟨Kld_pos hθθ' hθ'32, fun {_} hF hzf {_ _ _} hc0 hA0 hgrowth hlow hright _ t hσ =>
    logDeriv_le_ball hθ0 hθθ' hθ'32 hF hc0 hA0 hgrowth hright hσ (hlow t)
      (fun s hs => hzf s (re_gt_of_mem_ball hs))⟩

/-- **The log-derivative of an entire function in a zero-free half-plane, with its constants.** Let `F`
be entire with no zero in `Re s > θ`, `0 < θ < θ' < 3/2`, with `|F(s)| ≤ c(|Im s| + 2)` on
`θ ≤ Re s ≤ 3`, `1/|F(3/2 + it)| ≤ A` for every `t`, and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`. Then
`|F′/F(σ + it)| ≤ K(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'` and every `t`, with `K` depending on
`θ` and `θ'` only (`Kld θ θ'`, `logDeriv_le_uniform_of`). -/
theorem logDeriv_le_uniform {θ θ' : ℝ} (hθ0 : 0 < θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {F : ℂ → ℂ}, Differentiable ℂ F → (∀ s : ℂ, θ < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ σ t : ℝ, θ' ≤ σ →
        ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
          K * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) + C₀ :=
  ⟨Kld θ θ', (logDeriv_le_uniform_of hθ0 hθθ' hθ'32).1, (logDeriv_le_uniform_of hθ0 hθθ' hθ'32).2⟩

end LogDerivDisc

#print axioms LogDerivDisc.disc_point_ball
#print axioms LogDerivDisc.disc_point
#print axioms LogDerivDisc.logDeriv_le_Kld_ball
#print axioms LogDerivDisc.logDeriv_le_ball
#print axioms LogDerivDisc.logDeriv_le_Kld
#print axioms LogDerivDisc.logDeriv_le_uniform_of
#print axioms LogDerivDisc.logDeriv_le_uniform
