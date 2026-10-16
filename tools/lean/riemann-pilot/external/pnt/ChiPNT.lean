/-
# Round 478: `ψ(x, χ) = O(x^{11/12+η})` for every real Dirichlet character `χ ≠ 1`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For a quadratic Dirichlet character `χ ≠ 1` with `L(s, χ) ≠ 0` on `Re s > θ` (`0 ≤ θ < 1`),
`ψ(x, χ) = Σ_{n ≤ x} χ(n)Λ(n) = O(x^{θ+η})` for every `η > 0` (`psiChi_isBigO_of_zeroFree`); with round 477's
half-plane, `ψ(x, χ) = O(x^{11/12+η})` with no hypothesis (`psiChi_isBigO_eleven_twelfths`). *(Round 509: both
hold for every Dirichlet character `χ ≠ 1`, with round 254's growth bound `PsiOmega.norm_LFunction_leC`, moved to
src/LFunctionGrowth.lean, and round 495's half-plane `Eis.LFunction_ne_zero_of_re_gt`.)*

* `logDeriv_le_of_zeroFree`: round 337's log-derivative bound (`HalfPlanePNT.logDeriv_le_of_zeroFree`) for an
  entire `F` in place of `ζ`. If `F` has no zero in `Re s > θ ≥ 0`, grows at most linearly on
  `δ ≤ Re s ≤ 3`, `|Im s| ≥ 1`, for every `δ > 0`, has `1/|F(3/2 + it)| ≤ A` and `|F′/F| ≤ C₀` on
  `Re s ≥ 3/2`, then `|F′/F(σ + it)| ≤ C log|t|` on `σ ≥ θ' > θ`, `|t| > 3`. The disc step (`disc_point`) is
  round 337's with `F(3/2 + it + ρw)/F(3/2 + it)` (`locG`) in PNT+'s `FinalBound`; with no pole, no
  condition keeps the disc away from `1`.
* `sum_isBigO_of_zeroFree`: for coefficients with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on
  `Re s > 1`, `Σ_{n ≤ x} f(n) = O(x^{θ+η})`. Round 472's Mertens argument
  (`MertensExponent.mertens_isBigO_of_zeroFree`) with `−F′/F` for `1/ζ`: the smoothed Perron integral
  moved to `Re s = θ' = θ + η₀/4` (`SmoothPerron.smoothedSum_eq_verticalIntegral_left`), where
  `|F′/F(θ' + it)| ≤ K(1 + |t|)^{η₀/8}` from the log-derivative bound (and compactness for `|t| ≤ 4`), and
  the unsmoothing at `B = log 3X` (`SmoothPerron.norm_smoothedSum_sub_le`), with `ε = X^{θ'−1}`.
* `psiChi_isBigO_of_zeroFree`: `F = L(·, χ)`, entire for `χ ≠ 1` (Mathlib's
  `DirichletCharacter.differentiable_LFunction`), with linear growth from round 224's
  `PsiOmega.norm_LFunction_le` (`|L(s, χ)| ≤ (N + 1)|s|/Re s`; since round 509, round 254's
  `PsiOmega.norm_LFunction_leC`, the same bound for every `χ ≠ 1`, which since round 511 replaces it),
  `1/|L(3/2 + it, χ)| = |L(χμ, 3/2 + it)|`
  (Mathlib's `DirichletCharacter.LSeries.mul_mu_eq_one`) and `|L′/L| = |L(χΛ, s)| ≤ Σ Λ(n)n^{−3/2}` on
  `Re s ≥ 3/2` (Mathlib's `DirichletCharacter.LSeries_twist_vonMangoldt_eq`).
-/
import SmoothPerron
import LFunctionGrowth
import DirichletCharHalfPlane

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform6) "𝓜" => mellin

namespace ChiPNT

open SmoothPerron HalfPlanePNT

/-! ### The log-derivative of an entire function in a zero-free half-plane -/

/-- `F(s₀ + ρw)/F(s₀)`. -/
noncomputable def locG (F : ℂ → ℂ) (s₀ : ℂ) (ρ : ℝ) (w : ℂ) : ℂ := F (s₀ + ρ * w) / F s₀

lemma differentiable_locG {F : ℂ → ℂ} (hF : Differentiable ℂ F) (s₀ : ℂ) (ρ : ℝ) :
    Differentiable ℂ (locG F s₀ ρ) := by
  intro w
  unfold locG
  have hlin : DifferentiableAt ℂ (fun w : ℂ => s₀ + ρ * w) w := by fun_prop
  exact ((hF _).comp w hlin).div_const _

lemma locG_logDeriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s₀ z : ℂ} {ρ : ℝ} (hF0 : F s₀ ≠ 0)
    (hFz : F (s₀ + ρ * z) ≠ 0) :
    deriv (locG F s₀ ρ) z / locG F s₀ ρ z = ρ * (deriv F (s₀ + ρ * z) / F (s₀ + ρ * z)) := by
  have h1 : HasDerivAt F (deriv F (s₀ + ρ * z)) (s₀ + ρ * z) := (hF _).hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => s₀ + ρ * w) (ρ : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (ρ : ℂ)).const_add s₀
  have h2 := (h1.comp z hlin).div_const (F s₀)
  have hderiv : deriv (locG F s₀ ρ) z = ρ * deriv F (s₀ + ρ * z) / F s₀ := by
    rw [show locG F s₀ ρ = fun w => (F ∘ fun w : ℂ => s₀ + ρ * w) w / F s₀ by
      funext w; simp [locG], h2.deriv]
    ring
  rw [hderiv]; simp only [locG]; field_simp

/-- **The disc step** for an entire `F` with no zero in `Re s > θ ≥ 0`: with `ρ = 3/2 − θ` and radii
`0 < r' < r < R' < R < 1`, at a point `σ + it` with `θ < σ < 3/2` and `3/2 − σ ≤ ρr'`, if
`|F(3/2 + it + ρw)/F(3/2 + it)| ≤ B` on `|w| ≤ R`, then `ρ|F′/F(σ + it)| ≤ K log B` with the constant `K`
of PNT+'s `FinalBound`. -/
lemma disc_point {F : ℂ → ℂ} (hF : Differentiable ℂ F) {θ σ t r' r R' R B : ℝ} (hθσ : θ < σ)
    (hr'0 : 0 < r') (hr'r : r' < r) (hr1 : r < 1) (hrR' : r < R') (hR'R : R' < R) (hR1 : R < 1)
    (hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ)) (hσ32 : σ < 3 / 2)
    (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0) (hB : 1 < B)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG F (ctr t) (3 / 2 - θ) w‖ ≤ B) :
    (3 / 2 - θ) * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  set f := locG F (ctr t) ρ with hfdef
  have hF0 : F (ctr t) ≠ 0 := hzf _ (by rw [ctr_re]; linarith)
  have hf0 : f 0 = 1 := by simp [hfdef, locG, hF0]
  have hfd := differentiable_locG hF (ctr t) ρ
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := fun w _ => hfd.analyticAt w
  have hfA2 : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 2) := fun w _ => hfd.analyticAt w
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
  have hFz : F (ctr t + ρ * z) ≠ 0 := by
    rw [hsz]; apply hzf; simp; linarith
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
    apply hzf _ _ hzero
    rw [ctr_add_re]
    have h1 := re_ge (x := 3 / 2) q hρ.le
    have h2 : ρ * ‖q‖ ≤ ρ * r := mul_le_mul_of_nonneg_left hq.1 hρ.le
    have h3 : ρ * r < ρ := mul_lt_of_lt_one_right hρ hr1
    linarith
  rw [hsum, sub_zero, locG_logDeriv hF hF0 hFz, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, hsz] at FB
  exact FB

/-- **The log-derivative of an entire function in a zero-free half-plane.** Let `F` be entire with no
zero in `Re s > θ ≥ 0`, of at most linear growth `|F(s)| ≤ c_δ|Im s|` on `δ ≤ Re s ≤ 3`, `|Im s| ≥ 1`, for
every `δ > 0`, with `1/|F(3/2 + it)| ≤ A` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`. Then for every
`θ' ∈ (θ, 3/2)` there is `C` with `|F′/F(σ + it)| ≤ C log|t|` for `σ ≥ θ'`, `|t| > 3`. -/
theorem logDeriv_le_of_zeroFree {F : ℂ → ℂ} (hF : Differentiable ℂ F) {θ θ' : ℝ} (hθ0 : 0 ≤ θ)
    (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖F s‖ ≤ c * |s.im|)
    {A : ℝ} (hlow : ∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A)
    {C₀ : ℝ} (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 < |t| → θ' ≤ σ →
      ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ C * Real.log |t| := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  have hρ32 : ρ ≤ 3 / 2 := by linarith
  set r' : ℝ := (3 / 2 - θ') / ρ with hr'def
  have hr'0 : 0 < r' := div_pos (by linarith) hρ
  have hr'1 : r' < 1 := by rw [hr'def, div_lt_one hρ]; linarith
  set r : ℝ := r' + (1 - r') / 4 with hrdef
  set R' : ℝ := r' + (1 - r') / 2 with hR'def
  set R : ℝ := r' + 3 * (1 - r') / 4 with hRdef
  have hr'r : r' < r := by linarith
  have hr1 : r < 1 := by linarith
  have hrR' : r < R' := by linarith
  have hR'R : R' < R := by linarith
  have hR1 : R < 1 := by linarith
  have hR'0 : 0 < R' := by linarith
  set K : ℝ := 16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) with hKdef
  have hK : 0 < K := by
    have h1 : 0 < R ^ 2 / R' - R' := by
      rw [sub_pos, lt_div_iff₀ hR'0]; nlinarith
    have h2 : 0 < Real.log (R / R') := Real.log_pos (by rw [one_lt_div hR'0]; exact hR'R)
    have h3 : 0 < 16 * r ^ 2 / (r - r') ^ 3 := by
      have : 0 < r - r' := by linarith
      positivity
    have h4 : 0 < 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) := by positivity
    linarith
  have hδ : 0 < 3 / 2 - ρ * R := by
    have : ρ * R < ρ := mul_lt_of_lt_one_right hρ hR1
    linarith
  obtain ⟨c, hc0, hc⟩ := hgrowth _ hδ
  have hA0 : 0 ≤ A := (inv_nonneg.2 (norm_nonneg _)).trans (hlow 0)
  set c' : ℝ := c * A with hc'def
  have hc' : 0 ≤ c' := mul_nonneg hc0 hA0
  set L : ℝ := Real.log (2 * (1 + c')) + 1 with hLdef
  have hL : 0 < L := by
    have : 0 ≤ Real.log (2 * (1 + c')) := Real.log_nonneg (by linarith)
    linarith
  refine ⟨max |C₀| (K / ρ * L) + 1, by positivity, fun σ t ht hσ => ?_⟩
  have hlt : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ht.le)
  by_cases h32 : 3 / 2 ≤ σ
  · have h := hright (σ + t * I) (by simpa using h32)
    calc ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ |C₀| := h.trans (le_abs_self _)
      _ ≤ |C₀| * Real.log |t| := le_mul_of_one_le_right (abs_nonneg _) hlt.le
      _ ≤ (max |C₀| (K / ρ * L) + 1) * Real.log |t| := by
          gcongr
          have := le_max_left |C₀| (K / ρ * L); linarith
  push Not at h32
  have hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ) := by
    rw [hr'def, div_mul_cancel₀ _ hρ.ne']; linarith
  set B : ℝ := 2 + c' * (|t| + ρ) with hBdef
  have hB : 1 < B := by
    have : 0 ≤ c' * (|t| + ρ) := mul_nonneg hc' (by positivity)
    linarith
  have hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG F (ctr t) ρ w‖ ≤ B := by
    intro w hw
    have hre : 3 / 2 - ρ * R ≤ (ctr t + ρ * w).re := by
      rw [ctr_add_re]
      have := re_ge (x := 3 / 2) w hρ.le
      have : ρ * ‖w‖ ≤ ρ * R := mul_le_mul_of_nonneg_left hw hρ.le
      linarith
    have hre3 : (ctr t + ρ * w).re ≤ 3 := by
      rw [ctr_add_re]
      have h1 : w.re ≤ ‖w‖ := Complex.re_le_norm w
      have h2 : ρ * w.re ≤ ρ * 1 := mul_le_mul_of_nonneg_left (h1.trans (hw.trans hR1.le)) hρ.le
      linarith
    obtain ⟨him1, himle⟩ := im_bounds ht hρ hρ32 (hw.trans hR1.le)
    rw [← ctr_add_im] at him1 himle
    have hgr := hc _ hre hre3 him1
    unfold locG
    rw [norm_div, div_eq_mul_inv]
    calc ‖F (ctr t + ρ * w)‖ * ‖F (ctr t)‖⁻¹ ≤ (c * (|t| + ρ)) * A := by
          apply mul_le_mul _ (hlow t) (by positivity) (by positivity)
          exact hgr.trans (mul_le_mul_of_nonneg_left himle hc0)
      _ = c' * (|t| + ρ) := by rw [hc'def]; ring
      _ ≤ B := by rw [hBdef]; linarith
  have FB := disc_point hF (by linarith) hr'0 hr'r hr1 hrR' hR'R hR1 hz h32 hzf hB hfb
  rw [← hρdef, ← hKdef] at FB
  have hlogB : Real.log B ≤ L * Real.log |t| := by
    have hB2 : B ≤ 2 * (1 + c') * |t| := by
      have : c' * (|t| + ρ) ≤ c' * (|t| + 2) := mul_le_mul_of_nonneg_left (by linarith) hc'
      have : c' * (|t| + 2) ≤ c' * (2 * |t|) := mul_le_mul_of_nonneg_left (by linarith) hc'
      have : 2 ≤ 2 * |t| := by linarith
      rw [hBdef]; linarith
    have hl0 : 0 ≤ Real.log (2 * (1 + c')) := Real.log_nonneg (by linarith)
    calc Real.log B ≤ Real.log (2 * (1 + c') * |t|) := Real.log_le_log (by linarith) hB2
      _ = Real.log (2 * (1 + c')) + Real.log |t| := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ Real.log (2 * (1 + c')) * Real.log |t| + Real.log |t| := by
          have := mul_le_mul_of_nonneg_left hlt.le hl0; linarith
      _ = L * Real.log |t| := by simp only [hLdef]; ring
  have hmain : ρ * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ ρ * (K / ρ * L * Real.log |t|) := by
    calc ρ * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ K * Real.log B := FB
      _ ≤ K * (L * Real.log |t|) := mul_le_mul_of_nonneg_left hlogB hK.le
      _ = ρ * (K / ρ * L * Real.log |t|) := by field_simp
  have h1 := le_of_mul_le_mul_left hmain hρ
  calc ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ K / ρ * L * Real.log |t| := h1
    _ ≤ (max |C₀| (K / ρ * L) + 1) * Real.log |t| := by
        gcongr
        have := le_max_right |C₀| (K / ρ * L); linarith

/-! ### Sums of the coefficients of `−F′/F` -/

/-- `L(f, s)` converges absolutely on `Re s > 1` when `|f(n)| ≤ Λ(n)`. -/
lemma LSeriesSummable_of_le_vonMangoldt {f : ℕ → ℂ}
    (hfΛ : ∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm_bounded hΛ.norm fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · exact le_rfl
  · gcongr
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact hfΛ n

/-- **Sums of the coefficients of `−F′/F` in a zero-free half-plane.** Let `F` be as in
`logDeriv_le_of_zeroFree` with `θ < 1`, and `f` with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on
`Re s > 1`. Then `Σ_{n ≤ x} f(n) = O(x^{θ+η})` for every `η > 0`. -/
theorem sum_isBigO_of_zeroFree {F : ℂ → ℂ} (hF : Differentiable ℂ F) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖F s‖ ≤ c * |s.im|)
    {A : ℝ} (hlow : ∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A)
    {C₀ : ℝ} (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀)
    {f : ℕ → ℂ} (hf0 : f 0 = 0) (hfΛ : ∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hLS : ∀ s : ℂ, 1 < s.re → LSeries f s = -(deriv F s / F s)) {η : ℝ} (hη : 0 < η) :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop] fun x ↦ x ^ (θ + η) := by
  set η₀ : ℝ := min η ((1 - θ) / 2) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by linarith)
  have hη₀η : η₀ ≤ η := min_le_left _ _
  have hη₀1 : η₀ ≤ (1 - θ) / 2 := min_le_right _ _
  set θ' : ℝ := θ + η₀ / 4 with hθ'def
  set κ : ℝ := η₀ / 4 with hκdef
  set ε₁ : ℝ := η₀ / 8 with hε₁def
  have hθθ' : θ < θ' := by linarith
  have hθ'1 : θ' < 1 := by linarith
  have hθ'0 : 0 < θ' := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hε₁ : 0 < ε₁ := by linarith
  set G : ℂ → ℂ := fun s ↦ -(deriv F s / F s) with hGdef
  obtain ⟨C, hC0, hC⟩ := logDeriv_le_of_zeroFree hF hθ0 hθθ' (by linarith) hzf hgrowth hlow hright
  have hdF : ∀ s : ℂ, DifferentiableAt ℂ (deriv F) s := fun s ↦
    (hF.analyticAt s).deriv.differentiableAt
  have hGd : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s := fun s hs ↦
    ((hdF s).div (hF s) (hzf s hs)).neg
  have hGc : ∀ σ : ℝ, θ < σ → Continuous fun t : ℝ ↦ G (σ + t * I) := by
    intro σ hσ
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have h1 : ContinuousAt G (σ + t * I) := (hGd _ (by simpa using hσ)).continuousAt
    exact h1.comp (f := fun t : ℝ ↦ (σ : ℂ) + t * I) (by fun_prop)
  -- `|G| ≤ C log|t| ≤ C|t|` on horizontal segments
  have hgrowthG : ∀ σ t : ℝ, θ' ≤ σ → σ ≤ 2 → 4 ≤ |t| → ‖G (σ + t * I)‖ ≤ C * |t| := by
    intro σ t hσ _ ht
    rw [hGdef, norm_neg]
    calc ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ C * Real.log |t| := hC σ t (by linarith) hσ
      _ ≤ C * |t| := by
          gcongr
          exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  -- the line bound on `Re s = θ'`
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    (hGc θ' hθθ').continuousOn
  set K₁ : ℝ := max C₁ 0 + C / ε₁ with hK₁def
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₁ : ∀ t : ℝ, ‖G (θ' + t * I)‖ ≤ K₁ * (1 + |t|) ^ ε₁ := by
    intro t
    have h1 : 1 ≤ (1 + |t|) ^ ε₁ := Real.one_le_rpow (by linarith [abs_nonneg t]) hε₁.le
    by_cases ht : |t| ≤ 4
    · have hmem : t ∈ Icc (-4 : ℝ) 4 := by
        rw [mem_Icc]; constructor <;> linarith [abs_le.1 ht]
      calc ‖G (θ' + t * I)‖ ≤ C₁ := hC₁ t hmem
        _ ≤ max C₁ 0 := le_max_left _ _
        _ ≤ max C₁ 0 * (1 + |t|) ^ ε₁ := le_mul_of_one_le_right (le_max_right _ _) h1
        _ ≤ K₁ * (1 + |t|) ^ ε₁ := by
            gcongr
            rw [hK₁def]; have : 0 ≤ C / ε₁ := by positivity
            linarith
    · rw [not_le] at ht
      rw [hGdef, norm_neg]
      have hlog := Real.log_le_rpow_div (x := |t|) (abs_nonneg t) hε₁
      calc ‖deriv F (θ' + t * I) / F (θ' + t * I)‖ ≤ C * Real.log |t| := hC θ' t (by linarith) le_rfl
        _ ≤ C * (|t| ^ ε₁ / ε₁) := by gcongr
        _ = C / ε₁ * |t| ^ ε₁ := by ring
        _ ≤ C / ε₁ * (1 + |t|) ^ ε₁ := by
            gcongr
            linarith
        _ ≤ K₁ * (1 + |t|) ^ ε₁ := by
            gcongr
            rw [hK₁def]; linarith [le_max_right C₁ 0]
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν ν_supp hκ0.le hκ1 hθ'0 hθ'1.le
  set r : ℝ := 1 + κ - ε₁ with hrdef
  have hr : 1 < r := by linarith
  have hIr : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-r) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)
    simpa only [Real.norm_eq_abs] using this
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIrdef
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t ↦ by positivity
  refine IsBigO.of_bound (K₁ * KM * Ir + 4 * (2 + 1 / κ)) ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  have Xpos : 0 < X := by linarith
  set ε : ℝ := X ^ (θ' - 1) with hεdef
  have εpos : 0 < ε := Real.rpow_pos_of_pos Xpos _
  have ε_lt_one : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg hX (by linarith)
  have hpt : ∀ t : ℝ, ‖integrand ν ε X G (θ' + t * I)‖ ≤
      K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) := by
    intro t
    rw [norm_integrand Xpos]
    have hre : ((θ' : ℂ) + t * I).re = θ' := by simp
    rw [hre]
    have h1 := hK₁ t
    have h2 := hKM ε εpos ε_lt_one t
    have hpow : (1 + |t|) ^ ε₁ * (1 + |t|) ^ (-(1 + κ)) = (1 + |t|) ^ (-r) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      rw [hrdef]
      ring
    calc ‖G (θ' + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (θ' + t * I)‖ * X ^ θ'
        ≤ (K₁ * (1 + |t|) ^ ε₁) * (KM * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ))) * X ^ θ' := by
          gcongr
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * ((1 + |t|) ^ ε₁ * (1 + |t|) ^ (-(1 + κ))) := by ring
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) := by rw [hpow]
  have hint' : Integrable fun t : ℝ ↦ integrand ν ε X G (θ' + t * I) :=
    Integrable.mono' (hIr.const_mul (K₁ * KM * ε ^ (-κ) * X ^ θ'))
      (continuous_integrand_line hθ'0 (hGc θ' hθθ') diffν νnonneg ν_supp mass_one εpos ε_lt_one
        Xpos).aestronglyMeasurable (Eventually.of_forall hpt)
  have hid := smoothedSum_eq_verticalIntegral_left (f := f) hf0
    (LSeriesSummable_of_le_vonMangoldt hfΛ (by norm_num)) hLS hθ'0 (by linarith)
    (fun s hs ↦ hGd s (by linarith)) hgrowthG diffν νnonneg ν_supp mass_one εpos ε_lt_one hX.le hint'
  have hsm : ‖smoothedSum ν ε X f‖ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by
    rw [hid]
    calc _ ≤ ∫ t, K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) :=
          norm_verticalIntegral'_le (hIr.const_mul _) hpt
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * Ir := integral_const_mul _ _
      _ = K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by ring
  have hlog3X : 0 ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hB : ∀ n : ℕ, (n : ℝ) ≤ 3 * X → ‖f n‖ ≤ Real.log (3 * X) := by
    intro n hn
    refine (hfΛ n).trans (ArithmeticFunction.vonMangoldt_le_log.trans ?_)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h, hlog3X]
    · exact Real.log_le_log (by exact_mod_cast h) hn
  have hun := norm_smoothedSum_sub_le hf0 Xpos hB νnonneg ν_supp mass_one εpos ε_lt_one
  -- exponents
  have hεκ : ε ^ (-κ) * X ^ θ' ≤ X ^ (θ' + κ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by nlinarith)
  have hεX : ε * X = X ^ θ' := by
    rw [hεdef, ← Real.rpow_add_one Xpos.ne', sub_add_cancel]
  have h1θ' : 1 ≤ X ^ θ' := Real.one_le_rpow hX.le hθ'0.le
  have hfin : X ^ (θ' + κ) ≤ X ^ (θ + η) := Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlogX : Real.log (3 * X) ≤ (2 + 1 / κ) * X ^ κ := by
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    have hX1 := Real.log_le_rpow_div (x := X) Xpos.le hκ0
    have hXκ : 1 ≤ X ^ κ := Real.one_le_rpow hX.le hκ0.le
    rw [Real.log_mul (by norm_num) Xpos.ne']
    have : X ^ κ / κ = 1 / κ * X ^ κ := by ring
    nlinarith
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n =
      smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) := by ring
  rw [Real.norm_of_nonneg (Real.rpow_nonneg Xpos.le (θ + η)), hsplit]
  calc ‖smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n)‖
      ≤ ‖smoothedSum ν ε X f‖ + ‖smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ :=
        norm_sub_le _ _
    _ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + Real.log (3 * X) * (3 * Real.log 2 * ε * X + 1) :=
        add_le_add hsm hun
    _ ≤ K₁ * KM * Ir * X ^ (θ' + κ) + (2 + 1 / κ) * X ^ κ * (4 * X ^ θ') := by
        have h2 : 3 * Real.log 2 * ε * X + 1 ≤ 4 * X ^ θ' := by
          rw [mul_assoc (3 * Real.log 2), hεX]
          nlinarith
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hεκ (by positivity)
        · exact mul_le_mul hlogX h2 (by positivity) (by positivity)
    _ = K₁ * KM * Ir * X ^ (θ' + κ) + 4 * (2 + 1 / κ) * X ^ (θ' + κ) := by
        rw [Real.rpow_add Xpos]; ring
    _ = (K₁ * KM * Ir + 4 * (2 + 1 / κ)) * X ^ (θ' + κ) := by ring
    _ ≤ (K₁ * KM * Ir + 4 * (2 + 1 / κ)) * X ^ (θ + η) := by gcongr

/-! ### `ψ(x, χ)` for a real character -/

/-- `|L(f, s)| ≤ Σ |f(n)| n^{−σ₀}` on `Re s ≥ σ₀`. -/
lemma norm_LSeries_le_of_le_re {f : ℕ → ℂ} {σ₀ : ℝ} (hf : LSeriesSummable f σ₀) {s : ℂ}
    (hs : σ₀ ≤ s.re) : ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f σ₀ n‖ := by
  have hle : (σ₀ : ℂ).re ≤ s.re := by simpa using hs
  have hsum := (hf.of_re_le_re hle).norm
  calc ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, ‖LSeries.term f σ₀ n‖ :=
        Summable.tsum_le_tsum (fun n ↦ LSeries.norm_term_le_of_re_le_re f hle n) hsum hf.norm

/-- `ψ(x, χ) = Σ_{n ≤ x} χ(n)Λ(n)`. -/
noncomputable def psiChi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `L(χΛ, s) = −L′/L(s, χ)` on `Re s > 1`, with Mathlib's `LFunction`. -/
lemma LSeries_twist_vonMangoldt_eq_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs, ← neg_div]
  exact h

/-- **`ψ(x, χ)` in a zero-free half-plane**: for a Dirichlet character `χ ≠ 1` with
`L(s, χ) ≠ 0` on `Re s > θ` (`0 ≤ θ < 1`), `ψ(x, χ) = O(x^{θ+η})` for every `η > 0`. -/
theorem psiChi_isBigO_of_zeroFree (hχ : χ ≠ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hzf : ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0) {η : ℝ}
    (hη : 0 < η) : psiChi χ =O[atTop] fun x ↦ x ^ (θ + η) := by
  have hF := DirichletCharacter.differentiable_LFunction hχ
  -- linear growth
  have hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖DirichletCharacter.LFunction χ s‖ ≤ c * |s.im| := by
    intro δ hδ
    refine ⟨(N + 1) * 4 / δ, by positivity, fun s hs1 hs3 him ↦ ?_⟩
    have hre : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 4 * |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + |s.im| := by rw [abs_of_pos hre]; linarith
        _ ≤ 4 * |s.im| := by linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re :=
          PsiOmega.norm_LFunction_leC hχ hre
      _ ≤ (N + 1) * (4 * |s.im|) / δ := by
          gcongr
      _ = (N + 1) * 4 / δ * |s.im| := by ring
  -- the lower bound at `3/2 + it`
  have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))
  have hlow : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ctr t)‖⁻¹ ≤
      ∑' n, ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) (3 / 2 : ℝ) n‖ := by
    intro t
    have hs : 1 < (ctr t).re := by rw [ctr_re]; norm_num
    have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hne : LSeries (fun n ↦ χ n) (ctr t) ≠ 0 := fun h ↦ by simp [h] at hm
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hm]
    exact norm_LSeries_le hμ t
  -- the log-derivative right of `3/2`
  have hΛ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  have hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤
      ∑' n, ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℝ) n‖ := by
    intro s hs
    rw [← norm_neg, ← LSeries_twist_vonMangoldt_eq_LFunction χ (by linarith)]
    exact norm_LSeries_le_of_le_re hΛ hs
  have hfΛ : ∀ n : ℕ,
      ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one _ _)
  exact sum_isBigO_of_zeroFree hF hθ0 hθ1 hzf hgrowth hlow hright (by simp) hfΛ
    (fun s hs ↦ LSeries_twist_vonMangoldt_eq_LFunction χ hs) hη

/-- **`ψ(x, χ) = O(x^{11/12+η})`** for every Dirichlet character `χ ≠ 1` and every `η > 0`,
from round 495's half-plane. -/
theorem psiChi_isBigO_eleven_twelfths (hχ : χ ≠ 1) {η : ℝ} (hη : 0 < η) :
    psiChi χ =O[atTop] fun x ↦ x ^ (11 / 12 + η) :=
  psiChi_isBigO_of_zeroFree hχ (by norm_num) (by norm_num)
    (fun _ hs ↦ Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)) hη

end ChiPNT
