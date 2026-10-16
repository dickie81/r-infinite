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
  condition keeps the disc away from `1`. *(Round 513: proved from round 480's bound with its constants,
  `LogDerivDisc.logDeriv_le_uniform_of`, at `(θ + θ')/2`, with `F` bounded on the box `|Im s| ≤ 1`
  (`growth_of_ge_one`). `locG` and `disc_point` moved to `LogDerivDisc.lean`: STRUCTURAL-REVIEW §9.3, U3 and U4.)*
* `sum_isBigO_of_zeroFree`: for coefficients with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on
  `Re s > 1`, `Σ_{n ≤ x} f(n) = O(x^{θ+η})`. Round 472's Mertens argument
  (`MertensExponent.mertens_isBigO_of_zeroFree`) with `−F′/F` for `1/ζ`: the smoothed Perron integral
  moved to `Re s = θ' = θ + η₀/4` (`SmoothPerron.smoothedSum_eq_verticalIntegral_left`), where
  `|F′/F(θ' + it)| ≤ K(1 + |t|)^{η₀/8}` from the log-derivative bound (and compactness for `|t| ≤ 4`), and
  the unsmoothing at `B = log 3X` (`SmoothPerron.norm_smoothedSum_sub_le`), with `ε = X^{θ'−1}`. *(Round 513:
  proved from round 480's bound with its constants, `sum_le_uniform`, at `θ + η₁`, `η₁ = min(η, 1 − θ)/2`. The
  argument above is now that of `sum_le_uniform_of`, which moved here from `ChiUniform.lean` with `sum_le_uniform`,
  `eta0` and `integral_one_add_abs_rpow`: STRUCTURAL-REVIEW §9.3, U3.)*
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

open SmoothPerron LogDerivDisc

/-! ### The log-derivative of an entire function in a zero-free half-plane -/

/-- Linear growth `|F(s)| ≤ c_δ|Im s|` on `δ ≤ Re s ≤ 3`, `|Im s| ≥ 1`, for every `δ > 0`, gives
`|F(s)| ≤ c(|Im s| + 2)` on all of `θ ≤ Re s ≤ 3` for every `θ > 0`: a continuous `F` is bounded on the box
`θ ≤ Re s ≤ 3`, `|Im s| ≤ 1`. -/
lemma growth_of_ge_one {F : ℂ → ℂ} (hF : Continuous F)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖F s‖ ≤ c * |s.im|) {θ : ℝ} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2) := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := hgrowth θ hθ
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := θ) (b := 3)).reProdIm
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn hF.continuousOn
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨c₁ + max M 0, by positivity, fun s hs1 hs3 => ?_⟩
  have him : 0 ≤ |s.im| := abs_nonneg _
  by_cases h1 : 1 ≤ |s.im|
  · calc ‖F s‖ ≤ c₁ * |s.im| := hc₁ s hs1 hs3 h1
      _ ≤ (c₁ + max M 0) * (|s.im| + 2) := by nlinarith
  · push Not at h1
    have hmem : s ∈ Icc θ 3 ×ℂ Icc (-1) 1 :=
      Complex.mem_reProdIm.2 ⟨⟨hs1, hs3⟩, abs_le.1 h1.le⟩
    calc ‖F s‖ ≤ M := hM s hmem
      _ ≤ max M 0 := le_max_left _ _
      _ ≤ (c₁ + max M 0) * (|s.im| + 2) := by nlinarith

/-- **The log-derivative of an entire function in a zero-free half-plane.** Let `F` be entire with no
zero in `Re s > θ ≥ 0`, of at most linear growth `|F(s)| ≤ c_δ|Im s|` on `δ ≤ Re s ≤ 3`, `|Im s| ≥ 1`, for
every `δ > 0`, with `1/|F(3/2 + it)| ≤ A` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`. Then for every
`θ' ∈ (θ, 3/2)` there is `C` with `|F′/F(σ + it)| ≤ C log|t|` for `σ ≥ θ'`, `|t| > 3`.
(Round 513: `LogDerivDisc.logDeriv_le_uniform_of` at `(θ + θ')/2`.) -/
theorem logDeriv_le_of_zeroFree {F : ℂ → ℂ} (hF : Differentiable ℂ F) {θ θ' : ℝ} (hθ0 : 0 ≤ θ)
    (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖F s‖ ≤ c * |s.im|)
    {A : ℝ} (hlow : ∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A)
    {C₀ : ℝ} (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 < |t| → θ' ≤ σ →
      ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ C * Real.log |t| := by
  set θ₁ : ℝ := (θ + θ') / 2 with hθ₁def
  obtain ⟨c, hc0, hc⟩ := growth_of_ge_one hF.continuous hgrowth (by linarith : 0 < θ₁)
  have hA0 : 0 ≤ A := (inv_nonneg.2 (norm_nonneg _)).trans (hlow 0)
  obtain ⟨hK, hb⟩ := logDeriv_le_uniform_of (by linarith : 0 < θ₁) (by linarith : θ₁ < θ') hθ'32
  set K : ℝ := Kld θ₁ θ' with hKdef
  set L₀ : ℝ := Real.log (2 + 2 * c * A) with hL₀def
  have hL₀ : 0 ≤ L₀ := Real.log_nonneg (by nlinarith)
  refine ⟨K * L₀ + 2 * K + |C₀|, by positivity, fun σ t ht hσ => ?_⟩
  have hlt : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ht.le)
  have hl4 : Real.log (|t| + 4) ≤ 2 * Real.log |t| := by
    calc Real.log (|t| + 4) ≤ Real.log (|t| ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log |t| := by rw [Real.log_pow]; norm_num
  have h := hb hF (fun s hs => hzf s (by linarith)) hc0 hA0 hc hlow hright σ t hσ
  have h1 : L₀ ≤ L₀ * Real.log |t| := le_mul_of_one_le_right hL₀ hlt.le
  have h2 : C₀ ≤ |C₀| * Real.log |t| :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlt.le)
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 hl4) hK.le
  calc ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ K * (L₀ + Real.log (|t| + 4)) + C₀ := h
    _ ≤ (K * L₀ + 2 * K + |C₀|) * Real.log |t| := by nlinarith

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

/-- `∫_ℝ (1 + |t|)^{−r} dt = 2/(r − 1)` for `r > 1`. -/
lemma integral_one_add_abs_rpow {r : ℝ} (hr : 1 < r) :
    ∫ t : ℝ, (1 + |t|) ^ (-r) = 2 / (r - 1) := by
  rw [integral_comp_abs (f := fun t ↦ (1 + t) ^ (-r))]
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ ↦ (1 + t) ^ (1 - r) / (1 - r))
      ((1 + x) ^ (-r)) x := by
    intro x hx
    have hx1 : 0 < 1 + x := by linarith [mem_Ici.1 hx]
    have h := ((hasDerivAt_id x).const_add 1).rpow_const (p := 1 - r) (Or.inl hx1.ne')
    have h2 := h.div_const (1 - r)
    have e1 : (1 : ℝ) - r - 1 = -r := by ring
    simp only [id_eq, one_mul, e1] at h2
    convert h2 using 1
    have h1r : (1 : ℝ) - r ≠ 0 := by linarith
    field_simp
  have hint : IntegrableOn (fun t : ℝ ↦ (1 + t) ^ (-r)) (Ioi 0) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)).integrableOn
      (s := Ioi (0 : ℝ))
    refine h.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    simp only [Real.norm_eq_abs, abs_of_pos (mem_Ioi.1 ht)]
  have htend : Tendsto (fun t : ℝ ↦ (1 + t) ^ (1 - r) / (1 - r)) atTop (𝓝 (0 / (1 - r))) := by
    refine Tendsto.div_const ?_ _
    have h := tendsto_rpow_neg_atTop (y := r - 1) (by linarith)
    have h2 := h.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    refine h2.congr' (Eventually.of_forall fun t ↦ ?_)
    simp only [Function.comp, id]
    congr 1
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  simp only [add_zero, Real.one_rpow, zero_div, zero_sub]
  field_simp
  ring

/-- `η₀ = min(η, (1 − θ)/2)`, the exponent step of `sum_le_uniform`. -/
noncomputable def eta0 (θ η : ℝ) : ℝ := min η ((1 - θ) / 2)

/-- **Sums of the coefficients of `−F′/F`, with explicit constants.** `sum_le_uniform` for a given `C¹`
smoothing `ν` whose `Smooth1` has `|𝓜(Smooth1 ν ε)(θ′ + it)| ≤ K_M ε^{−κ}(1 + |t|)^{−1−κ}` on the line
`θ′ = θ + η₀/4`, `κ = η₀/4`, `η₀ = min(η, (1 − θ)/2)` (`eta0`). Then
`C₁ = K_M(16/η₀)(K + 1)` and `C₂ = K_M(16/η₀)K·4^{η₀/8}/(η₀/8) + 4(2 + 4/η₀)`, with `K = Kld θ θ′`. -/
theorem sum_le_uniform_of {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {η : ℝ} (hη : 0 < η)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (ν_supp : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {KM : ℝ} (hKM0 : 0 ≤ KM)
    (hKM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((θ + eta0 θ η / 4 : ℝ) + t * I)‖ ≤
        KM * ε ^ (-(eta0 θ η / 4)) * (1 + |t|) ^ (-(1 + eta0 θ η / 4))) :
    ∀ {F : ℂ → ℂ}, Differentiable ℂ F →
      (∀ s : ℂ, θ < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ {f : ℕ → ℂ}, f 0 = 0 → (∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n) →
      (∀ s : ℂ, 1 < s.re → LSeries f s = -(deriv F s / F s)) →
      ∀ X : ℝ, 1 < X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤
        (KM * (16 / eta0 θ η) * (Kld θ (θ + eta0 θ η / 4) + 1) *
            (Real.log (2 + 2 * c * A) + C₀) +
          (KM * (16 / eta0 θ η) *
              (Kld θ (θ + eta0 θ η / 4) * 4 ^ (eta0 θ η / 8) / (eta0 θ η / 8)) +
            4 * (2 + 4 / eta0 θ η))) * X ^ (θ + η) := by
  set η₀ : ℝ := eta0 θ η with hη₀def
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
  set K : ℝ := Kld θ θ' with hKdef
  obtain ⟨hK, hKb⟩ := logDeriv_le_uniform_of hθ0 hθθ' (by linarith)
  set r : ℝ := 1 + κ - ε₁ with hrdef
  have hr : 1 < r := by linarith
  have hIr : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-r) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)
    simpa only [Real.norm_eq_abs] using this
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIrdef
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t ↦ by positivity
  have hIreq : Ir = 16 / η₀ := by
    rw [hIrdef, integral_one_add_abs_rpow hr, hrdef, hκdef, hε₁def,
      show (1 : ℝ) + η₀ / 4 - η₀ / 8 - 1 = η₀ / 8 by ring, div_div_eq_mul_div]
    ring
  set D : ℝ := K * 4 ^ ε₁ / ε₁ with hDdef
  have hD : 0 ≤ D := by positivity
  have hκinv : 1 / κ = 4 / η₀ := by rw [hκdef]; field_simp
  rw [← hIreq, ← hκinv]
  intro F hF hzf c A C₀ hc0 hA0 hgrowth hlow hright f hf0 hfΛ hLS X hX
  have hb := fun σ t hσ ↦ hKb hF hzf hc0 hA0 hgrowth hlow hright σ t hσ
  set L₀ : ℝ := Real.log (2 + 2 * c * A) with hL₀def
  have hL₀ : 0 ≤ L₀ := Real.log_nonneg (by nlinarith)
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (hright (ctr 0) (by rw [ctr_re]))
  set G : ℂ → ℂ := fun s ↦ -(deriv F s / F s) with hGdef
  have hdF : ∀ s : ℂ, DifferentiableAt ℂ (deriv F) s := fun s ↦
    (hF.analyticAt s).deriv.differentiableAt
  have hGd : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s := fun s hs ↦
    ((hdF s).div (hF s) (hzf s hs)).neg
  have hGc : ∀ σ : ℝ, θ < σ → Continuous fun t : ℝ ↦ G (σ + t * I) := by
    intro σ hσ
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have h1 : ContinuousAt G (σ + t * I) := (hGd _ (by simpa using hσ)).continuousAt
    exact h1.comp (f := fun t : ℝ ↦ (σ : ℂ) + t * I) (by fun_prop)
  -- the log-derivative on horizontal segments
  have hgrowthG : ∀ σ t : ℝ, θ' ≤ σ → σ ≤ 2 → 4 ≤ |t| →
      ‖G (σ + t * I)‖ ≤ (K * L₀ + C₀ + 2 * K) * |t| := by
    intro σ t hσ _ ht
    rw [hGdef, norm_neg]
    have hlog : Real.log (|t| + 4) ≤ 2 * |t| := by
      have := Real.log_le_sub_one_of_pos (show 0 < |t| + 4 by linarith)
      linarith
    calc ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ K * (L₀ + Real.log (|t| + 4)) + C₀ := hb σ t hσ
      _ ≤ K * (L₀ * |t| + 2 * |t|) + C₀ * |t| := by
          have h1 : L₀ ≤ L₀ * |t| := le_mul_of_one_le_right hL₀ (by linarith)
          have h2 : C₀ ≤ C₀ * |t| := le_mul_of_one_le_right hC₀ (by linarith)
          have h3 := mul_le_mul_of_nonneg_left h1 hK.le
          have h4 := mul_le_mul_of_nonneg_left hlog hK.le
          linarith
      _ = (K * L₀ + C₀ + 2 * K) * |t| := by ring
  -- the line bound on `Re s = θ'`
  set K₁ : ℝ := K * L₀ + C₀ + D with hK₁def
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₁ : ∀ t : ℝ, ‖G (θ' + t * I)‖ ≤ K₁ * (1 + |t|) ^ ε₁ := by
    intro t
    have h1 : 1 ≤ (1 + |t|) ^ ε₁ := Real.one_le_rpow (by linarith [abs_nonneg t]) hε₁.le
    have hlog : Real.log (|t| + 4) ≤ 4 ^ ε₁ / ε₁ * (1 + |t|) ^ ε₁ := by
      have h := Real.log_le_rpow_div (x := |t| + 4) (by positivity) hε₁
      have h2 : (|t| + 4) ^ ε₁ ≤ (4 * (1 + |t|)) ^ ε₁ :=
        Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hε₁.le
      rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
      calc Real.log (|t| + 4) ≤ (|t| + 4) ^ ε₁ / ε₁ := h
        _ ≤ 4 ^ ε₁ * (1 + |t|) ^ ε₁ / ε₁ := by gcongr
        _ = 4 ^ ε₁ / ε₁ * (1 + |t|) ^ ε₁ := by ring
    rw [hGdef, norm_neg]
    calc ‖deriv F (θ' + t * I) / F (θ' + t * I)‖ ≤ K * (L₀ + Real.log (|t| + 4)) + C₀ := hb θ' t le_rfl
      _ ≤ K * (L₀ * (1 + |t|) ^ ε₁ + 4 ^ ε₁ / ε₁ * (1 + |t|) ^ ε₁) + C₀ * (1 + |t|) ^ ε₁ := by
          have h3 : L₀ ≤ L₀ * (1 + |t|) ^ ε₁ := le_mul_of_one_le_right hL₀ h1
          have h4 : C₀ ≤ C₀ * (1 + |t|) ^ ε₁ := le_mul_of_one_le_right hC₀ h1
          have h5 := mul_le_mul_of_nonneg_left h3 hK.le
          have h6 := mul_le_mul_of_nonneg_left hlog hK.le
          linarith
      _ = K₁ * (1 + |t|) ^ ε₁ := by rw [hK₁def, hDdef]; ring
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
  have hεκ : ε ^ (-κ) * X ^ θ' ≤ X ^ (θ' + κ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    have := mul_pos hκ0 hθ'0
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
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
    rw [this] at hX1
    have e : (2 + 1 / κ) * X ^ κ = 2 * X ^ κ + 1 / κ * X ^ κ := by ring
    rw [e]
    linarith
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n =
      smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) := by ring
  have hK₁le : K₁ ≤ (K + 1) * (L₀ + C₀) + D := by
    have := mul_nonneg hK.le hC₀
    rw [hK₁def]; linarith
  rw [hsplit]
  calc ‖smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n)‖
      ≤ ‖smoothedSum ν ε X f‖ + ‖smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ :=
        norm_sub_le _ _
    _ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + Real.log (3 * X) * (3 * Real.log 2 * ε * X + 1) :=
        add_le_add hsm hun
    _ ≤ K₁ * KM * Ir * X ^ (θ' + κ) + (2 + 1 / κ) * X ^ κ * (4 * X ^ θ') := by
        have h2 : 3 * Real.log 2 * ε * X + 1 ≤ 4 * X ^ θ' := by
          rw [mul_assoc (3 * Real.log 2), hεX]
          have := mul_le_mul_of_nonneg_right hlog2.le (by positivity : (0 : ℝ) ≤ X ^ θ')
          linarith
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hεκ (by positivity)
        · exact mul_le_mul hlogX h2 (by positivity) (by positivity)
    _ = (K₁ * KM * Ir + 4 * (2 + 1 / κ)) * X ^ (θ' + κ) := by
        rw [Real.rpow_add Xpos]; ring
    _ ≤ (K₁ * KM * Ir + 4 * (2 + 1 / κ)) * X ^ (θ + η) := by gcongr
    _ ≤ (KM * Ir * (K + 1) * (L₀ + C₀) + (KM * Ir * D + 4 * (2 + 1 / κ))) * X ^ (θ + η) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : K₁ * (KM * Ir) ≤ ((K + 1) * (L₀ + C₀) + D) * (KM * Ir) :=
          mul_le_mul_of_nonneg_right hK₁le (by positivity)
        linarith

/-- **Sums of the coefficients of `−F′/F`, with their constants.** For `0 < θ < 1` and `η > 0` there are
`C₁, C₂` such that for every `F` as in `logDeriv_le_uniform` and every `f` with `f(0) = 0`,
`|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on `Re s > 1`:
`|Σ_{n≤X} f(n)| ≤ (C₁(log(2 + 2cA) + C₀) + C₂)X^{θ+η}` for every `X > 1` (`sum_le_uniform_of`, with PNT+'s
`SmoothExistence`). -/
theorem sum_le_uniform {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {η : ℝ} (hη : 0 < η) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {F : ℂ → ℂ}, Differentiable ℂ F →
      (∀ s : ℂ, θ < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ {f : ℕ → ℂ}, f 0 = 0 → (∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n) →
      (∀ s : ℂ, 1 < s.re → LSeries f s = -(deriv F s / F s)) →
      ∀ X : ℝ, 1 < X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤
        (C₁ * (Real.log (2 + 2 * c * A) + C₀) + C₂) * X ^ (θ + η) := by
  have hη₀ : 0 < eta0 θ η := lt_min hη (by linarith)
  have hη₀1 : eta0 θ η ≤ (1 - θ) / 2 := min_le_right _ _
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν ν_supp (κ := eta0 θ η / 4) (by positivity)
    (by linarith) (σ := θ + eta0 θ η / 4) (by positivity) (by linarith)
  have hK := (logDeriv_le_uniform_of hθ0 (θ' := θ + eta0 θ η / 4) (by linarith) (by linarith)).1
  exact ⟨_, _, by positivity, by positivity,
    sum_le_uniform_of hθ0 hθ1 hη diffν νnonneg ν_supp mass_one hKM0 hKM⟩

/-- **Sums of the coefficients of `−F′/F` in a zero-free half-plane.** Let `F` be as in
`logDeriv_le_of_zeroFree` with `θ < 1`, and `f` with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on
`Re s > 1`. Then `Σ_{n ≤ x} f(n) = O(x^{θ+η})` for every `η > 0`. (Round 513: `sum_le_uniform` at `θ + η₁`,
`η₁ = min(η, 1 − θ)/2`.) -/
theorem sum_isBigO_of_zeroFree {F : ℂ → ℂ} (hF : Differentiable ℂ F) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hzf : ∀ s : ℂ, θ < s.re → F s ≠ 0)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖F s‖ ≤ c * |s.im|)
    {A : ℝ} (hlow : ∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A)
    {C₀ : ℝ} (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀)
    {f : ℕ → ℂ} (hf0 : f 0 = 0) (hfΛ : ∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hLS : ∀ s : ℂ, 1 < s.re → LSeries f s = -(deriv F s / F s)) {η : ℝ} (hη : 0 < η) :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop] fun x ↦ x ^ (θ + η) := by
  set η₁ : ℝ := min η (1 - θ) / 2 with hη₁def
  have hm : 0 < min η (1 - θ) := lt_min hη (by linarith)
  have hmη : min η (1 - θ) ≤ η := min_le_left _ _
  have hm1 : min η (1 - θ) ≤ 1 - θ := min_le_right _ _
  obtain ⟨c, hc0, hc⟩ := growth_of_ge_one hF.continuous hgrowth (by linarith : 0 < θ + η₁)
  have hA0 : 0 ≤ A := (inv_nonneg.2 (norm_nonneg _)).trans (hlow 0)
  obtain ⟨C₁, C₂, -, -, hb⟩ :=
    sum_le_uniform (θ := θ + η₁) (by linarith) (by linarith) (η := η - η₁) (by linarith)
  refine IsBigO.of_bound (C₁ * (Real.log (2 + 2 * c * A) + C₀) + C₂) ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  have h := hb hF (fun s hs => hzf s (by linarith)) hc0 hA0 hc hlow hright hf0 hfΛ hLS X hX
  rw [show θ + η₁ + (η - η₁) = θ + η by ring] at h
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]

/-! ### `ψ(x, χ)` for a real character -/

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
    exact norm_LSeries_le_of_le_re hμ (by rw [ctr_re])
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
