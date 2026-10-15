/-
# Round 480: bounds for the real Dirichlet L-functions, uniform in the modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `η > 0` there is `C` with `|ψ(x, χ)| ≤ C log(N + 2)·x^{11/12+η}` for every quadratic
Dirichlet character `χ ≠ 1` mod `N` and every `x > 1` (`psiChi_le_uniform`). No hypothesis.

* `logDeriv_le_uniform`: round 478's `ChiPNT.logDeriv_le_of_zeroFree` with its constants kept. For
  `0 < θ < θ' < 3/2` there is `K` such that every entire `F` with no zero in `Re s > θ`, `|F(s)| ≤ c(|Im s| + 2)`
  on `θ ≤ Re s ≤ 3`, `1/|F(3/2 + it)| ≤ A` for every `t` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2` has
  `|F′/F(σ + it)| ≤ K(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'` and every `t`.
* `sum_le_uniform`: round 478's `ChiPNT.sum_isBigO_of_zeroFree` with its constants kept. For `0 < θ < 1` and
  `η > 0` there are `C₁, C₂` such that, for every such `F` and every `f` with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and
  `L(f, s) = −F′/F(s)` on `Re s > 1`, `|Σ_{n ≤ X} f(n)| ≤ (C₁(log(2 + 2cA) + C₀) + C₂)X^{θ+η}` for `X > 1`.
* `psiChi_le_uniform`: `F = L(·, χ)`, with `c = 18(N + 1)/11` from round 224's `PsiOmega.norm_LFunction_le`,
  `A = ζ(3/2)` (`zeta32`) and `C₀ = −ζ′/ζ(3/2)` (`logDerivZeta32`), and round 477's half-plane `Re s > 11/12`.
-/
import ChiPNT

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform7) "𝓜" => mellin

namespace ChiUniform

open SmoothPerron HalfPlanePNT ChiPNT

/-! ### The log-derivative with its constants -/

/-- **The log-derivative of an entire function in a zero-free half-plane, with its constants.** Let `F`
be entire with no zero in `Re s > θ`, `0 < θ < θ' < 3/2`, with `|F(s)| ≤ c(|Im s| + 2)` on
`θ ≤ Re s ≤ 3`, `1/|F(3/2 + it)| ≤ A` for every `t`, and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`. Then
`|F′/F(σ + it)| ≤ K(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'` and every `t`, with `K` depending on
`θ` and `θ'` only. -/
theorem logDeriv_le_uniform {θ θ' : ℝ} (hθ0 : 0 < θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {F : ℂ → ℂ}, Differentiable ℂ F → (∀ s : ℂ, θ < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, θ ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ σ t : ℝ, θ' ≤ σ →
        ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
          K * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) + C₀ := by
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
  refine ⟨K / ρ, div_pos hK hρ, fun {F} hF hzf {c A C₀} hc0 hA0 hgrowth hlow hright σ t hσ ↦ ?_⟩
  have hl4 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have h2cA : 0 ≤ 2 * c * A := by positivity
  have hl2 : 0 ≤ Real.log (2 + 2 * c * A) := Real.log_nonneg (by linarith)
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (hright (ctr t) (by rw [ctr_re]))
  by_cases h32 : 3 / 2 ≤ σ
  · have h := hright (σ + t * I) (by simpa using h32)
    have : 0 ≤ K / ρ * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) :=
      mul_nonneg (div_pos hK hρ).le (add_nonneg hl2 hl4)
    linarith
  push Not at h32
  have hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ) := by
    rw [hr'def, div_mul_cancel₀ _ hρ.ne']; linarith
  set B : ℝ := 2 + 2 * c * A * (|t| + 4) with hBdef
  have hB : 1 < B := by
    have : 0 ≤ 2 * c * A * (|t| + 4) := by positivity
    linarith
  have hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG F (ctr t) ρ w‖ ≤ B := by
    intro w hw
    have hre : θ ≤ (ctr t + ρ * w).re := by
      rw [ctr_add_re]
      have := re_ge (x := 3 / 2) w hρ.le
      have : ρ * ‖w‖ ≤ ρ * R := mul_le_mul_of_nonneg_left hw hρ.le
      have : ρ * R < ρ := mul_lt_of_lt_one_right hρ hR1
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
          apply mul_le_mul _ (hlow t) (by positivity) (by positivity)
          exact hgr.trans (mul_le_mul_of_nonneg_left (by linarith) hc0)
      _ ≤ B := by
          have : 0 ≤ c * (|t| + 4) * A := by positivity
          rw [hBdef]; linarith
  have FB := disc_point hF (by linarith) hr'0 hr'r hr1 hrR' hR'R hR1 hz h32 hzf hB hfb
  rw [← hρdef, ← hKdef] at FB
  have hlogB : Real.log B ≤ Real.log (2 + 2 * c * A) + Real.log (|t| + 4) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by linarith)
    rw [hBdef]
    linarith [abs_nonneg t]
  have hmain : ρ * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤
      ρ * (K / ρ * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4))) := by
    calc ρ * ‖deriv F (σ + t * I) / F (σ + t * I)‖ ≤ K * Real.log B := FB
      _ ≤ K * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4)) := mul_le_mul_of_nonneg_left hlogB hK.le
      _ = ρ * (K / ρ * (Real.log (2 + 2 * c * A) + Real.log (|t| + 4))) := by field_simp
  have h1 := le_of_mul_le_mul_left hmain hρ
  linarith

/-! ### Sums of the coefficients of `−F′/F`, with their constants -/

/-- **Sums of the coefficients of `−F′/F`, with their constants.** For `0 < θ < 1` and `η > 0` there are
`C₁, C₂` such that for every `F` as in `logDeriv_le_uniform` and every `f` with `f(0) = 0`,
`|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on `Re s > 1`:
`|Σ_{n≤X} f(n)| ≤ (C₁(log(2 + 2cA) + C₀) + C₂)X^{θ+η}` for every `X > 1`. -/
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
  obtain ⟨K, hK, hKb⟩ := logDeriv_le_uniform hθ0 hθθ' (by linarith)
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
  set D : ℝ := K * 4 ^ ε₁ / ε₁ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨KM * Ir * (K + 1), KM * Ir * D + 4 * (2 + 1 / κ), by positivity, by positivity,
    fun {F} hF hzf {c A C₀} hc0 hA0 hgrowth hlow hright {f} hf0 hfΛ hLS X hX ↦ ?_⟩
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

/-! ### Real characters, uniformly in the modulus -/

/-- `ζ(3/2) = Σ_{n≥1} n^{−3/2}`, as the sum of the norms of the terms. -/
noncomputable def zeta32 : ℝ := ∑' n : ℕ, ‖LSeries.term (fun _ ↦ (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖

/-- `−ζ′/ζ(3/2) = Σ Λ(n)n^{−3/2}`, as the sum of the norms of the terms. -/
noncomputable def logDerivZeta32 : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖

/-- Termwise comparison of `Σ |f(n)|n^{−σ}`. -/
lemma tsum_norm_term_le {f g : ℕ → ℂ} (hfg : ∀ n, ‖f n‖ ≤ ‖g n‖) {σ : ℝ}
    (hg : LSeriesSummable g σ) :
    ∑' n, ‖LSeries.term f σ n‖ ≤ ∑' n, ‖LSeries.term g σ n‖ := by
  have hle : ∀ n, ‖LSeries.term f σ n‖ ≤ ‖LSeries.term g σ n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · gcongr
      exact hfg n
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg.norm) hg.norm

lemma summable_one_32 : LSeriesSummable (fun _ ↦ (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) := by
  have := (LSeriesSummable_one_iff (s := ((3 / 2 : ℝ) : ℂ))).2 (by norm_num)
  exact this

/-- **`ψ(x, χ)` uniformly in the modulus.** For every `η > 0` there is `C` with
`|ψ(x, χ)| ≤ C log(N + 2)·x^{11/12+η}` for every quadratic Dirichlet character `χ ≠ 1` mod `N` and
every `x > 1`. -/
theorem psiChi_le_uniform {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤ C * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := sum_le_uniform (θ := 11 / 12) (by norm_num) (by norm_num) hη
  have hA₀ : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hΛ₀ : 0 ≤ logDerivZeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  set c' : ℝ := Real.log (2 + 36 * zeta32 / 11) with hc'def
  have hc' : 0 ≤ c' := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 36 * zeta32 / 11 by positivity])
  refine ⟨C₁ * (1 + c' + logDerivZeta32) + C₂, by positivity, fun N _ χ hq hχ x hx ↦ ?_⟩
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have hzf : ∀ s : ℂ, 11 / 12 < s.re → DirichletCharacter.LFunction χ s ≠ 0 :=
    fun _ hs ↦ Eis.RealChar.LFunction_ne_zero_of_isQuadratic hq hs (Or.inl hχ)
  set c : ℝ := 18 * (N + 1) / 11 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hgrowth : ∀ s : ℂ, 11 / 12 ≤ s.re → s.re ≤ 3 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ c * (|s.im| + 2) := by
    intro s hs1 hs3
    have hre : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 3 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + |s.im| := by rw [abs_of_pos hre]; linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re :=
          PsiOmega.norm_LFunction_le hχ hq hre
      _ ≤ (N + 1) * (3 + |s.im|) / (11 / 12) := by
          gcongr
      _ ≤ c * (|s.im| + 2) := by
          rw [hcdef]
          have : 0 ≤ (N : ℝ) + 1 := by positivity
          have : 0 ≤ |s.im| := abs_nonneg _
          rw [div_le_iff₀ (by norm_num)]
          have := mul_nonneg (by positivity : (0 : ℝ) ≤ N + 1) (abs_nonneg s.im)
          linarith
  have hlow : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ctr t)‖⁻¹ ≤ zeta32 := by
    intro t
    have hs : 1 < (ctr t).re := by rw [ctr_re]; norm_num
    have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hm]
    have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
      DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))
    refine (norm_LSeries_le hμ t).trans (tsum_norm_term_le (fun n ↦ ?_) summable_one_32)
    rw [norm_mul, norm_one]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans ?_
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤ logDerivZeta32 := by
    intro s hs
    rw [← norm_neg, ← LSeries_twist_vonMangoldt_eq_LFunction χ (by linarith)]
    have hΛ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((3 / 2 : ℝ) : ℂ) :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num)
    refine (norm_LSeries_le_of_le_re hΛ hs).trans (tsum_norm_term_le (fun n ↦ ?_)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hfΛ : ∀ n : ℕ,
      ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one _ _)
  have hmain := hb hF hzf hc0 hA₀ hgrowth hlow hright (by simp) hfΛ
    (fun s hs ↦ LSeries_twist_vonMangoldt_eq_LFunction χ hs) x hx
  -- the constant
  have hN2 : (3 : ℝ) ≤ N + 2 := by
    have := NeZero.ne N
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    linarith
  have hlogN : 1 ≤ Real.log (N + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : Real.log (2 + 2 * c * zeta32) ≤ Real.log (N + 2) + c' := by
    rw [hc'def, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hcdef]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hxp : 0 ≤ x ^ (11 / 12 + η) := Real.rpow_nonneg (by linarith) _
  calc ‖psiChi χ x‖ ≤ (C₁ * (Real.log (2 + 2 * c * zeta32) + logDerivZeta32) + C₂) *
        x ^ (11 / 12 + η) := hmain
    _ ≤ (C₁ * (Real.log (N + 2) + c' + logDerivZeta32) + C₂) * x ^ (11 / 12 + η) := by
        gcongr
    _ ≤ ((C₁ * (1 + c' + logDerivZeta32) + C₂) * Real.log (N + 2)) * x ^ (11 / 12 + η) := by
        apply mul_le_mul_of_nonneg_right _ hxp
        have h1 : C₁ * c' ≤ C₁ * c' * Real.log (N + 2) := le_mul_of_one_le_right (by positivity) hlogN
        have h2 : C₁ * logDerivZeta32 ≤ C₁ * logDerivZeta32 * Real.log (N + 2) :=
          le_mul_of_one_le_right (by positivity) hlogN
        have h3 : C₂ ≤ C₂ * Real.log (N + 2) := le_mul_of_one_le_right hC₂ hlogN
        linarith
    _ = (C₁ * (1 + c' + logDerivZeta32) + C₂) * Real.log (N + 2) * x ^ (11 / 12 + η) := by ring

end ChiUniform
