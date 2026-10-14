/-
# Round 472: a smoothed Perron formula for a general Dirichlet series

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For a Dirichlet series `L(f, s) = Σ f(n) n^{−s}` absolutely convergent at some `σ ∈ (1, 2]`,
PNT+'s smoothing `Smooth1 ν ε` gives `Σ_n f(n) Smooth1(n/X) = (1/2πi) ∫_{(σ)} L(f, s) 𝓜(Smooth1)(s) X^s ds`
(`verticalIntegral_eq_smoothedSum`); the line may be moved left across a strip where the integrand is
holomorphic and decays on horizontal segments (`verticalIntegral_shift`), in particular to any `Re s = σ' > 0`
left of which `L(f, ·)` continues holomorphically with at most linear growth
(`smoothedSum_eq_verticalIntegral_left`); and the smoothing costs `B(3 log 2 · εX + 1)` when `|f(n)| ≤ B` for
`n ≤ 3X` (`norm_smoothedSum_sub_le`).

* `verticalIntegral_eq_smoothedSum`: PNT+'s `SmoothedChebyshevDirichlet` with `Λ` replaced by any `f` with
  `f(0) = 0` and `L(f, σ)` absolutely convergent; the sum and the integral are exchanged by
  `integral_tsum_of_summable_integral_norm`, and each term is Mathlib's Mellin inversion at `n/X`.
* `verticalIntegral_shift`: PNT+'s `DiffVertRect_eq_UpperLowerUs` with the rectangle integral zero
  (`HolomorphicOn.vanishesOnRectangle`); the tails of both vertical integrals tend to `0` by
  `tendsto_setIntegral_of_antitone`, and the horizontal segments by the decay hypothesis.
* `norm_smoothedSum_sub_le`: `Smooth1(x) = 1` for `x ≤ 1 − (log 2)ε` and `= 0` for `x ≥ 1 + (2 log 2)ε`
  (PNT+'s `Smooth1Properties_below`, `Smooth1Properties_above`), so only `n` in a window of length
  `3(log 2)εX` contribute, each at most `B`.
* `mellin_le_geom`: on `Re s = σ ∈ (0, 1]`, `|𝓜(Smooth1)(s)| ≤ K ε^{−κ} (1 + |t|)^{−1−κ}` for `κ ∈ [0, 1]`,
  from the geometric mean `B^{1−κ}C^κ ε^{−κ} |s|^{−1−κ}` of round 338's `B/|s|` (`MediumPNTW.MellinOfSmooth1d`)
  and PNT+'s `C/(ε|s|²)` (`MellinOfSmooth1b`).
-/
import HalfPlaneLindelof

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory

local notation (name := mellintransform3) "𝓜" => mellin

namespace SmoothPerron

/-- The smoothed sum `Σ_n f(n) Smooth1(n/X)`. -/
noncomputable def smoothedSum (ν : ℝ → ℝ) (ε X : ℝ) (f : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ, f n * (Smooth1 ν ε (n / X) : ℂ)

/-- The Perron integrand `L(s) 𝓜(Smooth1)(s) X^s`. -/
noncomputable def integrand (ν : ℝ → ℝ) (ε X : ℝ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  L s * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

variable {ν : ℝ → ℝ}

/-- `𝓜(Smooth1)` is continuous on a vertical line `Re s = σ > 0`. -/
lemma continuous_mellin_line (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) := by
  rw [← continuousOn_univ]
  refine ContinuousOn.comp' (t := {z : ℂ | 0 < z.re}) ?_ (by fun_prop) ?_
  · refine continuousOn_of_forall_continuousAt fun z hz ↦ ?_
    exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one hz).continuousAt
  · intro t _
    simp [hσ]

/-- `f(n) n^{−s} m X^s = f(n) ((n/X)^{−s} m)` for `n ≥ 1`, `X > 0`. -/
lemma div_cpow_mul_cpow {n : ℕ} (hn : n ≠ 0) {X : ℝ} (Xpos : 0 < X) (a m s : ℂ) :
    a / (n : ℂ) ^ s * m * (X : ℂ) ^ s = a * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-s) • m) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 Xpos.ne'
  have hns : (n : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn' h.1
  have hXs : (X : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hX' h.1
  have key : (((n : ℝ) / X : ℝ) : ℂ) ^ s * (X : ℂ) ^ s = (n : ℂ) ^ s := by
    rw [← mul_cpow_ofReal_nonneg (div_nonneg (Nat.cast_nonneg n) Xpos.le) Xpos.le]
    congr 1
    push_cast
    field_simp
  rw [smul_eq_mul, cpow_neg, eq_div_of_mul_eq hXs key, inv_div]
  field_simp

/-- **The smoothed Perron formula.** For `1 < σ ≤ 2`, `f(0) = 0` and `L(f, σ)` absolutely convergent,
`(1/2πi) ∫_{(σ)} L(f, s) 𝓜(Smooth1)(s) X^s ds = Σ_n f(n) Smooth1(n/X)`. -/
theorem verticalIntegral_eq_smoothedSum {f : ℕ → ℂ} (hf0 : f 0 = 0) (diffν : ContDiff ℝ 1 ν)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (Xpos : 0 < X) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) (hf : LSeriesSummable f σ) :
    VerticalIntegral' (integrand ν ε X (LSeries f)) σ = smoothedSum ν ε X f := by
  have hM : Integrable fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) :=
    SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one σ_gt σ_le
  have hMc := continuous_mellin_line diffν νnonneg suppν mass_one εpos ε_lt_one (by linarith : 0 < σ)
  let F : ℕ → ℝ → ℂ := fun n t ↦ LSeries.term f (σ + t * I) n *
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I)
  have hnormF : ∀ n t, ‖F n t‖ =
      ‖LSeries.term f σ n‖ * X ^ σ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ := by
    intro n t
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos Xpos, LSeries.norm_term_eq]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
    ring
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [F, LSeries.term_zero, zero_mul]
      exact continuous_const
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 Xpos.ne'
      have e : F n = fun t : ℝ ↦ f n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I) := by
        funext t
        simp only [F, LSeries.term_of_ne_zero hn]
      rw [e]
      have h1 : Continuous fun t : ℝ ↦ (n : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hn')
      have h2 : Continuous fun t : ℝ ↦ (X : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hX')
      have h3 : ∀ t : ℝ, (n : ℂ) ^ ((σ : ℂ) + t * I) ≠ 0 := fun t ↦ by
        rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn' h.1
      exact ((continuous_const.div h1 h3).mul hMc).mul h2
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    refine Integrable.mono' (hM.norm.const_mul (‖LSeries.term f σ n‖ * X ^ σ))
      (hFcont n).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t ↦ (hnormF n t).le
  have hFsum : Summable fun n ↦ ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    exact (hf.norm.mul_right (X ^ σ)).mul_right _
  have hsum_pt : ∀ t : ℝ, integrand ν ε X (LSeries f) (σ + t * I) = ∑' n, F n t := by
    intro t
    simp only [integrand, F, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  calc VerticalIntegral' (integrand ν ε X (LSeries f)) σ
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, ∑' n, F n t := by
        simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
        simp_rw [hsum_pt]
        field_simp
    _ = (1 / (2 * π) : ℂ) * ∑' n, ∫ t : ℝ, F n t := by
        rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = ∑' n, (1 / (2 * π) : ℂ) * ∫ t : ℝ, F n t := by rw [tsum_mul_left]
    _ = smoothedSum ν ε X f := by
        unfold smoothedSum
        congr 1
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [F, hf0]
        · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
          have hx : 0 < (n : ℝ) / X := div_pos hnpos Xpos
          have hinv := mellinInv_mellin_eq σ (fun x ↦ (Smooth1 ν ε x : ℂ)) hx
            (Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one
              (by simp only [ofReal_re]; linarith)) hM
            (Smooth1ContinuousAt diffν νnonneg suppν εpos hx).ofReal
          rw [mellinInv] at hinv
          have hpt : ∀ t : ℝ, F n t = f n * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) •
              𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)) := by
            intro t
            simp only [F, LSeries.term_of_ne_zero hn]
            exact div_cpow_mul_cpow hn Xpos _ _ _
          simp_rw [hpt]
          rw [integral_const_mul, ← hinv, Complex.real_smul]
          push_cast
          ring

/-! ### Moving the line -/

/-- `∫_{[T, ∞)} g → 0` for integrable `g`. -/
lemma tendsto_integral_Ici {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun T : ℝ ↦ ∫ y in Ici T, g y) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := g) (s := fun T : ℝ ↦ Ici T)
    (fun _ ↦ measurableSet_Ici) (fun _ _ hab ↦ Ici_subset_Ici.2 hab) ⟨0, hg.integrableOn⟩
  have he : (⋂ T : ℝ, Ici T) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ici, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨x + 1, by linarith⟩
  rwa [he, Measure.restrict_empty, integral_zero_measure] at h

/-- `∫_{(−∞, −T]} g → 0` for integrable `g`. -/
lemma tendsto_integral_Iic_neg {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun T : ℝ ↦ ∫ y in Iic (-T), g y) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := g) (s := fun T : ℝ ↦ Iic (-T))
    (fun _ ↦ measurableSet_Iic) (fun _ _ hab ↦ Iic_subset_Iic.2 (neg_le_neg hab)) ⟨0, hg.integrableOn⟩
  have he : (⋂ T : ℝ, Iic (-T)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨-x + 1, by linarith⟩
  rwa [he, Measure.restrict_empty, integral_zero_measure] at h

/-- The horizontal integral at height `y` tends to `0` under uniform decay on the strip. -/
lemma tendsto_HIntegral {G : ℂ → ℂ} {σ' σ : ℝ} (hσ : σ' ≤ σ)
    (hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc σ' σ, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η)
    {u : ℝ → ℝ} (hu : Tendsto (fun T ↦ |u T|) atTop atTop) :
    Tendsto (fun T : ℝ ↦ HIntegral G σ' σ (u T)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η : ℝ := δ / (2 * (σ - σ' + 1)) with hηdef
  have hη : 0 < η := div_pos hδ (by linarith)
  obtain ⟨T₀, hT₀⟩ := hdecay η hη
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 hu) T₀ |> eventually_atTop.1
  refine ⟨N, fun T hT ↦ ?_⟩
  rw [dist_zero_right]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ') (b := σ) (C := η)
    (f := fun x : ℝ ↦ G (x + u T * I)) (fun x hx ↦ by
      rw [uIoc_of_le hσ] at hx
      exact hT₀ x ⟨hx.1.le, hx.2⟩ (u T) (hN T hT))
  rw [abs_of_nonneg (by linarith)] at hb
  calc ‖HIntegral G σ' σ (u T)‖ ≤ η * (σ - σ') := hb
    _ < δ := by
      rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **Moving the line of integration.** If `G` is holomorphic on the closed strip `σ' ≤ Re s ≤ σ`,
integrable on both lines, and tends to `0` uniformly on the strip as `|Im s| → ∞`, then
`∫_{(σ)} G = ∫_{(σ')} G`. -/
theorem verticalIntegral_shift {G : ℂ → ℂ} {σ' σ : ℝ} (hσ : σ' ≤ σ)
    (hG : HolomorphicOn G (Icc σ' σ ×ℂ univ))
    (hint : Integrable fun t : ℝ ↦ G (σ + t * I)) (hint' : Integrable fun t : ℝ ↦ G (σ' + t * I))
    (hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc σ' σ, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η) :
    VerticalIntegral G σ = VerticalIntegral G σ' := by
  have hdiff : ∀ T : ℝ, VerticalIntegral G σ - VerticalIntegral G σ' =
      UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T := by
    intro T
    have h := DiffVertRect_eq_UpperLowerUs (f := G) (σ := σ') (σ' := σ) (T := T) hint' hint
    have hR : RectangleIntegral G (σ' - I * T) (σ + I * T) = 0 := by
      refine HolomorphicOn.vanishesOnRectangle hG fun z hz ↦ ?_
      rw [Rectangle, mem_reProdIm] at hz
      rw [mem_reProdIm]
      refine ⟨?_, mem_univ _⟩
      have h1 := hz.1
      simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, sub_zero,
        mul_zero, add_re, add_zero] at h1
      rwa [uIcc_of_le hσ] at h1
    rw [hR, sub_zero] at h
    exact h
  have habs : Tendsto (fun T : ℝ ↦ |T|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp tendsto_id
  have habs' : Tendsto (fun T : ℝ ↦ |-T|) atTop atTop := by
    simpa only [abs_neg] using habs
  have hU : Tendsto (fun T ↦ UpperUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((tendsto_HIntegral hσ hdecay habs).add ((tendsto_integral_Ici hint).const_smul I)).sub
      ((tendsto_integral_Ici hint').const_smul I)
    simpa [UpperUIntegral] using this
  have hL : Tendsto (fun T ↦ LowerUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((tendsto_HIntegral hσ hdecay habs').sub ((tendsto_integral_Iic_neg hint).const_smul I)).add
      ((tendsto_integral_Iic_neg hint').const_smul I)
    simpa [LowerUIntegral] using this
  have hlim := hU.sub hL
  rw [sub_zero] at hlim
  have hconst : Tendsto (fun T ↦ UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T) atTop
      (𝓝 (VerticalIntegral G σ - VerticalIntegral G σ')) := by
    simp_rw [← hdiff]
    exact tendsto_const_nhds
  exact sub_eq_zero.1 (tendsto_nhds_unique hconst hlim)

/-- `|(1/2πi) ∫_{(σ)} G| ≤ ∫ g` when `|G(σ + it)| ≤ g(t)` with `g` integrable. -/
lemma norm_verticalIntegral'_le {G : ℂ → ℂ} {σ : ℝ} {g : ℝ → ℝ} (hg : Integrable g)
    (hG : ∀ t : ℝ, ‖G (σ + t * I)‖ ≤ g t) : ‖VerticalIntegral' G σ‖ ≤ ∫ t, g t := by
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, norm_mul, norm_I, one_mul]
  calc ‖1 / (2 * (π : ℂ) * I)‖ * ‖∫ t : ℝ, G (σ + t * I)‖ ≤ 1 * ∫ t, g t := by
        gcongr
        · exact MediumPNTW.norm_twoPiI_inv_le
        · exact norm_integral_le_of_norm_le hg (Eventually.of_forall hG)
    _ = ∫ t, g t := one_mul _

/-! ### The Mellin transform of the smoothing -/

/-- `m ≤ A`, `m ≤ B` give `m ≤ A^{1−κ} B^κ` for `κ ∈ [0, 1]`. -/
lemma le_geom {m A B κ : ℝ} (hm : 0 ≤ m) (hA : m ≤ A) (hB : m ≤ B) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    m ≤ A ^ (1 - κ) * B ^ κ := by
  rcases hm.eq_or_lt with rfl | hm'
  · positivity
  have e : m = m ^ (1 - κ) * m ^ κ := by
    rw [← Real.rpow_add hm', sub_add_cancel, Real.rpow_one]
  calc m = m ^ (1 - κ) * m ^ κ := e
    _ ≤ A ^ (1 - κ) * B ^ κ :=
      mul_le_mul (Real.rpow_le_rpow hm hA (by linarith)) (Real.rpow_le_rpow hm hB hκ0) (by positivity)
        (Real.rpow_nonneg (hm.trans hA) _)

/-- **The Mellin transform of `Smooth1` on a line**: for `κ ∈ [0, 1]` and `0 < σ ≤ 1` there is `K` with
`|𝓜(Smooth1 ν ε)(σ + it)| ≤ K ε^{−κ} (1 + |t|)^{−1−κ}` for every `0 < ε < 1`. -/
lemma mellin_le_geom (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤ K * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ)) := by
  obtain ⟨B, Bpos, hB⟩ := MediumPNTW.MellinOfSmooth1d diffν suppν
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨B ^ (1 - κ) * C ^ κ * (σ / 2) ^ (-(1 + κ)), by positivity, fun ε εpos ε_lt_one t ↦ ?_⟩
  set s : ℂ := σ + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs0 : 0 < ‖s‖ := norm_pos_iff.2 fun h ↦ by rw [h, zero_re] at hsre; linarith
  -- `|s| ≥ (σ/2)(1 + |t|)`
  have hslow : σ / 2 * (1 + |t|) ≤ ‖s‖ := by
    have h1 : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hsre, abs_of_pos hσ0] at this; exact this
    have h2 : |t| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; rwa [hsim] at this
    nlinarith [abs_nonneg t]
  have hm1 : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ B * ‖s‖⁻¹ :=
    hB s (by rw [hsre]; exact hσ0) (by rw [hsre]; linarith) ε εpos ε_lt_one
  have hm2 : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ :=
    hC σ hσ0 s (by rw [hsre]) (by rw [hsre]; linarith) ε εpos ε_lt_one
  have hg := le_geom (norm_nonneg _) hm1 hm2 hκ0 hκ1
  have e1 : (B * ‖s‖⁻¹) ^ (1 - κ) = B ^ (1 - κ) * ‖s‖ ^ (-(1 - κ)) := by
    rw [Real.mul_rpow Bpos.le (inv_nonneg.2 hs0.le), Real.inv_rpow hs0.le, ← Real.rpow_neg hs0.le]
  have e2 : (C * (ε * ‖s‖ ^ 2)⁻¹) ^ κ = C ^ κ * ε ^ (-κ) * ‖s‖ ^ (-(2 * κ)) := by
    have hsq : (‖s‖ ^ 2 : ℝ) ^ κ = ‖s‖ ^ (2 * κ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      norm_num
    rw [Real.mul_rpow Cpos.le (by positivity), Real.inv_rpow (by positivity),
      Real.mul_rpow εpos.le (by positivity), hsq, mul_inv, Real.rpow_neg εpos.le,
      Real.rpow_neg hs0.le]
    ring
  have e3 : ‖s‖ ^ (-(1 - κ)) * ‖s‖ ^ (-(2 * κ)) = ‖s‖ ^ (-(1 + κ)) := by
    rw [← Real.rpow_add hs0]
    ring_nf
  have e : (B * ‖s‖⁻¹) ^ (1 - κ) * (C * (ε * ‖s‖ ^ 2)⁻¹) ^ κ =
      B ^ (1 - κ) * C ^ κ * ε ^ (-κ) * ‖s‖ ^ (-(1 + κ)) := by
    rw [e1, e2, ← e3]
    ring
  rw [e] at hg
  calc ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ B ^ (1 - κ) * C ^ κ * ε ^ (-κ) * ‖s‖ ^ (-(1 + κ)) := hg
    _ ≤ B ^ (1 - κ) * C ^ κ * ε ^ (-κ) * (σ / 2 * (1 + |t|)) ^ (-(1 + κ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hslow (by linarith))
        (by positivity)
    _ = B ^ (1 - κ) * C ^ κ * (σ / 2) ^ (-(1 + κ)) * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

/-! ### Unsmoothing -/

/-- `#{n ∈ ℕ : a < n < b} ≤ b − a + 1` for `0 ≤ a ≤ b`. -/
lemma card_window_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (S : Finset ℕ) :
    ((S.filter fun n : ℕ ↦ a < n ∧ (n : ℝ) < b).card : ℝ) ≤ b - a + 1 := by
  have hsub : S.filter (fun n : ℕ ↦ a < n ∧ (n : ℝ) < b) ⊆ Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_Ioo]
    constructor
    · exact_mod_cast (Nat.floor_le ha).trans_lt hn.2.1
    · exact_mod_cast hn.2.2.trans_le (Nat.le_ceil b)
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ioo] at hc
  have hc' : ((S.filter fun n : ℕ ↦ a < n ∧ (n : ℝ) < b).card : ℝ) ≤ ((⌈b⌉₊ - ⌊a⌋₊ - 1 : ℕ) : ℝ) := by
    exact_mod_cast hc
  refine hc'.trans ?_
  have hb1 : (⌈b⌉₊ : ℝ) < b + 1 := Nat.ceil_lt_add_one (ha.trans hab)
  have ha1 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  rcases le_or_gt (⌊a⌋₊ + 1) ⌈b⌉₊ with h | h
  · rw [Nat.sub_sub, Nat.cast_sub h]
    push_cast
    linarith
  · rw [Nat.sub_sub, Nat.sub_eq_zero_of_le h.le]
    simp only [Nat.cast_zero]
    linarith

/-- **Unsmoothing.** If `f(0) = 0` and `|f(n)| ≤ B` for `n ≤ 3X`, then
`|Σ f(n) Smooth1(n/X) − Σ_{1 ≤ n ≤ X} f(n)| ≤ B(3 log 2 · εX + 1)`. -/
theorem norm_smoothedSum_sub_le {f : ℕ → ℂ} (hf0 : f 0 = 0) {X : ℝ} (Xpos : 0 < X) {B : ℝ}
    (hB : ∀ n : ℕ, (n : ℝ) ≤ 3 * X → ‖f n‖ ≤ B)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    ‖smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤
      B * (3 * Real.log 2 * ε * X + 1) := by
  obtain ⟨c₁, -, hc₁, hbelow⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above suppν
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp; linarith))
  set N : ℕ := ⌊3 * X⌋₊ + 1 with hNdef
  set a : ℝ := X * (1 - c₁ * ε) with hadef
  set b : ℝ := X * (1 + c₂ * ε) with hbdef
  have ha0 : 0 ≤ a := by
    rw [hadef, hc₁]
    have : Real.log 2 * ε < 1 := by nlinarith
    exact mul_nonneg Xpos.le (by linarith)
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    have : 0 ≤ c₁ * ε := by rw [hc₁]; positivity
    have : 0 ≤ c₂ * ε := by rw [hc₂]; positivity
    nlinarith
  have hb3 : b ≤ 3 * X := by
    rw [hbdef, hc₂]
    have : 2 * Real.log 2 * ε ≤ 2 := by nlinarith
    nlinarith
  have hXa : a ≤ X := by
    rw [hadef]
    have : 0 ≤ c₁ * ε := by rw [hc₁]; positivity
    nlinarith
  have hXb : X ≤ b := by
    rw [hbdef]
    have : 0 ≤ c₂ * ε := by rw [hc₂]; positivity
    nlinarith
  -- `Smooth1` vanishes beyond `b`
  have hS0 : ∀ n : ℕ, b ≤ n → Smooth1 ν ε (n / X) = 0 := fun n hn ↦
    habove ε (n / X) ⟨εpos, ε_lt_one⟩ (by rw [le_div_iff₀ Xpos]; linarith)
  have hS1 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ a → Smooth1 ν ε (n / X) = 1 := fun n hn hna ↦
    hbelow ε (n / X) εpos (div_pos (Nat.cast_pos.2 hn) Xpos) (by rw [div_le_iff₀ Xpos]; linarith)
  -- the smoothed sum is finite
  have hfin : smoothedSum ν ε X f = ∑ n ∈ Finset.range N, f n * (Smooth1 ν ε (n / X) : ℂ) := by
    unfold smoothedSum
    refine tsum_eq_sum fun n hn ↦ ?_
    rw [Finset.mem_range, not_lt] at hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 3 * X < N := by rw [hNdef]; push_cast; exact Nat.lt_floor_add_one _
    rw [hS0 n (by linarith), ofReal_zero, mul_zero]
  -- the sharp sum over the same range
  have hsub : Finset.Icc 1 ⌊X⌋₊ ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range, hNdef]
    have : ⌊X⌋₊ ≤ ⌊3 * X⌋₊ := Nat.floor_le_floor (by linarith)
    omega
  have hsharp : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n =
      ∑ n ∈ Finset.range N, f n * (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0) := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  rw [hfin, hsharp, ← Finset.sum_sub_distrib]
  -- termwise
  have hterm : ∀ n ∈ Finset.range N,
      ‖f n * (Smooth1 ν ε (n / X) : ℂ) - f n * (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0)‖ ≤
        B * (if a < n ∧ (n : ℝ) < b then 1 else 0) := by
    intro n hn
    have hn3 : (n : ℝ) ≤ 3 * X := by
      rw [Finset.mem_range, hNdef] at hn
      have : n ≤ ⌊3 * X⌋₊ := by omega
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
    rw [← mul_sub, norm_mul]
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [hf0, norm_zero, zero_mul]
      positivity
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hmem : n ∈ Finset.Icc 1 ⌊X⌋₊ ↔ (n : ℝ) ≤ X := by
      rw [Finset.mem_Icc, Nat.le_floor_iff Xpos.le]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hnpos, h⟩
    by_cases hw : a < n ∧ (n : ℝ) < b
    · rw [ite_eq_left hw, mul_one]
      have hS : 0 ≤ Smooth1 ν ε (n / X) ∧ Smooth1 ν ε (n / X) ≤ 1 :=
        ⟨Smooth1Nonneg νnonneg (div_pos (Nat.cast_pos.2 hnpos) Xpos) εpos,
          Smooth1LeOne νnonneg mass_one εpos (div_pos (Nat.cast_pos.2 hnpos) Xpos)⟩
      have hd : ‖(Smooth1 ν ε (n / X) : ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0)‖ ≤ 1 := by
        split_ifs
        · rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith
        · rw [sub_zero, norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith
      calc ‖f n‖ * ‖(Smooth1 ν ε (n / X) : ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0)‖
          ≤ B * 1 := mul_le_mul (hB n hn3) hd (norm_nonneg _) hB0
        _ = B := mul_one B
    · rw [ite_eq_right hw, mul_zero]
      rw [not_and_or, not_lt, not_lt] at hw
      rcases hw with h | h
      · rw [hS1 n hnpos h, ite_eq_left (hmem.2 (h.trans hXa)), ofReal_one, sub_self, norm_zero, mul_zero]
      · have hnX : ¬ (n : ℝ) ≤ X := by
          intro h'
          have : b ≤ X := h.trans h'
          have : 0 < c₂ * ε := by rw [hc₂]; positivity
          rw [hbdef] at *
          nlinarith
        rw [hS0 n h, ite_eq_right (fun h' ↦ hnX (hmem.1 h')), ofReal_zero, sub_zero, norm_zero, mul_zero]
  calc ‖∑ n ∈ Finset.range N, (f n * (Smooth1 ν ε (n / X) : ℂ) -
        f n * (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0))‖
      ≤ ∑ n ∈ Finset.range N, ‖f n * (Smooth1 ν ε (n / X) : ℂ) -
        f n * (if n ∈ Finset.Icc 1 ⌊X⌋₊ then 1 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, B * (if a < n ∧ (n : ℝ) < b then 1 else 0) :=
        Finset.sum_le_sum hterm
    _ = B * ((Finset.range N).filter fun n : ℕ ↦ a < n ∧ (n : ℝ) < b).card := by
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ B * (b - a + 1) := by gcongr; exact card_window_le ha0 hab _
    _ = B * (3 * Real.log 2 * ε * X + 1) := by
        rw [hadef, hbdef, hc₁, hc₂]
        ring

/-! ### The identity on a line left of `1` -/

/-- `‖L(f, σ + it)‖ ≤ Σ ‖f(n) n^{−σ}‖`. -/
lemma norm_LSeries_le {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) (t : ℝ) :
    ‖LSeries f (σ + t * I)‖ ≤ ∑' n, ‖LSeries.term f σ n‖ := by
  have he : ∀ n, ‖LSeries.term f (σ + t * I) n‖ = ‖LSeries.term f σ n‖ := by
    intro n
    simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
  have hs : Summable fun n ↦ ‖LSeries.term f (σ + t * I) n‖ := by
    simpa only [he] using hf.norm
  calc ‖LSeries f (σ + t * I)‖ ≤ ∑' n, ‖LSeries.term f (σ + t * I) n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖LSeries.term f σ n‖ := by simp_rw [he]

lemma norm_integrand {L : ℂ → ℂ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    ‖integrand ν ε X L s‖ = ‖L s‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * X ^ s.re := by
  simp only [integrand, norm_mul, norm_cpow_eq_rpow_re_of_pos Xpos]

lemma continuous_integrand_line {L : ℂ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hL : Continuous fun t : ℝ ↦ L (σ + t * I)) (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {X : ℝ} (Xpos : 0 < X) :
    Continuous fun t : ℝ ↦ integrand ν ε X L (σ + t * I) :=
  (hL.mul (continuous_mellin_line diffν νnonneg suppν mass_one εpos ε_lt_one hσ)).mul
    (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 Xpos.ne')))

/-- **The smoothed sum as an integral on a line left of `1`.** Let `L(f, s) = L(s)` on `Re s > 1`, with
`L(f, 2)` absolutely convergent and `L` holomorphic on `Re s ≥ σ'` (`0 < σ' ≤ 2`) of at most linear growth
`|L(σ + it)| ≤ C|t|` on `σ' ≤ σ ≤ 2`, `|t| ≥ T`. Then for `0 < ε < 1`, `X ≥ 1`, and the integrand integrable
on `Re s = σ'`: `Σ_n f(n) Smooth1(n/X) = (1/2πi) ∫_{(σ')} L(s) 𝓜(Smooth1)(s) X^s ds`. -/
theorem smoothedSum_eq_verticalIntegral_left {f : ℕ → ℂ} (hf0 : f 0 = 0)
    (hf : LSeriesSummable f ((2 : ℝ) : ℂ)) {L : ℂ → ℂ} (hL : ∀ s : ℂ, 1 < s.re → LSeries f s = L s)
    {σ' : ℝ} (hσ'0 : 0 < σ') (hσ'2 : σ' ≤ 2) (hLd : ∀ s : ℂ, σ' ≤ s.re → DifferentiableAt ℂ L s)
    {T C : ℝ} (hgrowth : ∀ σ t : ℝ, σ' ≤ σ → σ ≤ 2 → T ≤ |t| → ‖L (σ + t * I)‖ ≤ C * |t|)
    (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (hX : 1 ≤ X) (hint' : Integrable fun t : ℝ ↦ integrand ν ε X L (σ' + t * I)) :
    smoothedSum ν ε X f = VerticalIntegral' (integrand ν ε X L) σ' := by
  have Xpos : 0 < X := by linarith
  rw [← verticalIntegral_eq_smoothedSum hf0 diffν νnonneg suppν mass_one εpos ε_lt_one Xpos
    (by norm_num : (1 : ℝ) < 2) le_rfl hf]
  have hline : VerticalIntegral' (integrand ν ε X (LSeries f)) 2 =
      VerticalIntegral' (integrand ν ε X L) 2 := by
    simp only [VerticalIntegral', VerticalIntegral]
    congr 3
    funext t
    simp only [integrand]
    rw [hL _ (by simp)]
  rw [hline]
  simp only [VerticalIntegral']
  congr 1
  have hcont2 : Continuous fun t : ℝ ↦ L ((2 : ℝ) + t * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' (t := {s : ℂ | σ' ≤ s.re}) ?_ (by fun_prop) ?_
    · exact fun s hs ↦ (hLd s hs).continuousAt.continuousWithinAt
    · intro t _
      simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      exact hσ'2
  obtain ⟨C₂, C₂pos, hC₂⟩ := MellinOfSmooth1b diffν suppν
  refine verticalIntegral_shift hσ'2 ?_ ?_ hint' ?_
  · intro s hs
    rw [mem_reProdIm] at hs
    have hre : σ' ≤ s.re := hs.1.1
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 := Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one
      (show 0 < s.re by linarith)
    have h2 : DifferentiableAt ℂ (fun y : ℂ ↦ (X : ℂ) ^ y) s :=
      (differentiableAt_id).const_cpow (Or.inl (ofReal_ne_zero.2 Xpos.ne'))
    exact ((hLd s hre).mul h1).mul h2
  · -- integrable on `Re s = 2`
    have hM2 : Integrable fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I) :=
      SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one
        (by norm_num) le_rfl
    refine Integrable.mono' (hM2.norm.const_mul ((∑' n, ‖LSeries.term f (2 : ℝ) n‖) * X ^ (2 : ℝ)))
      (continuous_integrand_line (by norm_num) hcont2 diffν νnonneg suppν mass_one εpos ε_lt_one
        Xpos).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    rw [norm_integrand Xpos]
    have hre : ((2 : ℝ) + t * I : ℂ).re = 2 := by simp
    rw [hre, ← hL _ (by rw [hre]; norm_num)]
    have := norm_LSeries_le hf t
    calc ‖LSeries f ((2 : ℝ) + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ * X ^ (2 : ℝ)
        ≤ (∑' n, ‖LSeries.term f (2 : ℝ) n‖) * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ *
          X ^ (2 : ℝ) := by gcongr
      _ = _ := by ring
  · -- decay on horizontal segments
    intro η hη
    set A : ℝ := max C 0 * C₂ * X ^ (2 : ℝ) / ε with hAdef
    have hA : 0 ≤ A := by positivity
    refine ⟨max (max T 1) (A / η), fun x hx y hy ↦ ?_⟩
    have hy1 : 1 ≤ |y| := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
    have hyT : T ≤ |y| := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
    have hyA : A / η ≤ |y| := (le_max_right _ _).trans hy
    have hy0 : 0 < |y| := by linarith
    set s : ℂ := x + y * I with hsdef
    have hsre : s.re = x := by simp [hsdef]
    have hsim : s.im = y := by simp [hsdef]
    have hsy : |y| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; rwa [hsim] at this
    rw [norm_integrand Xpos, hsre]
    have hL' : ‖L s‖ ≤ max C 0 * |y| :=
      (hgrowth x y hx.1 hx.2 hyT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0.le)
    have hM' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C₂ * (ε * |y| ^ 2)⁻¹ := by
      refine (hC₂ σ' hσ'0 s (by rw [hsre]; exact hx.1) (by rw [hsre]; exact hx.2) ε εpos
        ε_lt_one).trans ?_
      gcongr
    have hXx : X ^ x ≤ X ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hx.2
    calc ‖L s‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * X ^ x
        ≤ (max C 0 * |y|) * (C₂ * (ε * |y| ^ 2)⁻¹) * X ^ (2 : ℝ) := by gcongr
      _ = A / |y| := by
        rw [hAdef]
        field_simp
      _ ≤ η := by
        rw [div_le_iff₀ hy0]
        rw [div_le_iff₀ hη] at hyA
        linarith

end SmoothPerron

#print axioms SmoothPerron.verticalIntegral_eq_smoothedSum
#print axioms SmoothPerron.verticalIntegral_shift
#print axioms SmoothPerron.mellin_le_geom
#print axioms SmoothPerron.norm_smoothedSum_sub_le
#print axioms SmoothPerron.smoothedSum_eq_verticalIntegral_left
