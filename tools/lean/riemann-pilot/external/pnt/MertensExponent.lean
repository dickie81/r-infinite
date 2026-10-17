/-
# Round 472: Mertens' function in a zero-free half-plane, and `Θ` as its exponent

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` for `Re s > θ` (`0 ≤ θ < 1`), then `M(x) = Σ_{n ≤ x} μ(n) = O(x^{θ+η})` for every
`η > 0` (`mertens_isBigO_of_zeroFree`). At `θ = 11/12` (round 466's half-plane) and at `θ = Θ` (round 469's
supremum of the real parts of the nontrivial zeros) this holds with no hypothesis. With round 221's
`M(x) = Ω±(x^θ)` below the real part of any zero: `limsup log|M(x)| / log x = Θ` (`limsup_mexpo`), the
same exponent as round 469's `limsup log|ψ(x) − x| / log x`; `RH ⟺ Θ = ½` (`rh_iff_Theta_eq_half`);
`RH ⟺ M(x) = O(x^{½+η})` for every `η > 0` (`rh_iff_mertens`, Littlewood's criterion); and the partial sums of
`Σ μ(n) n^{−s}` converge for `Re s > Θ` and diverge for `Re s < Θ`, so its abscissa of convergence is `Θ`
(`moebiusAbscissa_eq_Theta`).

* `invZeta`: `1/ζ` as `(s − 1)/Z(s)` with round 220's entire `Z(s) = (s − 1)ζ(s)` (`PsiOmega.Zr`), so that it is
  holomorphic wherever `Z ≠ 0`, across `s = 1`; it is `L(μ, s)` on `Re s > 1` (round 221's
  `LSeries_moebius_eq`).
* `invZeta_line_bound`: `|1/ζ(θ' + it)| ≤ K(1 + |t|)^ε₁` for `θ' > θ`, from round 470's Lindelöf bound
  (`HalfPlaneLindelof.zeta_bound_of_zeroFree`) for large `|t|` and compactness for small `|t|`.
* `mertens_isBigO_of_zeroFree`: `SmoothPerron.smoothedSum_eq_verticalIntegral_left` moves the smoothed
  Perron integral to `Re s = θ' = θ + η₀/4`, where `SmoothPerron.mellin_le_geom` (with `κ = η₀/4`) and
  `invZeta_line_bound` (with `ε₁ = η₀/8`) give `O(ε^{−κ} X^{θ'})`; `SmoothPerron.norm_smoothedSum_sub_le`
  costs `3 log 2 · εX + 1`; and `ε = X^{θ'−1}`.
* `rh_iff_Theta_eq_half`: `Θ ≤ ½` under Mathlib's `RiemannHypothesis` (a nontrivial zero is not `1`, since
  `ζ(1) ≠ 0`); conversely round 335's `rh_of_zeroFree_half`.
* `rh_iff_mertens`: the converse half is round 221's `zeta_ne_zero_of_mertens`, after `|M(x)| ≤ x` turns the
  eventual bound into one on `(1, ∞)` (`zeta_ne_zero_of_mertens_isBigO`).
* `moebius_tendsto_of_Theta_lt`: Abel summation (Mathlib's `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`,
  as in its `LSeries_eq_mul_integral` without the hypothesis of absolute convergence,
  `tendsto_partialSum_of_isBigO`) from `M(x) = O(x^{Θ+η})`.
* `moebius_not_tendsto_of_lt_Theta`: convergence at `s` would give `M(x) = O(x^{σ₁})` for every
  `σ₁ ≥ max(Re s, 0)`, `σ₁ > 0` (Abel summation against `t^s`, `norm_sum_le_of_tendsto`), against
  `mertens_omega_Theta` for `σ₁ < Θ`.
-/
import SmoothPerron
import MertensOmega

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform4) "𝓜" => mellin

namespace MertensExponent

open SmoothPerron PsiOmega PsiExponent

/-- The Möbius coefficients, complex. -/
noncomputable abbrev fμc : ℕ → ℂ := fun n ↦ (fμ n : ℂ)

lemma fμc_zero : fμc 0 = 0 := by simp [fμc, fμ]

lemma norm_fμc_le (n : ℕ) : ‖fμc n‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  show |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `1/ζ` through round 220's entire `Z(s) = (s − 1)ζ(s)`. -/
noncomputable def invZeta (s : ℂ) : ℂ := (s - 1) / Zr s

lemma invZeta_of_ne {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  unfold invZeta
  rw [Zr_of_ne hs, ← div_div, div_self (sub_ne_zero.2 hs), one_div]

lemma LSeries_moebius_eq_invZeta {s : ℂ} (hs : 1 < s.re) : LSeries fμc s = invZeta s := by
  have hs1 : s ≠ 1 := fun h ↦ by rw [h, one_re] at hs; exact lt_irrefl _ hs
  rw [invZeta_of_ne hs1, ← one_div]
  exact LSeries_moebius_eq hs

lemma Zr_ne_zero_of_zeroFree {θ : ℝ} (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {s : ℂ}
    (hs : θ < s.re) : Zr s ≠ 0 :=
  fun h ↦ hzf s hs (Zr_eq_zero h).2

lemma differentiableAt_invZeta {s : ℂ} (hs : Zr s ≠ 0) : DifferentiableAt ℂ invZeta s := by
  show DifferentiableAt ℂ (fun s ↦ (s - 1) / Zr s) s
  exact (differentiableAt_id.sub_const 1).div (differentiable_Zr s) hs

lemma continuous_invZeta_line {θ σ : ℝ} (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) (hσ : θ < σ) :
    Continuous fun t : ℝ ↦ invZeta (σ + t * I) := by
  have hZ : ∀ t : ℝ, Zr (σ + t * I) ≠ 0 := fun t ↦ Zr_ne_zero_of_zeroFree hzf (by simpa using hσ)
  have hZc : Continuous Zr := differentiable_Zr.continuous
  unfold invZeta
  exact Continuous.div (by fun_prop) (by fun_prop) hZ

/-- **`1/ζ` on a vertical line in a zero-free half-plane**: `|1/ζ(θ' + it)| ≤ K(1 + |t|)^ε` for `θ' > θ`. -/
lemma invZeta_line_bound {θ θ' ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθθ' : θ < θ') (hε : 0 < ε)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ‖invZeta (θ' + t * I)‖ ≤ K * (1 + |t|) ^ ε := by
  obtain ⟨T, C, hTC⟩ := HalfPlaneLindelof.zeta_bound_of_zeroFree hθ0 hθ1 hθθ' hε hzf
  set T' := max T 1 with hT'def
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := -T') (b := T')).exists_bound_of_continuousOn
    (continuous_invZeta_line hzf hθθ').continuousOn
  refine ⟨max C₀ 0 + max C 0, by positivity, fun t ↦ ?_⟩
  have h1 : 1 ≤ (1 + |t|) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg t]) hε.le
  by_cases ht : |t| ≤ T'
  · have hmem : t ∈ Icc (-T') T' := by
      rw [mem_Icc]
      constructor <;> linarith [abs_le.1 ht]
    calc ‖invZeta (θ' + t * I)‖ ≤ C₀ := hC₀ t hmem
      _ ≤ max C₀ 0 := le_max_left _ _
      _ ≤ max C₀ 0 * (1 + |t|) ^ ε := le_mul_of_one_le_right (le_max_right _ _) h1
      _ ≤ (max C₀ 0 + max C 0) * (1 + |t|) ^ ε := by
          gcongr
          exact le_add_of_nonneg_right (le_max_right _ _)
  · rw [not_le] at ht
    have htT : T ≤ |t| := (le_max_left _ _).trans ht.le
    have ht1 : 1 ≤ |t| := (le_max_right _ _).trans ht.le
    have hne : (θ' : ℂ) + t * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, one_im] at this
      rw [this, abs_zero] at ht1
      norm_num at ht1
    rw [invZeta_of_ne hne, norm_inv]
    have hb := (hTC θ' t le_rfl htT).2
    calc ‖riemannZeta (θ' + t * I)‖⁻¹ ≤ C * |t| ^ ε := hb
      _ ≤ max C 0 * |t| ^ ε := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (1 + |t|) ^ ε := by gcongr; linarith
      _ ≤ (max C₀ 0 + max C 0) * (1 + |t|) ^ ε := by
          gcongr
          exact le_add_of_nonneg_left (le_max_right _ _)

/-- **Mertens' function in a zero-free half-plane**: if `ζ(s) ≠ 0` for `Re s > θ` (`0 ≤ θ < 1`), then
`M(x) = O(x^{θ+η})` for every `η > 0`. -/
theorem mertens_isBigO_of_zeroFree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ (θ + η) := by
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
  have hκ0 : 0 ≤ κ := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hε₁ : 0 < ε₁ := by linarith
  have hε₁1 : ε₁ ≤ 1 := by linarith
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν ν_supp hκ0 hκ1 hθ'0 hθ'1.le
  obtain ⟨K₁, hK₁0, hK₁⟩ := invZeta_line_bound hθ0 hθ1 hθθ' hε₁ hzf
  obtain ⟨T, C, hTC⟩ := HalfPlaneLindelof.zeta_bound_of_zeroFree hθ0 hθ1 hθθ' hε₁ hzf
  set r : ℝ := 1 + κ - ε₁ with hrdef
  have hr : 1 < r := by linarith
  have hIr : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-r) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)
    simpa only [Real.norm_eq_abs] using this
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIrdef
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t ↦ by positivity
  -- linear growth of `1/ζ` on horizontal segments
  have hgrowth : ∀ σ t : ℝ, θ' ≤ σ → σ ≤ 2 → max T 1 ≤ |t| → ‖invZeta (σ + t * I)‖ ≤ C * |t| := by
    intro σ t hσ _ ht
    have ht1 : 1 ≤ |t| := (le_max_right _ _).trans ht
    have hne : (σ : ℂ) + t * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, one_im] at this
      rw [this, abs_zero] at ht1
      norm_num at ht1
    rw [invZeta_of_ne hne, norm_inv]
    have hb := (hTC σ t hσ ((le_max_left _ _).trans ht)).2
    have htpos : 0 < |t| ^ ε₁ := Real.rpow_pos_of_pos (by linarith) _
    have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right htpos).1 ((inv_nonneg.2 (norm_nonneg _)).trans hb)
    calc ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε₁ := hb
      _ ≤ C * |t| := by
          gcongr
          exact (Real.rpow_le_rpow_of_exponent_le ht1 hε₁1).trans_eq (Real.rpow_one _)
  refine IsBigO.of_bound (K₁ * KM * Ir + 4) ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  have Xpos : 0 < X := by linarith
  set ε : ℝ := X ^ (θ' - 1) with hεdef
  have εpos : 0 < ε := Real.rpow_pos_of_pos Xpos _
  have ε_lt_one : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg hX (by linarith)
  -- the integrand on `Re s = θ'`
  have hpt : ∀ t : ℝ, ‖integrand ν ε X invZeta (θ' + t * I)‖ ≤
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
    calc ‖invZeta (θ' + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (θ' + t * I)‖ * X ^ θ'
        ≤ (K₁ * (1 + |t|) ^ ε₁) * (KM * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ))) * X ^ θ' := by
          gcongr
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * ((1 + |t|) ^ ε₁ * (1 + |t|) ^ (-(1 + κ))) := by ring
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) := by rw [hpow]
  have hint' : Integrable fun t : ℝ ↦ integrand ν ε X invZeta (θ' + t * I) :=
    Integrable.mono' (hIr.const_mul (K₁ * KM * ε ^ (-κ) * X ^ θ'))
      (continuous_integrand_line hθ'0 (continuous_invZeta_line hzf hθθ') diffν νnonneg ν_supp
        mass_one εpos ε_lt_one Xpos).aestronglyMeasurable (Eventually.of_forall hpt)
  have hid := smoothedSum_eq_verticalIntegral_left (f := fμc) fμc_zero
    (LSeriesSummable_moebius' (by norm_num)) (fun s hs ↦ LSeries_moebius_eq_invZeta hs) hθ'0
    (by linarith) (fun s hs ↦ differentiableAt_invZeta (Zr_ne_zero_of_zeroFree hzf (by linarith)))
    hgrowth diffν νnonneg ν_supp mass_one εpos ε_lt_one hX.le hint'
  have hsm : ‖smoothedSum ν ε X fμc‖ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by
    rw [hid]
    calc _ ≤ ∫ t, K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) :=
          norm_verticalIntegral'_le (hIr.const_mul _) hpt
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * Ir := integral_const_mul _ _
      _ = K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by ring
  have hun := norm_smoothedSum_sub_le fμc_zero Xpos (B := 1) (fun n _ ↦ norm_fμc_le n)
    νnonneg ν_supp mass_one εpos ε_lt_one
  -- exponents
  have hεκ : ε ^ (-κ) * X ^ θ' ≤ X ^ (θ' + κ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by nlinarith)
  have hεX : ε * X = X ^ θ' := by
    rw [hεdef, ← Real.rpow_add_one Xpos.ne', sub_add_cancel]
  have hθκ : X ^ θ' ≤ X ^ (θ' + κ) := Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have h1κ : 1 ≤ X ^ (θ' + κ) := Real.one_le_rpow hX.le (by linarith)
  have hfin : X ^ (θ' + κ) ≤ X ^ (θ + η) := Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hM : ((summ fμ X : ℝ) : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, fμc n := by
    simp only [summ, fμc]
    push_cast
    rfl
  rw [Real.norm_of_nonneg (Real.rpow_nonneg Xpos.le (θ + η)), ← Complex.norm_real, hM]
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, fμc n =
      smoothedSum ν ε X fμc - (smoothedSum ν ε X fμc - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, fμc n) := by ring
  rw [hsplit]
  calc ‖smoothedSum ν ε X fμc - (smoothedSum ν ε X fμc - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, fμc n)‖
      ≤ ‖smoothedSum ν ε X fμc‖ + ‖smoothedSum ν ε X fμc - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, fμc n‖ :=
        norm_sub_le _ _
    _ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + 1 * (3 * Real.log 2 * ε * X + 1) := add_le_add hsm hun
    _ = K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + (3 * Real.log 2 * X ^ θ' + 1) := by
        rw [← hεX]
        ring
    _ ≤ K₁ * KM * Ir * X ^ (θ' + κ) + (3 * X ^ (θ' + κ) + X ^ (θ' + κ)) := by
        gcongr
        linarith
    _ = (K₁ * KM * Ir + 4) * X ^ (θ' + κ) := by ring
    _ ≤ (K₁ * KM * Ir + 4) * X ^ (θ + η) := by gcongr

/-- **`M(x) = O(x^{11/12+η})`** for every `η > 0`, from round 466's half-plane. -/
theorem mertens_isBigO_eleven_twelfths {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ (11 / 12 + η) :=
  mertens_isBigO_of_zeroFree (by norm_num) (by norm_num)
    (fun _ hs ↦ (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1) hη

/-- **`M(x) = O(x^{Θ+η})`** for every `η > 0`. -/
theorem mertens_isBigO_Theta {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ (Theta + η) :=
  mertens_isBigO_of_zeroFree (by linarith [half_le_Theta]) (by linarith [Theta_le])
    (fun _ hs ↦ zeta_ne_zero_of_Theta_lt hs) hη

/-- **`M(x) = Ω±(x^{Θ−η})`** for `0 < η < Θ`: round 221's `mertens_omega` at a zero with `Re ρ > Θ − η`. -/
theorem mertens_omega_Theta {η : ℝ} (hη : 0 < η) (hηΘ : η < Theta) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ (Theta - η) < summ fμ x) ∧
      (∃ x, X < x ∧ summ fμ x < -(c * x ^ (Theta - η))) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_gt hη
  exact mertens_omega hρ.1 (by linarith) hre c X

/-! ### `RH ⟺ Θ = ½` -/

/-- **`RH ⟺ Θ = ½`.** -/
theorem rh_iff_Theta_eq_half : RiemannHypothesis ↔ Theta = 1 / 2 := by
  constructor
  · intro hRH
    refine le_antisymm (csSup_le zeroReals_nonempty ?_) half_le_Theta
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρ1 : ρ ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hρ.1)
    exact (hRH ρ hρ.1 hρ.2 hρ1).le
  · intro h
    exact rh_of_zeroFree_half fun ρ hρ ↦ zeta_ne_zero_of_Theta_lt (by rw [h]; exact hρ)

/-- A bound `M(x) = O(x^θ)` with `0 < θ ≤ 1` makes `ζ ≠ 0` on `Re s > θ` (round 221's
`zeta_ne_zero_of_mertens`, after a bound on `(1, ∞)` from `|M(x)| ≤ x`). -/
theorem zeta_ne_zero_of_mertens_isBigO {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h : (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ θ) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hC
  refine zeta_ne_zero_of_mertens (c := |C| + |x₀|) (ε := 1) hθ hθ1 one_ne_zero (fun x hx ↦ ?_) hρ
  have hx0 : 0 ≤ x := by linarith
  have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx.le hθ.le
  rw [one_mul]
  by_cases hxx : x₀ ≤ x
  · have := hx₀ x hxx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] at this
    calc summ fμ x ≤ |summ fμ x| := le_abs_self _
      _ ≤ C * x ^ θ := this
      _ ≤ (|C| + |x₀|) * x ^ θ := by
          gcongr
          linarith [le_abs_self C, abs_nonneg x₀]
  · rw [not_le] at hxx
    have hlin := linBound_moebius x hx0
    calc summ fμ x ≤ |summ fμ x| := le_abs_self _
      _ ≤ 1 * x := hlin
      _ ≤ |x₀| := by linarith [le_abs_self x₀]
      _ ≤ (|C| + |x₀|) * 1 := by linarith [abs_nonneg C]
      _ ≤ (|C| + |x₀|) * x ^ θ := by gcongr

/-- **Littlewood's criterion**: `RH ⟺ M(x) = O(x^{½+η})` for every `η > 0`. -/
theorem rh_iff_mertens :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ (1 / 2 + η) := by
  constructor
  · intro hRH η hη
    have := mertens_isBigO_Theta hη
    rwa [rh_iff_Theta_eq_half.1 hRH] at this
  · intro h
    refine rh_iff_Theta_eq_half.2 (le_antisymm ?_ half_le_Theta)
    refine le_of_forall_pos_lt_add fun η hη ↦ ?_
    set η' : ℝ := min η 1 / 2 with hη'def
    have hη' : 0 < η' := by positivity
    have hη'η : η' < η := by
      have := min_le_left η 1
      rw [hη'def]
      linarith
    have hη'1 : η' ≤ 1 / 2 := by
      have := min_le_right η 1
      rw [hη'def]
      linarith
    have hzf : ∀ ρ : ℂ, 1 / 2 + η' < ρ.re → riemannZeta ρ ≠ 0 := fun ρ hρ ↦
      zeta_ne_zero_of_mertens_isBigO (by linarith) (by linarith) (h η' hη') hρ
    have hle : Theta ≤ 1 / 2 + η' := by
      refine csSup_le zeroReals_nonempty ?_
      rintro _ ⟨ρ, hρ, rfl⟩
      by_contra hlt
      exact hzf ρ (not_le.1 hlt) hρ.1
    linarith

/-! ### `limsup log|M(x)| / log x = Θ` -/

/-- The exponent of Mertens' function at `x`: `log|M(x)| / log x`. -/
noncomputable def mexpo (x : ℝ) : ℝ := Real.log |summ fμ x| / Real.log x

theorem eventually_mexpo_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x in atTop, mexpo x ≤ Theta + 2 * ε := by
  obtain ⟨C, hC⟩ := (mertens_isBigO_Theta hε).bound
  have hlog : ∀ᶠ x in atTop, Real.log (max C 1) ≤ ε * Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (max C 1) / ε)] with x hx
    rw [div_le_iff₀ hε] at hx
    linarith
  filter_upwards [hC, hlog, eventually_gt_atTop 1] with x hx hl h1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos h1
  have hxp : 0 < x ^ (Theta + ε) := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxp] at hx
  unfold mexpo
  rw [div_le_iff₀ hlx]
  rcases eq_or_lt_of_le (abs_nonneg (summ fμ x)) with h | h
  · rw [← h, Real.log_zero]
    exact mul_nonneg (by linarith [half_le_Theta]) hlx.le
  · have hC1 : |summ fμ x| ≤ max C 1 * x ^ (Theta + ε) :=
      hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxp.le)
    calc Real.log |summ fμ x| ≤ Real.log (max C 1 * x ^ (Theta + ε)) := Real.log_le_log h hC1
      _ = Real.log (max C 1) + (Theta + ε) * Real.log x := by
        rw [Real.log_mul (by positivity) hxp.ne', Real.log_rpow hx0]
      _ ≤ (Theta + 2 * ε) * Real.log x := by
        have e : (Theta + 2 * ε) * Real.log x = (Theta + ε) * Real.log x + ε * Real.log x := by ring
        rw [e]
        linarith

theorem frequently_le_mexpo {ε : ℝ} (hε : 0 < ε) (hεΘ : ε < Theta) :
    ∃ᶠ x in atTop, Theta - ε ≤ mexpo x := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨x, hx, hlt⟩ := (mertens_omega_Theta hε hεΘ 1 (max a 1)).1
  refine ⟨x, (le_max_left _ _).trans hx.le, ?_⟩
  have h1 : 1 < x := (le_max_right _ _).trans_lt hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos h1
  rw [one_mul] at hlt
  have hpos : 0 < x ^ (Theta - ε) := Real.rpow_pos_of_pos hx0 _
  have habs : x ^ (Theta - ε) ≤ |summ fμ x| := hlt.le.trans (le_abs_self _)
  unfold mexpo
  rw [le_div_iff₀ hlx, ← Real.log_rpow hx0]
  exact Real.log_le_log hpos habs

/-- **The exponent of Mertens' function is `Θ`**: `limsup_{x→∞} log|M(x)| / log x = Θ`, the exponent of
`ψ(x) − x` (round 469's `PsiExponent.limsup_expo`). -/
theorem limsup_mexpo : limsup mexpo atTop = Theta := by
  have hΘ := half_le_Theta
  have hb : IsBoundedUnder (· ≤ ·) atTop mexpo :=
    isBoundedUnder_of_eventually_le (eventually_mexpo_le one_pos)
  have hcb : IsCoboundedUnder (· ≤ ·) atTop mexpo :=
    IsCoboundedUnder.of_frequently_ge (frequently_le_mexpo (ε := Theta / 2) (by linarith) (by linarith))
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact limsup_le_of_le hcb ((eventually_mexpo_le (half_pos hε)).mono fun x hx => by linarith)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hm : 0 < min ε (Theta / 2) := lt_min hε (by linarith)
    have hm' : min ε (Theta / 2) < Theta := by linarith [min_le_right ε (Theta / 2)]
    have h := le_limsup_of_frequently_le (frequently_le_mexpo hm hm') hb
    linarith [min_le_left ε (Theta / 2)]

/-! ### The abscissa of convergence of `Σ μ(n) n^{−s}` -/

/-- **Conditional convergence from a bound on partial sums.** If `f(0) = 0` and `Σ_{k ≤ n} f(k) = O(n^r)`
with `0 ≤ r < Re s`, the partial sums of `Σ f(k) k^{−s}` converge. This is the proof of Mathlib's
`LSeries_eq_mul_integral` (Abel summation, `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) without its
hypothesis of absolute convergence, which it uses only to name the limit. -/
theorem tendsto_partialSum_of_isBigO {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re) (hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    ∃ l : ℂ, Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), LSeries.term f s k) atTop (𝓝 l) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Finset.Icc 0 n, f k = ∑ k ∈ Finset.Icc 1 n, f k := fun n ↦ by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by aesop), hf,
      zero_add, zero_add]
  simp_rw [← h₄] at hO
  simp_rw [Nat.range_succ_eq_Icc_zero, LSeries.term_def₀ hf, mul_comm (f _)]
  refine ⟨_, tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0) _
    hf h₃ ?_ ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)⟩
  · exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using! hr.trans_lt hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using! isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

/-- **A convergent Dirichlet series has small coefficient sums**: if the partial sums of `Σ f(k) k^{−s}`
converge, then `|Σ_{1 ≤ k ≤ m} f(k)| ≤ K m^{σ₁}` for every `σ₁ > 0` with `Re s ≤ σ₁` (Abel summation against
`t^s`, Mathlib's `sum_mul_eq_sub_integral_mul₀'`). -/
theorem norm_sum_le_of_tendsto {f : ℕ → ℂ} (hf : f 0 = 0) {s l : ℂ}
    (hl : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), LSeries.term f s k) atTop (𝓝 l))
    {σ₁ : ℝ} (hσ₁ : 0 < σ₁) (hsσ₁ : s.re ≤ σ₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, f k‖ ≤ K * (m : ℝ) ^ σ₁ := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hl)
  have hB' : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 0 n, LSeries.term f s k‖ ≤ B := fun n ↦ by
    rw [← Nat.range_succ_eq_Icc_zero]
    exact hB _ ⟨n, rfl⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hc : ∀ k : ℕ, ((k : ℝ) : ℂ) ^ s * LSeries.term f s k = f k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hf]
    · rw [LSeries.term_of_ne_zero hk]
      have hk' : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
      have : ((k : ℝ) : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hk' h.1
      push_cast at this ⊢
      field_simp
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, f k =
      ∑ k ∈ Finset.Icc 0 m, ((k : ℝ) : ℂ) ^ s * LSeries.term f s k := by
    intro m
    simp_rw [hc]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc m.zero_le, Finset.sum_insert (by aesop), hf, zero_add,
      zero_add]
  rcases eq_or_ne s 0 with rfl | hs0
  · refine ⟨B, hB0, fun m ↦ ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Real.zero_rpow hσ₁.ne']
    have h1 : 1 ≤ (m : ℝ) ^ σ₁ := Real.one_le_rpow (by exact_mod_cast hm) hσ₁.le
    rw [hsum m]
    simp only [cpow_zero, one_mul]
    calc _ ≤ B := hB' m
      _ ≤ B * (m : ℝ) ^ σ₁ := le_mul_of_one_le_right hB0 h1
  refine ⟨B + ‖s‖ * B / σ₁, by positivity, fun m ↦ ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Real.zero_rpow hσ₁.ne']
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) m, DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ s) t :=
    fun t ht ↦ differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne' hs0
  have hderiv : ∀ t : ℝ, 0 < t → deriv (fun x : ℝ ↦ (x : ℂ) ^ s) t = s * (t : ℂ) ^ (s - 1) :=
    fun t ht ↦ Complex.deriv_ofReal_cpow_const ht.ne' hs0
  have hcont : ContinuousOn (fun t : ℝ ↦ s * (t : ℂ) ^ (s - 1)) (Set.Icc (1 : ℝ) m) :=
    continuousOn_const.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const
      fun t ht ↦ ofReal_mem_slitPlane.2 (by linarith [ht.1]))
  have hint : IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ s) (Set.Icc (1 : ℝ) m) :=
    (hcont.congr fun t ht ↦ hderiv t (by linarith [ht.1])).integrableOn_Icc
  have habel := sum_mul_eq_sub_integral_mul₀' (fun k ↦ LSeries.term f s k) (by simp) m hdiff hint
  have hrpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (σ₁ - 1)) volume 1 m :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hmaj : IntegrableOn (fun t : ℝ ↦ ‖s‖ * B * t ^ (σ₁ - 1)) (Set.Ioc (1 : ℝ) m) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hm1).1 hrpow).const_mul _
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) m, deriv (fun x : ℝ ↦ (x : ℂ) ^ s) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LSeries.term f s k‖ ≤ ‖s‖ * B * ((m : ℝ) ^ σ₁ / σ₁) := by
    refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦ ?_)
      have ht0 : 0 < t := by linarith [ht.1]
      rw [hderiv t ht0, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (s - 1).re = s.re - 1 := by simp
      rw [hre]
      have h1 : t ^ (s.re - 1) ≤ t ^ (σ₁ - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)
      calc ‖s‖ * t ^ (s.re - 1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LSeries.term f s k‖
          ≤ ‖s‖ * t ^ (σ₁ - 1) * B := by gcongr; exact hB' _
        _ = ‖s‖ * B * t ^ (σ₁ - 1) := by ring
    · rw [integral_const_mul, ← intervalIntegral.integral_of_le hm1,
        integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.one_rpow]
      gcongr
      linarith
  have hmσ : (m : ℝ) ^ s.re ≤ (m : ℝ) ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hm1 hsσ₁
  rw [hsum m, habel]
  calc ‖((m : ℝ) : ℂ) ^ s * ∑ k ∈ Finset.Icc 0 m, LSeries.term f s k -
        ∫ t in Set.Ioc (1 : ℝ) m, deriv (fun x : ℝ ↦ (x : ℂ) ^ s) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LSeries.term f s k‖
      ≤ ‖((m : ℝ) : ℂ) ^ s * ∑ k ∈ Finset.Icc 0 m, LSeries.term f s k‖ +
        ‖∫ t in Set.Ioc (1 : ℝ) m, deriv (fun x : ℝ ↦ (x : ℂ) ^ s) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LSeries.term f s k‖ := norm_sub_le _ _
    _ ≤ (m : ℝ) ^ σ₁ * B + ‖s‖ * B * ((m : ℝ) ^ σ₁ / σ₁) := by
        gcongr
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith)]
        exact mul_le_mul hmσ (hB' m) (norm_nonneg _) (by positivity)
    _ = (B + ‖s‖ * B / σ₁) * (m : ℝ) ^ σ₁ := by ring

/-- **`Σ μ(n) n^{−s}` converges for `Re s > Θ`.** -/
theorem moebius_tendsto_of_Theta_lt {s : ℂ} (hs : Theta < s.re) :
    ∃ l : ℂ, Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), LSeries.term fμc s k) atTop (𝓝 l) := by
  have hη : 0 < (s.re - Theta) / 2 := by linarith
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, fμc k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (Theta + (s.re - Theta) / 2) := by
    have h := (mertens_isBigO_Theta hη).comp_tendsto tendsto_natCast_atTop_atTop
    have e : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, fμc k) = fun n : ℕ ↦ ((summ fμ (n : ℝ) : ℝ) : ℂ) := by
      funext n
      simp only [summ, Nat.floor_natCast, fμc]
      push_cast
      rfl
    rw [e]
    exact Complex.isBigO_ofReal_left.2 h
  exact tendsto_partialSum_of_isBigO fμc_zero (by linarith [half_le_Theta]) (by linarith) hO

/-- **`Σ μ(n) n^{−s}` diverges for `Re s < Θ`**: convergence would make `M(x) = O(x^{σ₁})` for some
`σ₁ < Θ` (`norm_sum_le_of_tendsto`), against `mertens_omega_Theta`. -/
theorem moebius_not_tendsto_of_lt_Theta {s : ℂ} (hs : s.re < Theta) (l : ℂ) :
    ¬ Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), LSeries.term fμc s k) atTop (𝓝 l) := by
  intro hl
  have hΘ := half_le_Theta
  set σ₁ : ℝ := (max s.re 0 + Theta) / 2 with hσ₁def
  have hm1 : s.re ≤ max s.re 0 := le_max_left _ _
  have hm2 : 0 ≤ max s.re 0 := le_max_right _ _
  have hm3 : max s.re 0 < Theta := max_lt hs (by linarith)
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₁s : s.re ≤ σ₁ := by linarith
  have hσ₁Θ : σ₁ < Theta := by linarith
  obtain ⟨K, hK0, hK⟩ := norm_sum_le_of_tendsto fμc_zero hl hσ₁0 hσ₁s
  obtain ⟨x, hx1, hx⟩ := (mertens_omega_Theta (η := Theta - σ₁) (by linarith) (by linarith) K 1).1
  rw [sub_sub_cancel] at hx
  have hx0 : 0 ≤ x := by linarith
  have hM : ((summ fμ x : ℝ) : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, fμc k := by
    simp only [summ, fμc]
    push_cast
    rfl
  have h1 := hK ⌊x⌋₊
  rw [← hM, Complex.norm_real, Real.norm_eq_abs] at h1
  have hbound : |summ fμ x| ≤ K * x ^ σ₁ :=
    h1.trans (by gcongr; exact Nat.floor_le hx0)
  linarith [le_abs_self (summ fμ x)]

/-- The abscissa of convergence of `Σ μ(n) n^{−s}`: the infimum of the real `σ` at which its partial
sums converge. -/
noncomputable def moebiusAbscissa : ℝ :=
  sInf {σ : ℝ | ∃ l : ℂ, Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), LSeries.term fμc σ k) atTop
    (𝓝 l)}

/-- **The abscissa of convergence of `Σ μ(n) n^{−s}` is `Θ`.** -/
theorem moebiusAbscissa_eq_Theta : moebiusAbscissa = Theta := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨Theta + 1, moebius_tendsto_of_Theta_lt (by simp)⟩
  · rintro σ ⟨l, hl⟩
    by_contra h
    exact moebius_not_tendsto_of_lt_Theta (by simpa using not_le.1 h) l hl
  · intro w hw
    exact ⟨(Theta + w) / 2, moebius_tendsto_of_Theta_lt (by simp; linarith), by linarith⟩

end MertensExponent

#print axioms MertensExponent.mertens_isBigO_of_zeroFree
#print axioms MertensExponent.mertens_isBigO_eleven_twelfths
#print axioms MertensExponent.mertens_isBigO_Theta
#print axioms MertensExponent.mertens_omega_Theta
#print axioms MertensExponent.rh_iff_Theta_eq_half
#print axioms MertensExponent.rh_iff_mertens
#print axioms MertensExponent.limsup_mexpo
#print axioms MertensExponent.moebius_tendsto_of_Theta_lt
#print axioms MertensExponent.moebius_not_tendsto_of_lt_Theta
#print axioms MertensExponent.moebiusAbscissa_eq_Theta
