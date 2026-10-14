import KubotaCuspPoincare

/-! # The Fourier coefficients of the Eisenstein series at the cusps `γ_t` and `0` (round 462)

S5f-15 of round 360's plan, part 3. Round 461's next step planned the Fourier coefficients of `E_s∘γ_t` and
the pairing of round 461's `Q_t` with `ũ_s`. This round proves both, and the same at the cusp `0`, with `γ_t`
round 460's `lowT t`, `S = (0, −1; 1, 0)`, `3P` round 389's period parallelogram of `3ℤ[ω]` and round 361's
`ĕ(w) = e^{4πi·Re w}`:

* **Twisted tiling** (`wtSum`, a definition; **`hasSum_integral_ebr_wt`**, **`tsum_lintegral_wt_ne_top`** and
  **`integral_ebr_wtSeries`**): for a weight `w` with `|w| ≤ 1`, `w(0, d) = 0` and
  `w(c, d + 3cu) = w(c, d)·ĕ(−ξ·3u)`, `ξ ≠ 0`, `Re s > 2` and `v > 0`,
  `∫_{3P} ĕ(−ξz)·E_w(z, v) dz = B_ξ(s, v)·Σ_c W(c)N(c)^{−s}` with `E_w = Σ_{(c, d)} w(c, d)(v/Q_z(c, d))^s`,
  `B_ξ(s, v) = (2π/Γ(s))(2π|ξ|)^{s−1}·v·K_{s−1}(4π|ξ|v)` and `W(c) = Σ_{r mod 3c} w(c, r)ĕ(ξr/c)`, by round
  428's argument (round 389's tiling, round 428's `integral_ebr_height_cpow`).
* **The cusp `γ_t`** (`wtCuspT`, `rowTEquiv` and `cuspSmT`, definitions; **`wtCuspT_add`** and
  **`integral_ebr_eis1_lowT`**, with `rowMul_lowT`, `cuspF_rowMul`, `eisTerm_slAct_lowT`, `eis1_slAct_lowT`,
  `norm_cuspF_le`, `not_bRow_lowT`, `wtCuspT_zero_fst`, `lowT_row_ne_zero` and `conj_chiT_of_class`): the term
  of `(c, d)` at `γ_t·p` is that of the row `(c + dt, d)` at `p` (round 387's `height_rowMul`), so
  `E(γ_t·p, s) = Σ_{(c, d)} w_t(c, d)(v/Q_p(c, d))^s` with `w_t(c, d) = cuspF(c − dt, d)` (round 414's
  `cuspF`). The row `(c − (d + 3cu)t, d + 3cu)` is `(c − dt, d)·γ_tT_{3u}γ_t⁻¹`, so
  `w_t(c, d + 3cu) = w_t(c, d)·conj χ_t(u)` (round 387's `cub_rowMul`, round 460's `chiT_eq_kub`), which is
  `w_t(c, d)·ĕ(−(m/9)·3u)` for `m` in the class of the cusp (round 461's `CuspClass`). For `t` a unit no row
  of `γγ_t` has `c = 0`. So for `m ≠ 0` in the class,
  `∫_{3P} ĕ(−mz/9)E(γ_t·(z, v), s) dz = (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·Σ_c S^t_m(c)N(c)^{−s}`
  with `S^t_m(c) = Σ_{d mod 3c} cuspF(c − dt, d)·ĕ((m/9)(d/c))`; there is no term `v^s`.
* **The cusp `0`** (`wtCusp0`, `rowSEquiv` and `cuspSm0`, definitions; **`integral_ebr_eis1_sS`**, with
  `eis1_slAct_sS'`, `cuspF_add_fst`, `wtCusp0_add` and `wtCusp0_zero_fst`): round 440's terms at `S·p` give
  `E(S·p, s) = Σ_{(c, d)} cuspF(−d, c)(v/Q_p(c, d))^s`, periodic in `d` modulo `3c`, and for `m = δ₃x ≠ 0`,
  `∫_{3P} ĕ(−mz/9)E(S·(z, v), s) dz = (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·Σ_c S⁰_m(c)N(c)^{−s}` with
  `S⁰_m(c) = Σ_{d mod 3c} cuspF(−d, c)·ĕ((m/9)(d/c))`.
* **The band at `g·p`** (**`eisHigh_slAct_eq_band`** and **`eisLow_slAct_eq_band`**, with `height_slAct_le`):
  for `g` sending no bottom row to `(0, *)`, every height at `g·p` is at most `1/v`, so
  `E_s − h_s = E_s − E(1[Y ≤ v ≤ H]v^s)` at `g·p` for `v ≥ α`, `H = Y + β + 1/α`, as round 442's
  `eisLow_sS_eq_band`.
* **The pairings for `Re s > 2`** (`pmSerS`, a definition; **`inner_pmSerC_uL`**, **`inner_toLp_pmSerS`** and
  **`inner_pmSerS_uL`**, with `enorm_comp_lowT`, `setLIntegral_lowT_lt_top`, `lintegral_rhoT3_pmC_ne_top`,
  `setLIntegral_conj_ebr_mul`, `isAut_pmSerS` and `memLp_pmSerS`): for `ψ` measurable and bounded, vanishing
  outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
  `⟨Q_t(ψ), ũ_s⟩ = (2π/Γ(s))(2π|m|/9)^{s−1}·(Σ_c S^t_m(c)N(c)^{−s})·J_ψ(s) − ⟨Q_t(ψ), E(1[Y ≤ v ≤ H]v^s)⟩`
  (round 461's `inner_toLp_pmSerC`), and the same at the cusp `0` for `P_m(ψ)∘S⁻¹` with `S⁰_m` (round 429's
  `integral_conj_pmSer_mul`, round 442's `integral_conj_sS_inv_mul`), with round 430's `J_ψ`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Twisted tiling -/

open Classical in
/-- **The twisted sum of a weight over the classes modulo `3c`**: `Σ_{r mod 3c} F(r)·ĕ(ξr/c)`. -/
def wtSum (F : 𝓞 K → ℂ) (ξ : ℂ) (c : 𝓞 K) : ℂ :=
  ∑' r : 𝓞 K ⧸ span {3 * c}, F (repQ (3 * c) r) * ebr (ξ * (σO (repQ (3 * c) r) / σO c))

/-- **Twisted tiling**: for `c ≠ 0`, `ξ ≠ 0`, `v > 0`, `Re s > 1` and a weight `F` with `|F| ≤ 1` and
`F(d + 3cu) = F(d)·ĕ(−ξ·3u)`, `Σ_d ∫_{3P} ĕ(−ξz)·F(d)·(v/Q_z(c, d))^s dz = W·|c|^{−2s}·B_ξ(s, v)` with
`W = Σ_{r mod 3c} F(r)ĕ(ξr/c)` and `B_ξ(s, v) = (2π/Γ(s))(2π|ξ|)^{s−1}·v·K_{s−1}(4π|ξ|v)`. -/
theorem hasSum_integral_ebr_wt {c : 𝓞 K} (hc : c ≠ 0) {ξ : ℂ} (hξ : ξ ≠ 0) {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {F : 𝓞 K → ℂ} (hF1 : ∀ d, ‖F d‖ ≤ 1)
    (hFp : ∀ d u, F (d + 3 * c * u) = F d * ebr (-(ξ * σO (3 * u)))) :
    HasSum (fun d : 𝓞 K => ∫ z in fundP3, ebr (-(ξ * z)) *
        (F d * ((v / uhsDen (σO c) (σO d) z v : ℝ) : ℂ) ^ s))
      (wtSum F ξ c * (((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) *
        (2 * Real.pi / Gamma s * ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1)) * (v : ℂ) *
          besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v))) := by
  have := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  set Fi := fun d : 𝓞 K => ∫ z in fundP3, ebr (-(ξ * z)) *
    (F d * ((v / uhsDen (σO c) (σO d) z v : ℝ) : ℂ) ^ s) with hFi
  set G := fun d : 𝓞 K =>
    ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ s.re) with hG
  have hGtop : ∑' d, G d ≠ ⊤ := by
    rw [hG, tsum_lintegral_height_c hc hv hs]
    exact ENNReal.ofReal_ne_top
  have hB : ∀ d, ‖Fi d‖ ≤ (G d).toReal := by
    intro d
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.ne_top_of_tsum_ne_top hGtop d) (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_))
    have hpos : 0 < v / uhsDen (σO c) (σO d) z v :=
      div_pos hv (uhsDen_pos hv (Or.inl (σO_ne_zero hc)))
    rw [norm_mul, norm_ebr, one_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hpos.le _) (hF1 d)
  have hsum : Summable Fi := Summable.of_norm_bounded (ENNReal.summable_toReal hGtop) hB
  have hsum' : Summable fun p => Fi (resClassEquiv hc p) := (resClassEquiv hc).summable_iff.2 hsum
  rw [hsum.hasSum_iff, ← (resClassEquiv hc).tsum_eq, hsum'.tsum_prod' hsum'.prod_factor, tsum_fintype]
  unfold wtSum
  rw [tsum_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  set ρ := repQ (3 * c) r with hρ
  set f : ℂ → ℂ := fun z => ebr (-(ξ * z)) * (F ρ * ((v / uhsDen (σO c) (σO ρ) z v : ℝ) : ℂ) ^ s)
    with hf_def
  have hf : Integrable f := by
    have hm : Measurable fun z : ℂ => ebr (-(ξ * z)) := measurable_ebr.comp (by fun_prop)
    have hi : Integrable fun z : ℂ => F ρ * ((v / uhsDen (σO c) (σO ρ) z v : ℝ) : ℂ) ^ s :=
      (integrable_height_cpow (σO_ne_zero hc) _ hv hs).const_mul _
    refine hi.bdd_mul (c := 1) hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [norm_ebr]
  have h1 : ∀ u : 𝓞 K, Fi (resClassEquiv hc (r, u)) = ∫ y in fundP3, f (y - σO (3 * -u)) := by
    intro u
    simp only [hFi, resClassEquiv_apply, hf_def]
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [uhsDen_res, hFp, mul_neg, map_neg, sub_neg_eq_add,
      show -(ξ * (z + σO (3 * u))) = -(ξ * z) + -(ξ * σO (3 * u)) by ring, ebr_add]
    ring
  have h2 := (Equiv.neg (𝓞 K)).tsum_eq (fun t => ∫ y in fundP3, f (y - σO (3 * t)))
  simp only [Equiv.neg_apply] at h2
  rw [tsum_congr h1, h2, ← integral_tile3 hf]
  simp only [hf_def]
  simp_rw [mul_left_comm (ebr _)]
  rw [integral_const_mul, integral_ebr_height_cpow (σO_ne_zero hc) _ hv hξ hs]
  ring

open Classical in
/-- **The majorant for a weighted series**: for `|w| ≤ 1` with `w(0, d) = 0`, `Re s > 2` and `v > 0`,
`Σ_{(c, d)} ∫_{3P} |w(c, d)·(v/Q_z(c, d))^s| dz < ∞`. -/
theorem tsum_lintegral_wt_ne_top {w : 𝓞 K → 𝓞 K → ℂ} (hw1 : ∀ c d, ‖w c d‖ ≤ 1)
    (hw0 : ∀ d, w 0 d = 0) {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3,
      ‖w cd.1 cd.2 * ((v / uhsDen (σO cd.1) (σO cd.2) z v : ℝ) : ℂ) ^ s‖ₑ ≠ ⊤ := by
  set σ := s.re with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσ1' : 0 < σ - 1 := by linarith
  set B : ℝ≥0∞ := ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) / (σ - 1))
  have hslice : ∀ c : 𝓞 K, ∑' d : 𝓞 K, ∫⁻ z in fundP3,
      ‖w c d * ((v / uhsDen (σO c) (σO d) z v : ℝ) : ℂ) ^ s‖ₑ ≤
        B * (if c = 0 then 0 else ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2)))) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [hw0, zero_mul, enorm_zero, lintegral_zero, tsum_zero, ↓reduceIte, mul_zero, le_refl]
    · simp only [hc, ↓reduceIte]
      calc ∑' d : 𝓞 K, ∫⁻ z in fundP3, ‖w c d * ((v / uhsDen (σO c) (σO d) z v : ℝ) : ℂ) ^ s‖ₑ
          ≤ ∑' d : 𝓞 K, ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ σ) := by
            refine ENNReal.tsum_le_tsum fun d => lintegral_mono fun z => ?_
            rw [← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ?_
            have hpos : 0 < v / uhsDen (σO c) (σO d) z v :=
              div_pos hv (uhsDen_pos hv (Or.inl (σO_ne_zero hc)))
            rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
            exact mul_le_of_le_one_left (Real.rpow_nonneg hpos.le _) (hw1 c d)
        _ = ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) * Complex.normSq (σO c) ^ (1 - σ) / (σ - 1)) :=
            tsum_lintegral_height_c hc hv hσ1
        _ = B * ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2))) := by
            rw [← ENNReal.ofReal_mul (by positivity), rpow_normSq_eq]
            congr 1
            ring
  refine ne_top_of_le_ne_top ?_ ((ENNReal.tsum_prod').le.trans (ENNReal.tsum_le_tsum hslice))
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_norm_σO_rpow_le (by linarith)))

/-- **The Fourier coefficient of a weighted series**: for `|w| ≤ 1` with `w(0, d) = 0` and
`w(c, d + 3cu) = w(c, d)·ĕ(−ξ·3u)`, `ξ ≠ 0`, `Re s > 2` and `v > 0`,
`∫_{3P} ĕ(−ξz)·E_w(z, v) dz = B_ξ(s, v)·Σ_c W(c)N(c)^{−s}` with `E_w = Σ_{(c, d)} w(c, d)(v/Q_z(c, d))^s`,
`B_ξ(s, v) = (2π/Γ(s))(2π|ξ|)^{s−1}·v·K_{s−1}(4π|ξ|v)` and `W(c) = Σ_{r mod 3c} w(c, r)ĕ(ξr/c)`. -/
theorem integral_ebr_wtSeries {w : 𝓞 K → 𝓞 K → ℂ} (hw1 : ∀ c d, ‖w c d‖ ≤ 1)
    (hw0 : ∀ d, w 0 d = 0) {ξ : ℂ} (hξ : ξ ≠ 0)
    (hwp : ∀ c d u, w c (d + 3 * c * u) = w c d * ebr (-(ξ * σO (3 * u)))) {s : ℂ} (hs : 2 < s.re)
    {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(ξ * z)) *
        ∑' cd : 𝓞 K × 𝓞 K, w cd.1 cd.2 * ((v / uhsDen (σO cd.1) (σO cd.2) z v : ℝ) : ℂ) ^ s =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) *
        besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v) *
          ∑' c : 𝓞 K, wtSum (w c) ξ c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  set T := fun (z : ℂ) (cd : 𝓞 K × 𝓞 K) =>
    w cd.1 cd.2 * ((v / uhsDen (σO cd.1) (σO cd.2) z v : ℝ) : ℂ) ^ s with hT
  have hfin := tsum_lintegral_wt_ne_top hw1 hw0 hs hv
  have hm : Measurable fun z : ℂ => ebr (-(ξ * z)) := measurable_ebr.comp (by fun_prop)
  have hTm : ∀ cd, Measurable fun z => T z cd := by
    intro cd
    refine measurable_const.mul ?_
    have : Measurable fun z : ℂ => (v / uhsDen (σO cd.1) (σO cd.2) z v) := by
      unfold uhsDen
      fun_prop
    exact (Complex.measurable_ofReal.comp this).pow_const s
  set I := fun cd : 𝓞 K × 𝓞 K => ∫ z in fundP3, ebr (-(ξ * z)) * T z cd with hI
  have hfin' : ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3, ‖ebr (-(ξ * z)) * T z cd‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun cd => lintegral_mono fun z => ?_)
    rw [enorm_mul, ← ofReal_norm (ebr _), norm_ebr, ENNReal.ofReal_one, one_mul]
  have hI_le : ∀ cd, ‖I cd‖ ≤ (∫⁻ z in fundP3, ‖ebr (-(ξ * z)) * T z cd‖ₑ).toReal := by
    intro cd
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp_rw [ofReal_norm]
  have hIsum : Summable I := Summable.of_norm_bounded (ENNReal.summable_toReal hfin') hI_le
  have h1 : ∫ z in fundP3, ebr (-(ξ * z)) * ∑' cd, T z cd = ∑' cd, I cd := by
    have e : ∀ z, ebr (-(ξ * z)) * ∑' cd, T z cd = ∑' cd, ebr (-(ξ * z)) * T z cd := fun z => by
      rw [tsum_mul_left]
    simp_rw [e]
    exact integral_tsum (fun cd => (hm.mul (hTm cd)).aestronglyMeasurable) hfin'
  set J := fun c : 𝓞 K => ∑' d : 𝓞 K, I (c, d) with hJ
  have hJsum : Summable J := hIsum.prod
  have hJ0 : J 0 = 0 := by
    simp only [hJ, hI, hT, hw0, zero_mul, mul_zero, integral_zero, tsum_zero]
  have hJc : ∀ c : 𝓞 K, c ≠ 0 → J c = 2 * Real.pi / Gamma s *
      ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v) *
        (wtSum (w c) ξ c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) := by
    intro c hc
    show ∑' d : 𝓞 K, ∫ z in fundP3, ebr (-(ξ * z)) *
      (w c d * ((v / uhsDen (σO c) (σO d) z v : ℝ) : ℂ) ^ s) = _
    rw [(hasSum_integral_ebr_wt hc hξ hv (by linarith) (hw1 c) (hwp c)).tsum_eq]
    ring
  have hs0 : -s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [h1, hIsum.tsum_prod' hIsum.prod_factor]
  change ∑' c, J c = _
  rw [← tsum_mul_left]
  refine tsum_congr fun c => ?_
  by_cases hc : c = 0
  · rw [hc, hJ0, map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0]
    ring
  · exact hJc c hc

/-! ### The terms at `γ_t·p` -/

theorem rowMul_lowT (t c d : 𝓞 K) : rowMul (lowT t) (c, d) = (c + d * t, d) := by
  simp [rowMul, lowT]

/-- **The symbol along `Γ_1(3)`, with the condition**: `cuspF((c, d)g) = cuspF(c, d)·conj κ(g)`. -/
theorem cuspF_rowMul {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (cd : 𝓞 K × 𝓞 K) :
    cuspF (rowMul g cd).1 (rowMul g cd).2 = cuspF cd.1 cd.2 * conj (kub ↑g) := by
  unfold cuspF
  by_cases h : BRow cd
  · rw [ite_eq_left (bRow_rowMul hg h), ite_eq_left h, cub_rowMul hg h]
  · rw [ite_eq_right (fun h' => h ((bRow_rowMul_iff hg cd).1 h')), ite_eq_right h, zero_mul]

/-- **The weight at the cusp `γ_t`**: the row `(c, d)` of `γγ_t` carries `cuspF(c − dt, d)`. -/
def wtCuspT (t c d : 𝓞 K) : ℂ := cuspF (c - d * t) d

/-- **The terms at `γ_t·p`**: the term of `(c, d)` at `γ_t·p` is `cuspF(c, d)·(v/Q_p(c + dt, d))^s`. -/
theorem eisTerm_slAct_lowT (s : ℂ) (t : 𝓞 K) {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    eisTerm s (slAct (lowT t) p) cd =
      cuspF cd.1 cd.2 * ((p.2 / uhsDen (σO (cd.1 + cd.2 * t)) (σO cd.2) p.1 p.2 : ℝ) : ℂ) ^ s := by
  unfold eisTerm cuspF
  split_ifs with h
  · rw [height_rowMul (lowT t) h hp, show rowMul (lowT t) cd = (cd.1 + cd.2 * t, cd.2) from rowMul_lowT t _ _]
  · rw [zero_mul]

/-- The rows `(c + dt, d)`. -/
def rowTEquiv (t : 𝓞 K) : 𝓞 K × 𝓞 K ≃ 𝓞 K × 𝓞 K where
  toFun cd := (cd.1 + cd.2 * t, cd.2)
  invFun cd := (cd.1 - cd.2 * t, cd.2)
  left_inv cd := by simp
  right_inv cd := by simp

/-- **`E_s` at `γ_t·p`**: `E(γ_t·p, s) = Σ_{(c, d)} cuspF(c − dt, d)·(v/Q_p(c, d))^s`. -/
theorem eis1_slAct_lowT (s : ℂ) (t : 𝓞 K) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s (slAct (lowT t) p) = ∑' cd : 𝓞 K × 𝓞 K, wtCuspT t cd.1 cd.2 *
      ((p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 : ℝ) : ℂ) ^ s := by
  unfold eis1
  rw [← (rowTEquiv t).symm.tsum_eq]
  refine tsum_congr fun cd => ?_
  rw [eisTerm_slAct_lowT s t hp]
  simp only [rowTEquiv, Equiv.coe_fn_symm_mk, sub_add_cancel, wtCuspT]

/-- **The twisted periodicity of the weight**: `w_t(c, d + 3cu) = w_t(c, d)·conj χ_t(u)`, since
`(c − (d + 3cu)t, d + 3cu) = (c − dt, d)·γ_t T_{3u} γ_t⁻¹` (round 460's `cuspPar`). -/
theorem wtCuspT_add (t c d u : 𝓞 K) : wtCuspT t c (d + 3 * c * u) = wtCuspT t c d * conj (chiT t u) := by
  have e : rowMul (cuspPar t u) (c - d * t, d) = (c - (d + 3 * c * u) * t, d + 3 * c * u) := by
    simp only [rowMul, cuspPar_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Prod.mk.injEq]
    constructor <;> ring
  have h := cuspF_rowMul (cuspPar_mem t u) (c - d * t, d)
  rw [e] at h
  unfold wtCuspT
  rw [h, chiT_eq_kub]

theorem norm_cuspF_le (c d : 𝓞 K) : ‖cuspF c d‖ ≤ 1 := by
  unfold cuspF
  split_ifs with h
  · rw [norm_σO_cub h.2.2 h.1]
  · rw [norm_zero]; exact zero_le_one

/-- `(−dt, d)` is not a bottom row for `t` a unit: `3 ∣ dt` would give `3 ∣ d`, and `d ≡ 1 (mod 3)`. -/
theorem not_bRow_lowT {t : 𝓞 K} (ht : IsUnit t) (d : 𝓞 K) : ¬ BRow (0 - d * t, d) := by
  rintro ⟨-, h3, hd⟩
  obtain ⟨u, rfl⟩ := ht
  have h3d : (3 : 𝓞 K) ∣ d := by
    have : (3 : 𝓞 K) ∣ (0 - d * ↑u) * ↑u⁻¹ := dvd_mul_of_dvd_left h3 _
    rwa [zero_sub, neg_mul, mul_assoc, Units.mul_inv, mul_one, dvd_neg] at this
  exact not_three_dvd_one (by simpa using (dvd_sub h3d hd))

/-- **No row of `γγ_t` has `c = 0`.** -/
theorem wtCuspT_zero_fst {t : 𝓞 K} (ht : IsUnit t) (d : 𝓞 K) : wtCuspT t 0 d = 0 := by
  unfold wtCuspT cuspF
  exact ite_eq_right (not_bRow_lowT ht d)

/-- **`γ_t` sends no bottom row to `(0, *)`**: `c + dt ≠ 0` for `(c, d)` a bottom row and `t` a unit. -/
theorem lowT_row_ne_zero {t : 𝓞 K} (ht : IsUnit t) {cd : 𝓞 K × 𝓞 K} (hb : BRow cd) :
    (rowMul (lowT t) cd).1 ≠ 0 := by
  obtain ⟨c, d⟩ := cd
  rw [rowMul_lowT]
  intro h
  refine not_bRow_lowT ht d ?_
  rwa [show 0 - d * t = c by linear_combination -h]

open Classical in
/-- **The Kubota sums at the cusp `γ_t`**: `S^t_m(c) = Σ_{d mod 3c} cuspF(c − dt, d)·ĕ((m/9)(d/c))`. -/
def cuspSmT (t m c : 𝓞 K) : ℂ := wtSum (wtCuspT t c) (σO m / 9) c

/-- `conj χ_t(u) = ĕ(−(m/9)·3u)` for `m` in the class of the cusp. -/
theorem conj_chiT_of_class {t m : 𝓞 K} (hm : CuspClass t m) (u : 𝓞 K) :
    conj (chiT t u) = ebr (-(σO m / 9 * σO (3 * u))) := by
  rw [← hm u, conj_ebr]
  congr 1
  ring

/-- **The `m`-th Fourier coefficient of `E_s` at the cusp `γ_t`**: for `t` a unit, `m ≠ 0` in the class
of the cusp (round 461's `CuspClass`), `Re s > 2` and `v > 0`,
`∫_{3P} ĕ(−mz/9)E(γ_t·(z, v), s) dz = (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·Σ_c S^t_m(c)N(c)^{−s}`. -/
theorem integral_ebr_eis1_lowT {t m : 𝓞 K} (ht : IsUnit t) (hm : CuspClass t m) (hm0 : m ≠ 0) {s : ℂ}
    (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO m / 9 * z)) * eis1 s (slAct (lowT t) (z, v)) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO m / 9‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) *
        besselK (s - 1) (4 * Real.pi * ‖σO m / 9‖ * v) *
          ∑' c : 𝓞 K, cuspSmT t m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  have e : ∀ z : ℂ, eis1 s (slAct (lowT t) (z, v)) = ∑' cd : 𝓞 K × 𝓞 K, wtCuspT t cd.1 cd.2 *
      ((v / uhsDen (σO cd.1) (σO cd.2) z v : ℝ) : ℂ) ^ s := fun z =>
    eis1_slAct_lowT s t (p := (z, v)) hv
  simp_rw [e]
  exact integral_ebr_wtSeries (w := wtCuspT t) (fun c d => norm_cuspF_le _ _) (wtCuspT_zero_fst ht)
    (div_ne_zero (σO_ne_zero hm0) (by norm_num))
    (fun c d u => by rw [wtCuspT_add, conj_chiT_of_class hm]) hs hv

/-! ### The terms at `S·p` -/

/-- **The weight at the cusp `0`**: the row `(c, d)` of `γS` carries `cuspF(−d, c)`. -/
def wtCusp0 (c d : 𝓞 K) : ℂ := cuspF (-d) c

/-- The rows `(−d, c)`. -/
def rowSEquiv : 𝓞 K × 𝓞 K ≃ 𝓞 K × 𝓞 K where
  toFun cd := (-cd.2, cd.1)
  invFun cd := (cd.2, -cd.1)
  left_inv cd := by simp
  right_inv cd := by simp

/-- **`E_s` at `S·p`**: `E(S·p, s) = Σ_{(c, d)} cuspF(−d, c)·(v/Q_p(c, d))^s` (round 440's
`eis1_slAct_sS`, with the rows `(d, −c)`). -/
theorem eis1_slAct_sS' (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s (slAct sS p) = ∑' cd : 𝓞 K × 𝓞 K, wtCusp0 cd.1 cd.2 *
      ((p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 : ℝ) : ℂ) ^ s := by
  rw [eis1_slAct_sS s hp, ← rowSEquiv.tsum_eq]
  refine tsum_congr fun cd => ?_
  simp only [rowSEquiv, Equiv.coe_fn_mk, wtCusp0, cuspF, eisTermS, neg_neg]
  by_cases h : BRow (-cd.2, cd.1)
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, zero_mul]

theorem cuspF_add_fst (c d x : 𝓞 K) : cuspF (c + 3 * d * x) d = cuspF c d := by
  unfold cuspF
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_add_fst_iff x).2 h), ite_eq_left h,
      cub_congr (show d ∣ (c + 3 * d * x) - c from ⟨3 * x, by ring⟩)]
  · rw [ite_eq_right (fun h' => h ((bRow_add_fst_iff x).1 h')), ite_eq_right h]

theorem wtCusp0_add (c d u : 𝓞 K) : wtCusp0 c (d + 3 * c * u) = wtCusp0 c d := by
  unfold wtCusp0
  rw [show -(d + 3 * c * u) = -d + 3 * c * -u by ring, cuspF_add_fst]

theorem wtCusp0_zero_fst (d : 𝓞 K) : wtCusp0 0 d = 0 := by
  unfold wtCusp0 cuspF
  exact ite_eq_right fun h => primary_ne_zero h.2.2 rfl

open Classical in
/-- **The Kubota sums at the cusp `0`**: `S⁰_m(c) = Σ_{d mod 3c} cuspF(−d, c)·ĕ((m/9)(d/c))`. -/
def cuspSm0 (m c : 𝓞 K) : ℂ := wtSum (wtCusp0 c) (σO m / 9) c

/-- **The `m`-th Fourier coefficient of `E_s` at the cusp `0`**: for `m = δ₃x ≠ 0`, `Re s > 2` and `v > 0`,
`∫_{3P} ĕ(−mz/9)E(S·(z, v), s) dz = (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·Σ_c S⁰_m(c)N(c)^{−s}`. There
is no term `v^s`: every bottom row `(c, d)` has `d ≠ 0`. -/
theorem integral_ebr_eis1_sS {x : 𝓞 K} (hx : x ≠ 0) {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * eis1 s (slAct sS (z, v)) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) *
        besselK (s - 1) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v) *
          ∑' c : 𝓞 K, cuspSm0 (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  have e : ∀ z : ℂ, eis1 s (slAct sS (z, v)) = ∑' cd : 𝓞 K × 𝓞 K, wtCusp0 cd.1 cd.2 *
      ((v / uhsDen (σO cd.1) (σO cd.2) z v : ℝ) : ℂ) ^ s := fun z =>
    eis1_slAct_sS' s (p := (z, v)) hv
  simp_rw [e]
  refine integral_ebr_wtSeries (w := wtCusp0) (fun c d => norm_cuspF_le _ _) wtCusp0_zero_fst
    (div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)) (fun c d u => ?_) hs hv
  rw [wtCusp0_add, show -(σO (δ3 * x) / 9 * σO (3 * u)) = -(σO (δ3 * x) * σO (3 * u) / 9) by ring,
    ← conj_ebr, ebr_period, map_one, mul_one]

/-! ### The band at `g·p` -/

/-- **Every height at `g·p` is at most `1/v`** for a bottom row that `g` does not send to `(0, *)`. -/
theorem height_slAct_le {g : SL(2, 𝓞 K)} {cd : 𝓞 K × 𝓞 K} (hb : BRow cd) (hg : (rowMul g cd).1 ≠ 0)
    {p : ℂ × ℝ} (hp : p ∈ UHS) :
    (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ≤ 1 / p.2 := by
  rw [height_rowMul g hb hp]
  exact height_le_inv hg _ p.1 hp

/-- **`h_s` at `g·p` is a band series** when `g` sends no bottom row to `(0, *)`:
`h_s(g·p) = E(1[Y ≤ v ≤ Y + β + 1/α]v^s)(g·p)` for `α ≤ v` and `α ≤ β` (round 442's `eisHigh_sS_eq_band`). -/
theorem eisHigh_slAct_eq_band (s : ℂ) {g : SL(2, 𝓞 K)} (hg : ∀ cd, BRow cd → (rowMul g cd).1 ≠ 0)
    {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) (hαβ : α ≤ β) {p : ℂ × ℝ} (hαv : α ≤ p.2) :
    eisHigh s Y (slAct g p) = pseis (bandF s Y (Y + β + 1 / α)) (slAct g p) := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  unfold eisHigh pseis
  refine tsum_congr fun cd => ?_
  unfold psTerm
  split_ifs with hb
  · congr 1
    have hH : (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ≤
        Y + β + 1 / α := by
      have h1 := height_slAct_le hb (hg cd hb) hp
      have h2 : 1 / p.2 ≤ 1 / α := one_div_le_one_div_of_le hα hαv
      linarith
    unfold highF bandF
    by_cases hlt : (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 < Y
    · have hn : ¬ (Y ≤ (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ∧
          (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ≤ Y + β + 1 / α) :=
        fun h => not_le.2 hlt h.1
      simp only [hlt, hn, ↓reduceIte]
    · have hy : Y ≤ (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ∧
          (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 ≤ Y + β + 1 / α :=
        ⟨not_lt.1 hlt, hH⟩
      simp only [hlt, hy, and_self, ↓reduceIte]
  · rfl

/-- **`E_s − h_s = E_s − E(1[Y ≤ v ≤ H]v^s)` at `g·p`**, `H = Y + β + 1/α`, for `Re s > 2`, `α ≤ v`, `α ≤ β`
and `g` sending no bottom row to `(0, *)`. -/
theorem eisLow_slAct_eq_band {s : ℂ} (hs : 2 < s.re) {g : SL(2, 𝓞 K)}
    (hg : ∀ cd, BRow cd → (rowMul g cd).1 ≠ 0) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) (hαβ : α ≤ β)
    {p : ℂ × ℝ} (hαv : α ≤ p.2) :
    eisLow s Y (slAct g p) = eis1 s (slAct g p) - pseis (bandF s Y (Y + β + 1 / α)) (slAct g p) := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  rw [eis1_eq_eisLow_add_eisHigh hs Y (slAct_mem g hp), eisHigh_slAct_eq_band s hg hY hα hαβ hαv]
  ring

/-- `|u∘γ_t|` is invariant under `Γ_1(3)` when `|u|` is (round 460's `lowT_conj_mem`). -/
theorem enorm_comp_lowT {u : ℂ × ℝ → ℂ} (hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ)
    (t : 𝓞 K) : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct (lowT t) (slAct γ p))‖ₑ = ‖u (slAct (lowT t) p)‖ₑ := by
  intro γ hγ p hp
  rw [slAct_conj (lowT t) γ hp, hinv _ (lowT_conj_mem t hγ) _ (slAct_mem _ hp)]

/-- **An automorphic function in `L²(ν)`, moved by `γ_t`, is integrable on `3P × [α, β]`** against
`dz dv/v³` (round 432's `lintegral_boxZ_lt_top`, as round 442's `setLIntegral_sS_lt_top`). -/
theorem setLIntegral_lowT_lt_top (t : 𝓞 K) {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hu2 : MemLp u 2 (muR rhoG)) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫⁻ p in fundP3 ×ˢ Icc α β, ‖u (slAct (lowT t) p)‖ₑ ∂uhsMeasure < ⊤ := by
  have hm : Measurable fun p => u (slAct (lowT t) p) := hum.comp (measurable_slAct _)
  refine (lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
    p ∈ boxZ 6 α β))).trans_lt ?_
  exact lintegral_boxZ_lt_top hm (enorm_comp_lowT (enorm_slAct_of_isAut hu) t)
    (lintegral_enorm_comp_lt_top (lowT t) hum (enorm_slAct_of_isAut hu) hu2) 6 hα β

/-- **The finiteness for the unfolding of a twisted series**, from integrability on `3P × [α, β]`. -/
theorem lintegral_rhoT3_pmC_ne_top (m : 𝓞 K) {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) {G : ℂ × ℝ → ℂ} (hGm : Measurable G)
    (hG : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖G p‖ₑ ∂uhsMeasure < ⊤) :
    ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ₑ ∂uhsMeasure ≠ ⊤ := by
  have e : ∀ p : ℂ × ℝ, ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * G p‖ₑ = ‖conj (ψ p.2) * G p‖ₑ := by
    intro p
    rw [map_mul, enorm_mul, enorm_mul, enorm_mul, ← ofReal_norm (conj (ebr _)), Complex.norm_conj, norm_ebr,
      ENNReal.ofReal_one, mul_one]
  simp_rw [e]
  exact lintegral_rhoT3_ps_ne_top hM hψ0 hGm hG

/-- `|conj ĕ(mz/9)·G| = |G|`, integrated over `3P × [α, β]`. -/
theorem setLIntegral_conj_ebr_mul (m : 𝓞 K) {G : ℂ × ℝ → ℂ} {T : Set (ℂ × ℝ)} :
    ∫⁻ p in T, ‖conj (ebr (σO m * p.1 / 9)) * G p‖ₑ ∂uhsMeasure = ∫⁻ p in T, ‖G p‖ₑ ∂uhsMeasure := by
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, ← ofReal_norm (conj (ebr _)), Complex.norm_conj, norm_ebr, ENNReal.ofReal_one, one_mul]

/-! ### The pairing of `Q_t` with `ũ_s` -/

/-- **The pairing of `Q_t` with `ũ_s` for `Re s > 2`**: for `t` a unit, `m ≠ 0` in the class of the cusp,
`R ≥ 0`, `Y > 0`, `ψ` measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
`⟨Q_t(ψ), ũ_s⟩ = (2π/Γ(s))(2π|m|/9)^{s−1}·(Σ_c S^t_m(c)N(c)^{−s})·J_ψ(s) − ⟨Q_t(ψ), E(1[Y ≤ v ≤ H]v^s)⟩`
with `J_ψ = jPsi (4π|m|/9) ψ` and `H = Y + β + 1/α`. -/
theorem inner_pmSerC_uL {t m : 𝓞 K} (ht : IsUnit t) (hm : CuspClass t m) (hm0 : m ≠ 0) {R : ℝ}
    (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSerC t m ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat R s).im ≠ 0) :
    inner ℂ (hψ2.toLp (pmSerC t m ψ)) (uL R hR Y hY s) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO m / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSmT t m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          jPsi (4 * Real.pi * ‖σO m / 9‖) ψ s -
        inner ℂ (hψ2.toLp (pmSerC t m ψ)) (bandL hY (le_band hα hαβ) s) := by
  set H := Y + β + 1 / α
  have hg : ∀ cd, BRow cd → (rowMul (lowT t) cd).1 ≠ 0 := fun cd hb => lowT_row_ne_zero ht hb
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hLm : Measurable (eisLow s Y) := measurable_eisLow s Y
  have hBm : Measurable (pseis (bandF s Y H)) := measurable_pseis (measurable_bandF s Y H)
  have hEm : Measurable (eis1 s) := by
    rw [eis1_eq_pseis]
    exact measurable_pseis (Complex.measurable_ofReal.pow_const s)
  have hL2 := memLp_eisLow hs hY.le
  have hB2 := memLp_pseis_bandF s hY (le_band hα hαβ)
  have hLfin := setLIntegral_lowT_lt_top t hLm (isAut_eisLow s Y) hL2 hα β
  have hBfin := setLIntegral_lowT_lt_top t hBm (isAut_pseis _) hB2 hα β
  have hLSm : Measurable fun p => eisLow s Y (slAct (lowT t) p) := hLm.comp (measurable_slAct _)
  have hBSm : Measurable fun p => pseis (bandF s Y H) (slAct (lowT t) p) := hBm.comp (measurable_slAct _)
  have hESm : Measurable fun p => eis1 s (slAct (lowT t) p) := hEm.comp (measurable_slAct _)
  have hEfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct (lowT t) p)‖ₑ ∂uhsMeasure < ⊤ := by
    calc ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct (lowT t) p)‖ₑ ∂uhsMeasure
        ≤ ∫⁻ p in fundP3 ×ˢ Icc α β, (‖eisLow s Y (slAct (lowT t) p)‖ₑ +
            ‖pseis (bandF s Y H) (slAct (lowT t) p)‖ₑ) ∂uhsMeasure := by
          refine setLIntegral_mono (hLSm.enorm.add hBSm.enorm) fun p hp => ?_
          rw [show eis1 s (slAct (lowT t) p) = eisLow s Y (slAct (lowT t) p) +
              pseis (bandF s Y H) (slAct (lowT t) p) by
            rw [eisLow_slAct_eq_band hs hg hY hα hαβ hp.2.1]; ring]
          exact enorm_add_le _ _
      _ = (∫⁻ p in fundP3 ×ˢ Icc α β, ‖eisLow s Y (slAct (lowT t) p)‖ₑ ∂uhsMeasure) +
            ∫⁻ p in fundP3 ×ˢ Icc α β, ‖pseis (bandF s Y H) (slAct (lowT t) p)‖ₑ ∂uhsMeasure :=
          lintegral_add_left hLSm.enorm _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hLfin, hBfin⟩
  -- the character
  have hme : Measurable fun p : ℂ × ℝ => conj (ebr (σO m * p.1 / 9)) :=
    Complex.continuous_conj.measurable.comp
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9))
  set FE : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * eis1 s (slAct (lowT t) p) with hFE
  set FB : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * pseis (bandF s Y H) (slAct (lowT t) p)
    with hFB
  have hFEm : Measurable FE := hme.mul hESm
  have hFBm : Measurable FB := hme.mul hBSm
  have hFEfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FE p‖ₑ ∂uhsMeasure < ⊤ := by
    rw [hFE, setLIntegral_conj_ebr_mul]
    exact hEfin
  have hFBfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FB p‖ₑ ∂uhsMeasure < ⊤ := by
    rw [hFB, setLIntegral_conj_ebr_mul]
    exact hBfin
  have hFEint : IntegrableOn FE (fundP3 ×ˢ Icc α β) := by
    refine ⟨hFEm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FE p‖ₑ < ⊤
    exact (setLIntegral_volume_le hFEm.enorm hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFEfin)
  rw [uL_eq_eisLow hR hY hs him,
    inner_toLp_pmSerC hm hψ hψ2 (isAut_eisLow s Y) hLm hL2 (lintegral_rhoT3_pmC_ne_top m hM hψ0 hLSm hLfin),
    bandL, inner_toLp_pmSerC hm hψ hψ2 (isAut_pseis _) hBm hB2
      (lintegral_rhoT3_pmC_ne_top m hM hψ0 hBSm hBfin)]
  have h1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) *
      eisLow s Y (slAct (lowT t) p) ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, (conj (ψ p.2) * FE p - conj (ψ p.2) * FB p) ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFE, hFB]
    by_cases hv : p.2 ∈ Icc α β
    · rw [eisLow_slAct_eq_band hs hg hY hα hαβ hv.1, map_mul]
      ring
    · simp [hψ0 _ hv]
  have h2 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) *
      pseis (bandF s Y H) (slAct (lowT t) p) ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * FB p ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFB]
    rw [map_mul]
    ring
  rw [h1, h2, integral_sub (integrableOn_fundP3_of_lintegral hψ hM hψ0 hFEm hFEfin)
      (integrableOn_fundP3_of_lintegral hψ hM hψ0 hFBm hFBfin),
    integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hFEm hFEint]
  congr 1
  have he : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, FE (z, v) =
      ∫ v in Ioi 0, 2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO m / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSmT t m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          (conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) *
            besselK (s - 1) (4 * Real.pi * ‖σO m / 9‖ * v))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hc : ∫ z in fundP3, FE (z, v) =
        ∫ z in fundP3, ebr (-(σO m / 9 * z)) * eis1 s (slAct (lowT t) (z, v)) := by
      refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
      simp only [hFE]
      rw [conj_ebr]
      congr 2
      ring
    rw [hc, integral_ebr_eis1_lowT ht hm hm0 hs hv']
    have e2 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) = ((v ^ (-2 : ℤ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [show (-2 : ℤ) = -3 + 1 by norm_num, zpow_add₀ hv'.ne', zpow_one]
    rw [← e2]
    ring
  rw [he, integral_const_mul]
  rfl

/-! ### The twisted Poincaré series at the cusp `0` -/

/-- **`P_m(ψ)∘S⁻¹`, the twisted Poincaré series at the cusp `0`.** -/
def pmSerS (m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := pmSer m ψ (slAct sS⁻¹ p)

theorem isAut_pmSerS (x : 𝓞 K) (ψ : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pmSerS (δ3 * x) ψ) :=
  isAut_comp_sS_inv (isAut_pmSer x ψ)

theorem memLp_pmSerS {x : 𝓞 K} {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) : MemLp (pmSerS (δ3 * x) ψ) 2 (muR rhoG) :=
  memLp_comp sS⁻¹ (measurable_pmSer _ hψ) (enorm_slAct_of_isAut (isAut_pmSer x ψ)) hψ2

/-- **The pairing with the series at `0`, unfolded**: for `w` measurable, automorphic and in `L²(ν)`,
`⟨P_m(ψ)∘S⁻¹, w⟩ = ∫_{3P×(0,∞)} conj(ψ(v)ĕ(mz/9))·w(S·(z, v)) dz dv/v³` (round 429's
`integral_conj_pmSer_mul`, round 442's `integral_conj_sS_inv_mul`). -/
theorem inner_toLp_pmSerS {x : 𝓞 K} {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {w : ℂ × ℝ → ℂ}
    (hw : IsAut Gam3 (fun g => kub ↑g) w) (hwm : Measurable w) (hw2 : MemLp w 2 (muR rhoG))
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * w (slAct sS p)‖ₑ
      ∂uhsMeasure ≠ ⊤) :
    inner ℂ ((memLp_pmSerS hψ hψ2).toLp (pmSerS (δ3 * x) ψ)) (hw2.toLp w) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * w (slAct sS p)
        ∂uhsMeasure := by
  have hS2 := memLp_pmSerS (x := x) hψ hψ2
  have hpm : Measurable (pmSer (δ3 * x) ψ) := measurable_pmSer _ hψ
  have hint : ∫⁻ p, ‖conj (pmSer (δ3 * x) ψ (slAct sS⁻¹ p)) * w p‖ₑ ∂(muR rhoG) < ⊤ := by
    have h1 : MemLp (fun p => conj (pmSerS (δ3 * x) ψ p)) 2 (muR rhoG) :=
      hS2.of_le ((Complex.continuous_conj.measurable.comp
        (hpm.comp (measurable_slAct _))).aestronglyMeasurable)
        (Eventually.of_forall fun p => by rw [Complex.norm_conj])
    exact (h1.integrable_mul hw2).2
  rw [L2.inner_def, ← integral_conj_pmSer_mul hψ (isAut_comp_sS hw) (hwm.comp (measurable_slAct _)) hfin,
    ← integral_conj_sS_inv_mul hpm hwm (isAut_pmSer x ψ) hw hint]
  refine integral_congr_ae ?_
  filter_upwards [hS2.coeFn_toLp, hw2.coeFn_toLp] with p h1 h2
  rw [RCLike.inner_apply', h1, h2]
  rfl

/-- **The pairing of `P_m(ψ)∘S⁻¹` with `ũ_s` for `Re s > 2`**: for `m = δ₃x ≠ 0`, `R ≥ 0`, `Y > 0`, `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
`⟨P_m(ψ)∘S⁻¹, ũ_s⟩ = A_m(s)·(Σ_c S⁰_m(c)N(c)^{−s})·J_ψ(s) − ⟨P_m(ψ)∘S⁻¹, E(1[Y ≤ v ≤ H]v^s)⟩` with
`A_m(s) = (2π/Γ(s))(2π|m|/9)^{s−1}` with `J_ψ = jPsi (4π|m|/9) ψ` and `H = Y + β + 1/α`. -/
theorem inner_pmSerS_uL {x : 𝓞 K} (hx : x ≠ 0) {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ}
    (hs : 2 < s.re) (him : (hhat R s).im ≠ 0) :
    inner ℂ ((memLp_pmSerS hψ hψ2).toLp (pmSerS (δ3 * x) ψ)) (uL R hR Y hY s) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSm0 (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ s -
        inner ℂ ((memLp_pmSerS hψ hψ2).toLp (pmSerS (δ3 * x) ψ)) (bandL hY (le_band hα hαβ) s) := by
  set H := Y + β + 1 / α
  set m := δ3 * x with hmdef
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hLm : Measurable (eisLow s Y) := measurable_eisLow s Y
  have hBm : Measurable (pseis (bandF s Y H)) := measurable_pseis (measurable_bandF s Y H)
  have hEm : Measurable (eis1 s) := by
    rw [eis1_eq_pseis]
    exact measurable_pseis (Complex.measurable_ofReal.pow_const s)
  have hL2 := memLp_eisLow hs hY.le
  have hB2 := memLp_pseis_bandF s hY (le_band hα hαβ)
  have hLfin := setLIntegral_sS_lt_top hLm (isAut_eisLow s Y) hL2 hα β
  have hBfin := setLIntegral_sS_lt_top hBm (isAut_pseis _) hB2 hα β
  have hLSm : Measurable fun p => eisLow s Y (slAct sS p) := hLm.comp (measurable_slAct _)
  have hBSm : Measurable fun p => pseis (bandF s Y H) (slAct sS p) := hBm.comp (measurable_slAct _)
  have hESm : Measurable fun p => eis1 s (slAct sS p) := hEm.comp (measurable_slAct _)
  have hEfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct sS p)‖ₑ ∂uhsMeasure < ⊤ := by
    calc ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct sS p)‖ₑ ∂uhsMeasure
        ≤ ∫⁻ p in fundP3 ×ˢ Icc α β, (‖eisLow s Y (slAct sS p)‖ₑ +
            ‖pseis (bandF s Y H) (slAct sS p)‖ₑ) ∂uhsMeasure := by
          refine setLIntegral_mono (hLSm.enorm.add hBSm.enorm) fun p hp => ?_
          rw [show eis1 s (slAct sS p) = eisLow s Y (slAct sS p) + pseis (bandF s Y H) (slAct sS p) by
            rw [eisLow_sS_eq_band hs hY hα hαβ hp.2.1]; ring]
          exact enorm_add_le _ _
      _ = (∫⁻ p in fundP3 ×ˢ Icc α β, ‖eisLow s Y (slAct sS p)‖ₑ ∂uhsMeasure) +
            ∫⁻ p in fundP3 ×ˢ Icc α β, ‖pseis (bandF s Y H) (slAct sS p)‖ₑ ∂uhsMeasure :=
          lintegral_add_left hLSm.enorm _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hLfin, hBfin⟩
  have hme : Measurable fun p : ℂ × ℝ => conj (ebr (σO m * p.1 / 9)) :=
    Complex.continuous_conj.measurable.comp
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9))
  set FE : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * eis1 s (slAct sS p) with hFE
  set FB : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * pseis (bandF s Y H) (slAct sS p)
    with hFB
  have hFEm : Measurable FE := hme.mul hESm
  have hFBm : Measurable FB := hme.mul hBSm
  have hFEfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FE p‖ₑ ∂uhsMeasure < ⊤ := by
    rw [hFE, setLIntegral_conj_ebr_mul]
    exact hEfin
  have hFBfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FB p‖ₑ ∂uhsMeasure < ⊤ := by
    rw [hFB, setLIntegral_conj_ebr_mul]
    exact hBfin
  have hFEint : IntegrableOn FE (fundP3 ×ˢ Icc α β) := by
    refine ⟨hFEm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖FE p‖ₑ < ⊤
    exact (setLIntegral_volume_le hFEm.enorm hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFEfin)
  rw [uL_eq_eisLow hR hY hs him,
    inner_toLp_pmSerS hψ hψ2 (isAut_eisLow s Y) hLm hL2 (lintegral_rhoT3_pmC_ne_top m hM hψ0 hLSm hLfin),
    bandL, inner_toLp_pmSerS hψ hψ2 (isAut_pseis _) hBm hB2
      (lintegral_rhoT3_pmC_ne_top m hM hψ0 hBSm hBfin)]
  have h1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) *
      eisLow s Y (slAct sS p) ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, (conj (ψ p.2) * FE p - conj (ψ p.2) * FB p) ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFE, hFB]
    by_cases hv : p.2 ∈ Icc α β
    · rw [eisLow_sS_eq_band hs hY hα hαβ hv.1, map_mul]
      ring
    · simp [hψ0 _ hv]
  have h2 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) *
      pseis (bandF s Y H) (slAct sS p) ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * FB p ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFB]
    rw [map_mul]
    ring
  rw [h1, h2, integral_sub (integrableOn_fundP3_of_lintegral hψ hM hψ0 hFEm hFEfin)
      (integrableOn_fundP3_of_lintegral hψ hM hψ0 hFBm hFBfin),
    integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hFEm hFEint]
  congr 1
  have he : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, FE (z, v) =
      ∫ v in Ioi 0, 2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO m / 9‖ : ℝ) : ℂ) ^ (s - 1) *
          (∑' c : 𝓞 K, cuspSm0 m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) *
          (conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) *
            besselK (s - 1) (4 * Real.pi * ‖σO m / 9‖ * v))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hc : ∫ z in fundP3, FE (z, v) =
        ∫ z in fundP3, ebr (-(σO m / 9 * z)) * eis1 s (slAct sS (z, v)) := by
      refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
      simp only [hFE]
      rw [conj_ebr]
      congr 2
      ring
    rw [hc, hmdef, integral_ebr_eis1_sS hx hs hv']
    have e2 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) = ((v ^ (-2 : ℤ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [show (-2 : ℤ) = -3 + 1 by norm_num, zpow_add₀ hv'.ne', zpow_one]
    rw [← e2]
    ring
  rw [he, integral_const_mul]
  rfl

end Eis

end

#print axioms Eis.hasSum_integral_ebr_wt
#print axioms Eis.tsum_lintegral_wt_ne_top
#print axioms Eis.integral_ebr_wtSeries
#print axioms Eis.rowMul_lowT
#print axioms Eis.cuspF_rowMul
#print axioms Eis.eisTerm_slAct_lowT
#print axioms Eis.eis1_slAct_lowT
#print axioms Eis.wtCuspT_add
#print axioms Eis.norm_cuspF_le
#print axioms Eis.not_bRow_lowT
#print axioms Eis.wtCuspT_zero_fst
#print axioms Eis.lowT_row_ne_zero
#print axioms Eis.conj_chiT_of_class
#print axioms Eis.integral_ebr_eis1_lowT
#print axioms Eis.eis1_slAct_sS'
#print axioms Eis.cuspF_add_fst
#print axioms Eis.wtCusp0_add
#print axioms Eis.wtCusp0_zero_fst
#print axioms Eis.integral_ebr_eis1_sS
#print axioms Eis.height_slAct_le
#print axioms Eis.eisHigh_slAct_eq_band
#print axioms Eis.eisLow_slAct_eq_band
#print axioms Eis.enorm_comp_lowT
#print axioms Eis.setLIntegral_lowT_lt_top
#print axioms Eis.lintegral_rhoT3_pmC_ne_top
#print axioms Eis.setLIntegral_conj_ebr_mul
#print axioms Eis.inner_pmSerC_uL
#print axioms Eis.isAut_pmSerS
#print axioms Eis.memLp_pmSerS
#print axioms Eis.inner_toLp_pmSerS
#print axioms Eis.inner_pmSerS_uL
