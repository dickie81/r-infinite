import KubotaThetaConst

/-! # The growth of θ's Fourier coefficients (round 434)

S5f-10 of round 360's plan, part 17 (S5f-10f, seventh part). Round 433's next step planned a growth bound for
the coefficients `ρ(m)` of θ (round 431's `rhoM`). This round proves it, for `r > 0` and `Y > 0`:

* **Counting** (**`tsum_normSq_le_le`** and **`cBox_le`**): `#{x ∈ ℤ[ω] : |σ(x)|² ≤ R} ≤ (4R + 3)²` for
  `R ≥ 0`, through the coordinates of round 294's `crd` as in the proof of round 385's `finite_normSq_le`; so
  round 432's count `cBox(α)` of bottom rows is at most `(11/α)²(147/α²)²` for `0 < α ≤ 1`.
* **The growth of `ρ(m)`** (**`norm_rhoM_le`**, with `bkR_anti`): there is `C` with `|ρ(m)| ≤ C·|m|⁵` for
  every `m = δ₃x ≠ 0`. With `v₀ = 9/(4π|m|)`, the coefficient `∫_{3P} ĕ(−mz/9)θ̃(z, v) dz` is
  `ρ(m)·v·K_{1/3}(4π|m|v/9)` for almost every `v > 0` (round 432's `coef_thetaF_ae`), of absolute value at
  least `|ρ(m)|·v₀·K_{1/3}(2)` on `[v₀, 2v₀]`, since `K_{1/3}` decreases. Its integral over `[v₀, 2v₀]` is at
  most `(2v₀)³` times the integral of `|θ̃|` over the box `{|z| ≤ 6, v₀ ≤ v ≤ 2v₀}` against `dz dv/v³`, and
  round 432's `lintegral_boxZ_le` bounds that by `cTr(6)·cBox(v₀)·∫|θ̃| dν`, at most a constant times
  `v₀^{−6}`. So `|ρ(m)|·v₀² ≤ C′·v₀^{−3}`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Counting lattice points -/

/-- **Lattice points in a disc**: `#{x ∈ ℤ[ω] : |σ(x)|² ≤ R} ≤ (4R + 3)²` for `R ≥ 0`. -/
theorem tsum_normSq_le_le {R : ℝ} (hR : 0 ≤ R) :
    ∑' x : 𝓞 K, {x : 𝓞 K | Complex.normSq (σO x) ≤ R}.indicator (1 : 𝓞 K → ℝ≥0∞) x ≤
      ENNReal.ofReal ((4 * R + 3) ^ 2) := by
  set K' : ℤ := ⌈2 * R⌉ with hK'
  set B : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-K') K' with hB
  have key : ∀ m : ℤ, (m : ℝ) ^ 2 ≤ 2 * R → m ∈ Finset.Icc (-K') K' := by
    intro m hm
    have habs : ((|m| : ℤ) : ℝ) ≤ 2 * R := by
      have : ((|m| : ℤ) : ℝ) ≤ (m : ℝ) ^ 2 := by
        rw [Int.cast_abs]
        rcases eq_or_ne m 0 with rfl | hm0
        · simp
        · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
          calc |(m : ℝ)| ≤ |(m : ℝ)| * |(m : ℝ)| := le_mul_of_one_le_left (abs_nonneg _) h1
            _ = (m : ℝ) ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
      linarith
    have hc : (|m| : ℤ) ≤ K' := by
      have := Int.le_ceil (2 * R)
      exact_mod_cast habs.trans this
    exact Finset.mem_Icc.2 ⟨by linarith [neg_abs_le m], le_trans (le_abs_self m) hc⟩
  have hmem : ∀ n : Fin 2 → ℤ, Complex.normSq (σO (crd n)) ≤ R → n ∈ B := by
    intro n hn
    rw [normSq_σO_crd] at hn
    have h0 : ((n 0 : ℝ)) ^ 2 ≤ 2 * R := by nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
    have h1 : ((n 1 : ℝ)) ^ 2 ≤ 2 * R := by nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
    refine Fintype.mem_piFinset.2 fun i => ?_
    fin_cases i
    · exact key _ h0
    · exact key _ h1
  have hK0 : 0 ≤ K' := Int.ceil_nonneg (by linarith)
  have hcard : (B.card : ℝ) = (2 * (K' : ℝ) + 1) ^ 2 := by
    have hc : B.card = ((2 * K' + 1).toNat) ^ 2 := by
      rw [hB, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Int.card_Icc, show K' + 1 - -K' = 2 * K' + 1 by ring]
    have h : (((2 * K' + 1).toNat : ℤ)) = 2 * K' + 1 := Int.toNat_of_nonneg (by linarith)
    rw [hc]
    push_cast
    rw [← Int.cast_natCast (R := ℝ), h]
    push_cast
    ring
  have hKle : (K' : ℝ) ≤ 2 * R + 1 := (Int.ceil_lt_add_one (2 * R)).le
  calc ∑' x : 𝓞 K, {x : 𝓞 K | Complex.normSq (σO x) ≤ R}.indicator (1 : 𝓞 K → ℝ≥0∞) x
      = ∑' n : Fin 2 → ℤ, {x : 𝓞 K | Complex.normSq (σO x) ≤ R}.indicator (1 : 𝓞 K → ℝ≥0∞)
          (crdEquiv n) := (crdEquiv.tsum_eq _).symm
    _ ≤ ∑' n : Fin 2 → ℤ, (B : Set (Fin 2 → ℤ)).indicator (1 : (Fin 2 → ℤ) → ℝ≥0∞) n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        by_cases h : crdEquiv n ∈ {x : 𝓞 K | Complex.normSq (σO x) ≤ R}
        · rw [indicator_of_mem h, indicator_of_mem (show n ∈ (B : Set (Fin 2 → ℤ)) from hmem n h)]
          simp
        · rw [indicator_of_notMem h]
          exact zero_le
    _ = (B.card : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := B) fun n hn => indicator_of_notMem (by simpa using hn) _]
        rw [Finset.sum_congr rfl fun n hn => indicator_of_mem (Finset.mem_coe.2 hn) _]
        simp
    _ ≤ ENNReal.ofReal ((4 * R + 3) ^ 2) := by
        rw [← ENNReal.ofReal_natCast, hcard]
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ 2 * (K' : ℝ) + 1 := by have : (0 : ℝ) ≤ K' := by exact_mod_cast hK0
                                          linarith
        exact pow_le_pow_left₀ this (by linarith) 2

/-- **`#rowBd(α) ≤ (11/α)²(147/α²)²`** for `0 < α ≤ 1`. -/
theorem cBox_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    cBox α ≤ ENNReal.ofReal ((11 / α) ^ 2 * (147 / α ^ 2) ^ 2) := by
  set Sc : Set (𝓞 K) := {x | Complex.normSq (σO x) ≤ 2 / α} with hSc
  set Sd : Set (𝓞 K) := {x | Complex.normSq (σO x) ≤ 36 / α ^ 2} with hSd
  have h1α : 1 ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
  have hsub : ∀ cd : 𝓞 K × 𝓞 K, cd ∈ rowBd α → cd.1 ∈ Sc ∧ cd.2 ∈ Sd := by
    rintro ⟨c, d⟩ ⟨hc, hd⟩
    refine ⟨hc, ?_⟩
    show Complex.normSq (σO d) ≤ 36 / α ^ 2
    have h2α : 1 ≤ 2 / α := by rw [le_div_iff₀ hα]; linarith
    have hs : Real.sqrt (2 / α) ≤ 2 / α :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [h2α]⟩
    have hd' : ‖σO d‖ ≤ 6 / α := by
      have : (6 : ℝ) / α = 1 / α + 1 / α + 2 * (2 / α) := by ring
      rw [this]
      simp only at hd
      linarith
    rw [Complex.normSq_eq_norm_sq, show (36 : ℝ) / α ^ 2 = (6 / α) ^ 2 by ring]
    exact pow_le_pow_left₀ (norm_nonneg _) hd' 2
  calc cBox α = ∑' cd : 𝓞 K × 𝓞 K, (rowBd α).indicator (1 : 𝓞 K × 𝓞 K → ℝ≥0∞) cd := rfl
    _ ≤ ∑' cd : 𝓞 K × 𝓞 K, Sc.indicator (1 : 𝓞 K → ℝ≥0∞) cd.1 * Sd.indicator (1 : 𝓞 K → ℝ≥0∞) cd.2 := by
        refine ENNReal.tsum_le_tsum fun cd => ?_
        by_cases h : cd ∈ rowBd α
        · rw [indicator_of_mem h, indicator_of_mem (hsub cd h).1, indicator_of_mem (hsub cd h).2]
          simp
        · rw [indicator_of_notMem h]
          exact zero_le
    _ = (∑' c : 𝓞 K, Sc.indicator (1 : 𝓞 K → ℝ≥0∞) c) * ∑' d : 𝓞 K, Sd.indicator (1 : 𝓞 K → ℝ≥0∞) d := by
        rw [ENNReal.tsum_prod (f := fun c d => Sc.indicator (1 : 𝓞 K → ℝ≥0∞) c *
          Sd.indicator (1 : 𝓞 K → ℝ≥0∞) d), ← ENNReal.tsum_mul_right]
        refine tsum_congr fun c => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal ((4 * (2 / α) + 3) ^ 2) * ENNReal.ofReal ((4 * (36 / α ^ 2) + 3) ^ 2) :=
        mul_le_mul' (tsum_normSq_le_le (by positivity)) (tsum_normSq_le_le (by positivity))
    _ ≤ ENNReal.ofReal ((11 / α) ^ 2 * (147 / α ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hα2 : α ^ 2 ≤ 1 := by nlinarith
        have h1α2 : 1 ≤ 1 / α ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have e1 : 4 * (2 / α) + 3 ≤ 11 / α := by
          have : (11 : ℝ) / α = 8 * (1 / α) + 3 * (1 / α) := by ring
          rw [this]
          have : 4 * (2 / α) = 8 * (1 / α) := by ring
          rw [this]
          linarith
        have e2 : 4 * (36 / α ^ 2) + 3 ≤ 147 / α ^ 2 := by
          have : (147 : ℝ) / α ^ 2 = 144 * (1 / α ^ 2) + 3 * (1 / α ^ 2) := by ring
          rw [this]
          have : 4 * (36 / α ^ 2) = 144 * (1 / α ^ 2) := by ring
          rw [this]
          linarith
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) e1 2) (pow_le_pow_left₀ (by positivity) e2 2)
          (by positivity) (by positivity)

/-! ### The growth of `ρ(m)` -/

/-- `x ↦ bkR r x = 2K_r(x)` is antitone on `(0, ∞)`, by round 361's `bkK_anti`. -/
theorem bkR_anti (r : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : bkR r y ≤ bkR r x := by
  unfold bkR
  refine setIntegral_mono_on (integrableOn_bkR (hx.trans_le hxy) r) (integrableOn_bkR hx r)
    measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_of_nonneg_left (bkK_anti hxy ht) (Real.rpow_nonneg (le_of_lt ht) _)

/-- **The growth of `ρ(m)`**: for `r > 0` and `Y > 0` there is `C` with `|ρ(m)| ≤ C·|m|⁵` for every
`m = δ₃x ≠ 0`. -/
theorem norm_rhoM_le {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, ∀ x : 𝓞 K, x ≠ 0 → ‖rhoM x r Y hY‖ ≤ C * ‖σO (δ3 * x)‖ ^ 5 := by
  set θt := thetaF r Y hY with hθt
  set L := ∫⁻ p, ‖θt p‖ₑ ∂(muR rhoG) with hL
  have hLt : L < ⊤ := ((memLp_thetaF hr hY).integrable one_le_two).2
  set Cb : ℝ := (11 : ℝ) ^ 2 * 147 ^ 2 with hCb
  set Ke : ℝ≥0∞ := ENNReal.ofReal (8 * Cb) * (cTr 6 * L) with hKe
  have hKet : Ke ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (cTr_ne_top 6) hLt.ne)
  set b := bkR (1 / 3) 2 with hb
  have hb0 : 0 < b := bkR_pos (by norm_num) _
  refine ⟨2 * Ke.toReal / b * (4 * Real.pi / 9) ^ 5, fun x hx => ?_⟩
  have hm0 : δ3 * x ≠ 0 := mul_ne_zero δ3_ne_zero hx
  have hm1 : 1 ≤ ‖σO (δ3 * x)‖ := one_le_norm_σO hm0
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := ⟨_, rfl⟩
  have hAeq : A = 4 * Real.pi / 9 * ‖σO (δ3 * x)‖ := by
    rw [hA, norm_div, show ‖(9 : ℂ)‖ = 9 by norm_num]
    ring
  have hA1 : 1 ≤ A := by
    rw [hAeq]
    have : (1 : ℝ) ≤ 4 * Real.pi / 9 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [Real.pi_gt_three]
    nlinarith
  have hA0 : 0 < A := by linarith
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : ℝ, v₀ = 1 / A := ⟨_, rfl⟩
  have hv₀ : 0 < v₀ := by rw [hv₀def]; positivity
  have hv₀1 : v₀ ≤ 1 := by rw [hv₀def, div_le_one hA0]; exact hA1
  have hAv : A * v₀ = 1 := by rw [hv₀def]; field_simp
  set ρ := rhoM x r Y hY with hρ
  set a : ℝ → ℂ := fun v => ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * θt (z, v) with ha
  have hae := coef_thetaF_ae hx hr hY
  rw [← hA] at hae
  have hI0 : Icc v₀ (2 * v₀) ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hv₀ hv.1
  have haeI : ∀ᵐ v ∂(volume.restrict (Icc v₀ (2 * v₀))),
      a v = ρ * ((v : ℂ) * besselK (1 / 3) (A * v)) :=
    ae_restrict_of_ae_restrict_of_subset hI0 hae
  -- the lower bound
  have hlow : ENNReal.ofReal (‖ρ‖ * v₀ * (b / 2) * v₀) ≤ ∫⁻ v in Icc v₀ (2 * v₀), ‖a v‖ₑ := by
    have e : ENNReal.ofReal (‖ρ‖ * v₀ * (b / 2) * v₀) =
        ∫⁻ _ in Icc v₀ (2 * v₀), ENNReal.ofReal (‖ρ‖ * v₀ * (b / 2)) := by
      rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [e]
    refine lintegral_mono_ae ?_
    filter_upwards [haeI, ae_restrict_mem measurableSet_Icc] with v hv hvI
    have hv0 : 0 < v := lt_of_lt_of_le hv₀ hvI.1
    rw [hv, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_mul, besselK_third_ofReal, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hv0.le, Real.norm_of_nonneg (by have := bkR_nonneg (1 / 3) (A * v); positivity)]
    have hAv1 : 0 < A * v := by positivity
    have hAv2 : A * v ≤ 2 := by
      have : A * v ≤ A * (2 * v₀) := mul_le_mul_of_nonneg_left hvI.2 hA0.le
      linarith
    have hbk : b ≤ bkR (1 / 3) (A * v) := bkR_anti _ hAv1 hAv2
    have hρ0 := norm_nonneg ρ
    calc ‖ρ‖ * v₀ * (b / 2) ≤ ‖ρ‖ * v * (1 / 2 * bkR (1 / 3) (A * v)) := by
          have h1 : v₀ ≤ v := hvI.1
          have h2 : b / 2 ≤ 1 / 2 * bkR (1 / 3) (A * v) := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hρ0) h2 (by positivity) (by positivity)
      _ = ‖ρ‖ * (v * (1 / 2 * bkR (1 / 3) (A * v))) := by ring
  -- the upper bound
  have hmeas : Measurable fun p : ℂ × ℝ => ‖θt p‖ₑ := (measurable_thetaF r Y hY).enorm
  have hT : MeasurableSet (fundP3 ×ˢ Icc v₀ (2 * v₀)) := measurableSet_fundP3.prod measurableSet_Icc
  have hup : ∫⁻ v in Icc v₀ (2 * v₀), ‖a v‖ₑ ≤ ENNReal.ofReal (1 / v₀ ^ 3) * Ke := by
    calc ∫⁻ v in Icc v₀ (2 * v₀), ‖a v‖ₑ
        ≤ ∫⁻ v in Icc v₀ (2 * v₀), ∫⁻ z in fundP3, ‖θt (z, v)‖ₑ := by
          refine lintegral_mono fun v => ?_
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          refine lintegral_congr fun z => ?_
          rw [enorm_mul, ← ofReal_norm (ebr _), norm_ebr, ENNReal.ofReal_one, one_mul]
      _ = ∫⁻ p in fundP3 ×ˢ Icc v₀ (2 * v₀), ‖θt p‖ₑ := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod_symm _ hmeas.aemeasurable]
      _ ≤ ENNReal.ofReal ((2 * v₀) ^ 3) * ∫⁻ p in fundP3 ×ˢ Icc v₀ (2 * v₀), ‖θt p‖ₑ ∂uhsMeasure :=
          setLIntegral_volume_le hmeas hT hv₀ fun p hp => ⟨hp.2.1, hp.2.2⟩
      _ ≤ ENNReal.ofReal ((2 * v₀) ^ 3) * ∫⁻ p in boxZ 6 v₀ (2 * v₀), ‖θt p‖ₑ ∂uhsMeasure := by
          gcongr
          intro p hp
          obtain ⟨hp1, hp2⟩ := Set.mem_prod.1 hp
          exact ⟨norm_le_six_of_mem_fundP3 hp1, hp2.1, hp2.2⟩
      _ ≤ ENNReal.ofReal ((2 * v₀) ^ 3) * (cTr 6 * cBox v₀ * L) := by
          gcongr
          exact lintegral_boxZ_le (measurable_thetaF r Y hY) (enorm_thetaF_slAct r Y hY) 6 hv₀ _
      _ ≤ ENNReal.ofReal ((2 * v₀) ^ 3) *
            (cTr 6 * ENNReal.ofReal ((11 / v₀) ^ 2 * (147 / v₀ ^ 2) ^ 2) * L) := by
          gcongr
          exact cBox_le hv₀ hv₀1
      _ = ENNReal.ofReal (1 / v₀ ^ 3) * Ke := by
          rw [hKe, ← mul_assoc, mul_comm (cTr 6) _, ← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc]
          congr 2
          field_simp
          rw [hCb]
          norm_num
  have hfin := hlow.trans hup
  rw [← ENNReal.ofReal_toReal hKet, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  have hKe0 : 0 ≤ Ke.toReal := ENNReal.toReal_nonneg
  rw [show ‖σO (δ3 * x)‖ = A * (9 / (4 * Real.pi)) by rw [hAeq]; field_simp]
  have hv5 : A ^ 5 = 1 / v₀ ^ 5 := by rw [hv₀def]; field_simp
  rw [show 2 * Ke.toReal / b * (4 * Real.pi / 9) ^ 5 * (A * (9 / (4 * Real.pi))) ^ 5 =
      2 * Ke.toReal / b * A ^ 5 by field_simp, hv5]
  rw [show 2 * Ke.toReal / b * (1 / v₀ ^ 5) = 2 * Ke.toReal / (b * v₀ ^ 5) by field_simp,
    le_div_iff₀ (by positivity)]
  have : ‖ρ‖ * v₀ * (b / 2) * v₀ * v₀ ^ 3 ≤ Ke.toReal := by
    calc ‖ρ‖ * v₀ * (b / 2) * v₀ * v₀ ^ 3 ≤ 1 / v₀ ^ 3 * Ke.toReal * v₀ ^ 3 :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
      _ = Ke.toReal := by field_simp
  nlinarith [this]

end Eis

end

#print axioms Eis.tsum_normSq_le_le
#print axioms Eis.cBox_le
#print axioms Eis.bkR_anti
#print axioms Eis.norm_rhoM_le
