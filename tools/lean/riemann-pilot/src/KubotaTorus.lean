import KubotaEisFourier

/-! # Fourier analysis on `ℂ/3ℤ[ω]` (round 435)

S5f-10 of round 360's plan, part 18 (S5f-10f, eighth part). Round 434's next step planned θ as its Fourier
series, through the orthogonality of the characters `ĕ(mz/9)`, `m ∈ δ₃ℤ[ω]`, on the period parallelogram `3P`
of `3ℤ[ω]` and the uniqueness of Fourier coefficients there. This round proves the two, through the chart
`tch(y) = 3(y₀ + y₁ϖ)` from `ℝ²` onto `ℂ` and Mathlib's Fourier analysis on the unit torus `ℝ²/ℤ²`:

* **The chart** (`tch`, `frq` and `frqInv`, definitions; **`ebr_tch`**, with `tch_apply`, `frq_crd`,
  `frq_frqInv`, `frq_neg`, `frq_injective`, `eq_zero_of_frq_eq_zero`, `ebr_neg_tch` and `continuous_tch`): for
  `x = a + bω`, `ĕ(σ(δ₃x)·tch(y)/9) = e(−b·y₀ + (b − a)·y₁)`, Mathlib's `mFourier` at the frequency
  `frq(x) = (−b, b − a)`, and `x ↦ frq(x)` is a bijection of `ℤ[ω]` onto `ℤ²`.
* **The change of variables** (`Mw3` and `tchE`, definitions; **`map_tchE`**, **`integral_box_tch`** and
  **`lintegral_box_tch`**, with `Mw3_apply`, `abs_det_Mw3`, `tchE_apply`, `tch_mem_fundP3_iff`,
  `preimage_tchE_fundP3`, `measurableSet_box` and `box_Ico_ae_eq_Ioc`):
  `∫_{(0,1]²} f(tch(y)) dy = (9√3/2)⁻¹∫_{3P} f`, by Mathlib's `map_linearMap_addHaar_eq_smul_addHaar` with the
  determinant of round 294's `Mw`; the chart carries `[0, 1)²` onto `3P`, and `[0, 1)²` differs from `(0, 1]²`
  by a null set.
* **Orthogonality** (**`integral_fundP3_ebr_eq_zero`** and **`integral_fundP3_ebr_mul`**, with
  `integral_box_mFourier_eq_zero`): `∫_{3P} ĕ(−σ(δ₃x)z/9) dz = 0` for `x ≠ 0`, the integral round 428 left
  unevaluated, and `∫_{3P} ĕ(−σ(δ₃x)z/9)·ĕ(σ(δ₃x′)z/9) dz` is `9√3/2` if `x = x′` and `0` otherwise, from
  Mathlib's `orthonormal_mFourier`.
* **Uniqueness** (**`ae_eq_zero_of_coef`** and **`ae_eq_zero_of_periodic`**): a measurable `g`,
  square-integrable on `3P`, whose coefficients `∫_{3P} ĕ(−σ(δ₃x)z/9)g(z) dz` all vanish, vanishes almost
  everywhere on `3P`, by Mathlib's Hilbert basis `mFourierBasis` of `L²` of the unit torus; if `g` is also
  periodic under `3ℤ[ω]`, it vanishes almost everywhere on `ℂ`, by round 389's `lintegral_tile3`.
-/

open MeasureTheory Set Filter NumberField Complex UnitAddTorus PlanePoisson
open scoped ENNReal Topology

noncomputable section

namespace Eis

-- Mathlib's Fourier analysis on the torus is stated for the Haar probability measure on `UnitAddCircle`, a
-- local instance of `Mathlib/Analysis/Fourier/AddCircleMulti.lean`; this file uses the same instance.
attribute [local instance high] instMeasureSpaceUnitAddCircle

/-! ### The chart -/

/-- **The chart** `y ↦ 3(y₀ + y₁ϖ)` of `ℂ/3ℤ[ω]` by `ℝ²/ℤ²`. -/
def tch (y : Fin 2 → ℝ) : ℂ := 3 * Mw (cpt y)

theorem tch_apply (y : Fin 2 → ℝ) : tch y = 3 * ((y 0 : ℂ) + (y 1 : ℂ) * varpi) := by
  simp [tch, Mw_apply, cpt]

/-- The frequency of `z ↦ ĕ(σ(δ₃x)z/9)` in the chart: `(−b, b − a)` for `x = a + bω`. -/
def frq (x : 𝓞 K) : Fin 2 → ℤ := ![-(crdEquiv.symm x 1), crdEquiv.symm x 1 - crdEquiv.symm x 0]

/-- The point of `ℤ[ω]` with frequency `n`: `(−n₀ − n₁) + (−n₀)ω`. -/
def frqInv (n : Fin 2 → ℤ) : 𝓞 K := crd ![-n 0 - n 1, -n 0]

theorem frq_crd (c : Fin 2 → ℤ) : frq (crd c) = ![-c 1, c 1 - c 0] := by
  have h : crdEquiv.symm (crd c) = c := crdEquiv.symm_apply_apply c
  simp [frq, h]

theorem frq_frqInv (n : Fin 2 → ℤ) : frq (frqInv n) = n := by
  rw [frqInv, frq_crd]
  ext i
  fin_cases i <;> simp

theorem frq_neg (x : 𝓞 K) : frq (-x) = -frq x := by
  obtain ⟨c, rfl⟩ := crdEquiv.surjective x
  have e : -crdEquiv c = crd (-c) := by
    show -crd c = crd (-c)
    simp [crd]; ring
  rw [e, frq_crd]
  show ![-(-c) 1, (-c) 1 - (-c) 0] = -frq (crd c)
  rw [frq_crd]
  ext i
  fin_cases i <;> simp; ring

theorem frq_injective : Function.Injective frq := by
  intro x x' h
  obtain ⟨c, rfl⟩ := crdEquiv.surjective x
  obtain ⟨d, rfl⟩ := crdEquiv.surjective x'
  have h' : frq (crd c) = frq (crd d) := h
  rw [frq_crd, frq_crd] at h'
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp at h0 h1
  have e : c = d := by
    ext i
    fin_cases i
    · show c 0 = d 0
      omega
    · show c 1 = d 1
      omega
  rw [e]

theorem eq_zero_of_frq_eq_zero {x : 𝓞 K} (h : frq x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := crdEquiv.surjective x
  have h' : frq (crd c) = 0 := h
  rw [frq_crd] at h'
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp at h0 h1
  show crd c = 0
  have hc0 : c 0 = 0 := by omega
  simp [crd, hc0, h0]

/-- **The characters in the chart**: `ĕ(σ(δ₃x)·tch(y)/9) = e(⟨frq x, y⟩)`, Mathlib's `mFourier`. -/
theorem ebr_tch (x : 𝓞 K) (y : Fin 2 → ℝ) :
    ebr (σO (δ3 * x) * tch y / 9) = mFourier (frq x) (fun i => (y i : UnitAddCircle)) := by
  obtain ⟨c, rfl⟩ := crdEquiv.surjective x
  show ebr (σO (δ3 * crd c) * tch y / 9) = mFourier (frq (crd c)) (fun i => (y i : UnitAddCircle))
  rw [frq_crd]
  show _ = ∏ i : Fin 2, fourier (![-c 1, c 1 - c 0] i) ((y i : UnitAddCircle))
  rw [Fin.prod_univ_two, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  unfold ebr
  congr 1
  have hs := varpi_re_im
  have hre : (σO (δ3 * crd c) * tch y / 9).re = (-(c 1 : ℝ) * y 0 + ((c 1 : ℝ) - c 0) * y 1) / 2 := by
    rw [map_mul, σO_δ3, tch_apply]
    simp only [crd, map_add, map_mul, map_intCast, σO_ω]
    simp [Complex.mul_re, Complex.mul_im, hs.1]
    linear_combination (2 / 3 : ℝ) * ((c 1 : ℝ) * y 1 - (c 0 : ℝ) * y 1 - (c 1 : ℝ) * y 0) * hs.2
  rw [hre]
  simp
  ring

theorem ebr_neg_tch (x : 𝓞 K) (y : Fin 2 → ℝ) :
    ebr (-(σO (δ3 * x) / 9 * tch y)) = mFourier (-frq x) (fun i => (y i : UnitAddCircle)) := by
  rw [← frq_neg, ← ebr_tch]
  congr 1
  rw [mul_neg, map_neg]
  ring

theorem continuous_tch : Continuous tch := by
  have h : Continuous cpt := by unfold cpt; fun_prop
  exact continuous_const.mul (continuous_Mw.comp h)

/-! ### The change of variables -/

/-- `z ↦ 3·Mw(z)`, an `ℝ`-linear automorphism of `ℂ`. -/
def Mw3 : ℂ ≃ₗ[ℝ] ℂ := Mw.trans (LinearEquiv.smulOfNeZero ℝ ℂ 3 three_ne_zero)

theorem Mw3_apply (z : ℂ) : Mw3 z = 3 * Mw z := by
  simp [Mw3, Complex.real_smul]

theorem abs_det_Mw3 : |LinearMap.det (Mw3 : ℂ →ₗ[ℝ] ℂ)| = 9 * (Real.sqrt 3 / 2) := by
  have h : (Mw3 : ℂ →ₗ[ℝ] ℂ) = (3 : ℝ) • (Mw : ℂ →ₗ[ℝ] ℂ) := by
    refine LinearMap.ext fun z => ?_
    simp [Mw3_apply, Complex.real_smul]
  rw [h, LinearMap.det_smul, Complex.finrank_real_complex, abs_mul, abs_det_Mw]
  norm_num

/-- The chart as a measurable equivalence `ℝ² ≃ ℂ`. -/
def tchE : (Fin 2 → ℝ) ≃ᵐ ℂ :=
  Complex.measurableEquivPi.symm.trans Mw3.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem tchE_apply (y : Fin 2 → ℝ) : tchE y = tch y := by
  show Mw3 (Complex.measurableEquivPi.symm y) = tch y
  rw [Mw3_apply, Complex.measurableEquivPi_symm_apply]
  rfl

/-- **The chart's image measure**: Lebesgue measure on `ℝ²` is carried to `(9√3/2)⁻¹` times Lebesgue measure
on `ℂ`. -/
theorem map_tchE :
    Measure.map tchE volume = ENNReal.ofReal (9 * (Real.sqrt 3 / 2))⁻¹ • (volume : Measure ℂ) := by
  have hdet : LinearMap.det (Mw3 : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    intro h
    have := abs_det_Mw3
    rw [h, abs_zero] at this
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    linarith
  have e : (tchE : (Fin 2 → ℝ) → ℂ) = (Mw3 : ℂ →ₗ[ℝ] ℂ) ∘ Complex.measurableEquivPi.symm := rfl
  rw [e, ← Measure.map_map (Mw3 : ℂ →ₗ[ℝ] ℂ).continuous_of_finiteDimensional.measurable
    Complex.measurableEquivPi.symm.measurable,
    (MeasurePreserving.symm _ Complex.volume_preserving_equiv_pi).map_eq,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, abs_inv, abs_det_Mw3]

theorem tch_mem_fundP3_iff (y : Fin 2 → ℝ) : tch y ∈ fundP3 ↔ ∀ i, y i ∈ Ico (0 : ℝ) 1 := by
  show tch y / 3 ∈ fundP ↔ _
  have e : tch y / 3 = Mw (cpt y) := by rw [tch]; ring
  rw [e]
  show (Mw.symm (Mw (cpt y))).re ∈ Ico (0 : ℝ) 1 ∧ (Mw.symm (Mw (cpt y))).im ∈ Ico (0 : ℝ) 1 ↔ _
  rw [Mw.symm_apply_apply, Fin.forall_fin_two]
  simp [cpt]

theorem preimage_tchE_fundP3 : tchE ⁻¹' fundP3 = {y : Fin 2 → ℝ | ∀ i, y i ∈ Ico (0 : ℝ) 1} := by
  ext y
  rw [mem_preimage, tchE_apply, tch_mem_fundP3_iff]
  rfl

theorem measurableSet_box : MeasurableSet {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} := by
  have e : {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext y; simp
  rw [e]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem box_Ico_ae_eq_Ioc :
    {y : Fin 2 → ℝ | ∀ i, y i ∈ Ico (0 : ℝ) 1} =ᵐ[volume] {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} := by
  have e1 : {y : Fin 2 → ℝ | ∀ i, y i ∈ Ico (0 : ℝ) 1} = Set.pi univ fun _ => Ico (0 : ℝ) 1 := by
    ext y; simp
  have e2 : {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext y; simp
  rw [e1, e2, volume_pi]
  exact Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Ioc

/-- **The change of variables**: `∫_{(0,1]²} f(tch y) dy = (9√3/2)⁻¹∫_{3P} f`. -/
theorem integral_box_tch (f : ℂ → ℂ) :
    ∫ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, f (tch y) =
      ((9 * (Real.sqrt 3 / 2))⁻¹ : ℝ) • ∫ z in fundP3, f z := by
  have e : (fun y => f (tch y)) = fun y => f (tchE y) := funext fun y => by rw [tchE_apply]
  rw [e, ← setIntegral_congr_set box_Ico_ae_eq_Ioc, ← preimage_tchE_fundP3,
    ← setIntegral_map_equiv tchE f fundP3, map_tchE, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]

theorem lintegral_box_tch (f : ℂ → ℝ≥0∞) :
    ∫⁻ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, f (tch y) =
      ENNReal.ofReal (9 * (Real.sqrt 3 / 2))⁻¹ * ∫⁻ z in fundP3, f z := by
  have e : (fun y => f (tch y)) = fun y => f (tchE y) := funext fun y => by rw [tchE_apply]
  rw [e, ← setLIntegral_congr box_Ico_ae_eq_Ioc, ← preimage_tchE_fundP3, ← lintegral_map_equiv f tchE,
    ← tchE.restrict_map, map_tchE, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-! ### Orthogonality and uniqueness -/

/-- `∫_{(0,1]²} e(⟨n, y⟩) dy = 0` for `n ≠ 0` (Mathlib's `orthonormal_mFourier`). -/
theorem integral_box_mFourier_eq_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ∫ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, mFourier n (fun i => (y i : UnitAddCircle)) = 0 := by
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 2)) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simp [Ne.symm hn, mFourier_zero] at h
  have h2 := integral_preimage (d := Fin 2) (fun t => mFourier n t) 0
  simp only [Pi.zero_apply, zero_add] at h2
  rw [← h2]
  exact h

/-- **Orthogonality on `3P`**: `∫_{3P} ĕ(−σ(δ₃x)z/9) dz = 0` for `x ≠ 0`. -/
theorem integral_fundP3_ebr_eq_zero {x : 𝓞 K} (hx : x ≠ 0) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) = 0 := by
  have h := integral_box_tch (fun z => ebr (-(σO (δ3 * x) / 9 * z)))
  simp only [ebr_neg_tch] at h
  have hn : -frq x ≠ 0 := neg_ne_zero.2 fun h => hx (eq_zero_of_frq_eq_zero h)
  rw [integral_box_mFourier_eq_zero hn] at h
  have hc : ((9 * (Real.sqrt 3 / 2))⁻¹ : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.1 h.symm).resolve_left hc

open Classical in
/-- **Orthogonality on `3P`**, in full: `∫_{3P} ĕ(−σ(δ₃x)z/9)·ĕ(σ(δ₃x′)z/9) dz` is `9√3/2` if `x = x′`, and
`0` otherwise. -/
theorem integral_fundP3_ebr_mul (x x' : 𝓞 K) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * ebr (σO (δ3 * x') * z / 9) =
      if x = x' then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) else 0 := by
  have e : ∀ z, ebr (-(σO (δ3 * x) / 9 * z)) * ebr (σO (δ3 * x') * z / 9) =
      ebr (-(σO (δ3 * (x - x')) / 9 * z)) := by
    intro z
    rw [← ebr_add, mul_sub, map_sub]
    congr 1
    ring
  simp_rw [e]
  split_ifs with h
  · simp only [h, sub_self, mul_zero, map_zero, zero_div, zero_mul, neg_zero, ebr_zero]
    rw [setIntegral_const, Measure.real, volume_fundP3, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_one]
  · exact integral_fundP3_ebr_eq_zero (sub_ne_zero.2 h)

/-- **Uniqueness of the Fourier coefficients on `ℂ/3ℤ[ω]`**: a measurable `g`, square-integrable on `3P`,
whose coefficients `∫_{3P} ĕ(−σ(δ₃x)z/9)g(z) dz` vanish for every `x ∈ ℤ[ω]`, vanishes almost everywhere on
`3P`. -/
theorem ae_eq_zero_of_coef {g : ℂ → ℂ} (hg : Measurable g) (h2 : ∫⁻ z in fundP3, ‖g z‖ₑ ^ 2 < ⊤)
    (hc : ∀ x : 𝓞 K, ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * g z = 0) :
    ∀ᵐ z ∂(volume.restrict fundP3), g z = 0 := by
  set B := {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} with hB
  set G : UnitAddTorus (Fin 2) → ℂ := fun t => g (tch (measurableEquivPiIoc 0 t).1) with hGdef
  have hGm : Measurable G := hg.comp (continuous_tch.measurable.comp
    (measurable_subtype_coe.comp (measurableEquivPiIoc 0).measurable))
  have hGy : ∀ y ∈ B, G (fun i => (y i : UnitAddCircle)) = g (tch y) := by
    intro y hy
    simp only [hGdef, coe_measurableEquivPiIoc_apply]
    congr 2
    funext i
    exact AddCircle.equivIoc_coe_of_mem (by simpa using hy i)
  have hbox : ∀ F : ℂ → ℝ≥0∞,
      ∫⁻ t, F (G t) = ENNReal.ofReal (9 * (Real.sqrt 3 / 2))⁻¹ * ∫⁻ z in fundP3, F (g z) := by
    intro F
    have h := lintegral_preimage (d := Fin 2) (fun t => F (G t)) 0
    simp only [Pi.zero_apply, zero_add] at h
    rw [h, ← lintegral_box_tch (fun z => F (g z))]
    exact setLIntegral_congr_fun measurableSet_box fun y hy => by simp only [hGy y hy]
  have hL2 : ∫⁻ t, ‖G t‖ₑ ^ 2 < ⊤ := by
    rw [hbox (fun w => ‖w‖ₑ ^ 2)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  have hGL : MemLp G 2 := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hGm.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hL2.ne
  have hcoef : ∀ n, mFourierCoeff G n = 0 := by
    intro n
    have h := integral_box_tch (fun z => ebr (-(σO (δ3 * frqInv n) / 9 * z)) * g z)
    rw [hc, smul_zero] at h
    rw [mFourierCoeff_eq_integral G n 0]
    simp only [Pi.zero_apply, zero_add]
    rw [← h]
    refine setIntegral_congr_fun measurableSet_box fun y hy => ?_
    simp only [smul_eq_mul, hGy y hy, ebr_neg_tch, frq_frqInv]
  have hzero : hGL.toLp G = 0 := by
    apply mFourierBasis.repr.injective
    rw [map_zero]
    ext n
    rw [mFourierBasis_repr]
    have e : mFourierCoeff (⇑(hGL.toLp G)) n = mFourierCoeff G n :=
      integral_congr_ae (by filter_upwards [hGL.coeFn_toLp] with t ht; rw [ht])
    rw [e, hcoef n]
    rfl
  have hGae : G =ᵐ[volume] 0 := by
    have h := hGL.coeFn_toLp
    rw [hzero] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hint : ∫⁻ t, ‖G t‖ₑ = 0 := by
    rw [lintegral_congr_ae (hGae.mono fun t ht => by rw [ht])]
    simp
  rw [hbox (fun w => ‖w‖ₑ), mul_eq_zero] at hint
  have h0 : ∫⁻ z in fundP3, ‖g z‖ₑ = 0 :=
    hint.resolve_left (ENNReal.ofReal_pos.2 (by positivity)).ne'
  filter_upwards [(lintegral_eq_zero_iff hg.enorm).1 h0] with z hz
  simpa using hz

/-- **From `3P` to `ℂ`**: a measurable function periodic under `3ℤ[ω]` that vanishes almost everywhere on `3P`
vanishes almost everywhere, by round 389's tiling `lintegral_tile3`. -/
theorem ae_eq_zero_of_periodic {g : ℂ → ℂ} (hg : Measurable g) (hper : ∀ z u, g (z + σO (3 * u)) = g z)
    (h : ∀ᵐ z ∂(volume.restrict fundP3), g z = 0) : ∀ᵐ z, g z = 0 := by
  have h0 : ∫⁻ z in fundP3, ‖g z‖ₑ = 0 := by
    rw [lintegral_congr_ae (h.mono fun z hz => by rw [hz])]
    simp
  have h1 : ∫⁻ z, ‖g z‖ₑ = 0 := by
    rw [lintegral_tile3 hg.enorm]
    simp only [hper, h0, tsum_zero]
  filter_upwards [(lintegral_eq_zero_iff hg.enorm).1 h1] with z hz
  simpa using hz

end Eis

end

#print axioms Eis.tch_apply
#print axioms Eis.frq_crd
#print axioms Eis.frq_frqInv
#print axioms Eis.frq_neg
#print axioms Eis.frq_injective
#print axioms Eis.eq_zero_of_frq_eq_zero
#print axioms Eis.ebr_tch
#print axioms Eis.ebr_neg_tch
#print axioms Eis.continuous_tch
#print axioms Eis.Mw3_apply
#print axioms Eis.abs_det_Mw3
#print axioms Eis.tchE_apply
#print axioms Eis.map_tchE
#print axioms Eis.tch_mem_fundP3_iff
#print axioms Eis.preimage_tchE_fundP3
#print axioms Eis.measurableSet_box
#print axioms Eis.box_Ico_ae_eq_Ioc
#print axioms Eis.integral_box_tch
#print axioms Eis.lintegral_box_tch
#print axioms Eis.integral_box_mFourier_eq_zero
#print axioms Eis.integral_fundP3_ebr_eq_zero
#print axioms Eis.integral_fundP3_ebr_mul
#print axioms Eis.ae_eq_zero_of_coef
#print axioms Eis.ae_eq_zero_of_periodic
