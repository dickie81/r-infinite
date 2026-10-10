import KubotaEisenstein

/-! # The growth of the cubic Eisenstein series at the cusps (round 388)

S5f-9b of round 360's plan, part 1. For `σ = Re s > 2` and `v ≥ 1/2`, `E(g·w, s) = a_g·v^s + O(v^{2−σ})` at
every cusp `g·∞`, `g ∈ SL_2(ℤ[ω])`, with a constant that depends only on `σ`.

* **The period parallelogram** (**`volume_fundP`**, with `fundP_eq_image`, `norm_varpi` and
  `norm_le_two_of_mem_fundP`): round 385's `P` has area `√3/2` and lies in the closed disc of radius `2`.
* **Tiling** (**`lintegral_tile`**): `∫_ℂ G = Σ_{t∈ℤ[ω]} ∫_P G(y + σ(t)) dy` for measurable `G ≥ 0`.
* **The radial integral** (**`lintegral_normSq_add_rpow`**, with `integral_Ioi_mul_rpow`):
  `∫_ℂ (|x|² + A)^{−σ} dx = πA^{1−σ}/(σ − 1)` for `A > 0` and `σ > 1`.
* **The comparison** (**`tsum_normSq_add_rpow_le`**, with `normSq_add_le_mul`, `rpow_le_of_mem_fundP` and
  `measurable_normSq_add_rpow`): `(√3/2)·Σ_d (|w + σ(d)|² + A)^{−σ} ≤ 33^σ·πA^{1−σ}/(σ − 1)` for
  `A ≥ 1/4`.
* **The rows with `c ≠ 0`** (`cuspK` and `cuspC`, definitions; **`summable_height_ne`**, with `cuspK_pos`,
  `cuspC_nonneg`, `rpow_mul_sq_rpow`, `tsum_height_c_le`, `tsum_norm_σO_rpow_le` and `tsum_height_ne_le`):
  `Σ_{c≠0, d} (v/Q_w(c, d))^σ ≤ cuspC(σ)·v^{2−σ}` over all pairs of `ℤ[ω]` with `c ≠ 0`, for `σ > 2` and
  `v ≥ 1/2`, with `Q_w(c, d) = |cz + d|² + |c|²v²`.
* **The cusps** (`cuspA`, a definition; **`norm_eis1_sub_le`** and **`norm_eis1_slAct_sub_le`**, with
  `cuspA_one`, `isUnit_rowMul_snd` and `eisTerm_slAct_of_fst`): `|E(w, s) − v^s| ≤ cuspC(σ)·v^{2−σ}`, and
  `|E(g·w, s) − a_g·v^s| ≤ cuspC(σ)·v^{2−σ}` for every `g ∈ SL_2(ℤ[ω])`, where `a_g = Σ (c/d)₃` over the
  bottom rows `(c, d)` of `Γ_1(3)` with `(c, d)g = (0, *)`; `a_1 = 1`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

theorem fundP_eq_image :
    fundP = Mw '' {u : ℂ | u.re ∈ Ico (0 : ℝ) 1 ∧ u.im ∈ Ico (0 : ℝ) 1} := by
  ext z
  constructor
  · intro hz
    exact ⟨Mw.symm z, hz, Mw.apply_symm_apply z⟩
  · rintro ⟨u, hu, rfl⟩
    change (Mw.symm (Mw u)).re ∈ _ ∧ (Mw.symm (Mw u)).im ∈ _
    rw [Mw.symm_apply_apply]
    exact hu

/-- **The area of `P`**: `vol(P) = √3/2`. -/
theorem volume_fundP : volume fundP = ENNReal.ofReal (Real.sqrt 3 / 2) := by
  rw [fundP_eq_image]
  have h := Measure.addHaar_image_linearMap volume (Mw : ℂ →ₗ[ℝ] ℂ)
    {u : ℂ | u.re ∈ Ico (0 : ℝ) 1 ∧ u.im ∈ Ico (0 : ℝ) 1}
  rw [abs_det_Mw] at h
  rw [show (Mw '' {u : ℂ | u.re ∈ Ico (0 : ℝ) 1 ∧ u.im ∈ Ico (0 : ℝ) 1}) =
    (Mw : ℂ →ₗ[ℝ] ℂ) '' {u : ℂ | u.re ∈ Ico (0 : ℝ) 1 ∧ u.im ∈ Ico (0 : ℝ) 1} from rfl, h]
  have hS : {u : ℂ | u.re ∈ Ico (0 : ℝ) 1 ∧ u.im ∈ Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
    ext u
    simp
  rw [hS, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

theorem norm_varpi : ‖varpi‖ = 1 := by
  have := normSq_varpi
  rw [Complex.normSq_eq_norm_sq] at this
  change ‖σO ω‖ = 1
  nlinarith [norm_nonneg (σO ω)]

theorem norm_le_two_of_mem_fundP {y : ℂ} (hy : y ∈ fundP) : ‖y‖ ≤ 2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hy
  set u := Mw.symm y
  have e : y = (u.re : ℂ) + (u.im : ℂ) * varpi := (Mw.apply_symm_apply y).symm
  calc ‖y‖ = ‖(u.re : ℂ) + (u.im : ℂ) * varpi‖ := by rw [← e]
    _ ≤ ‖(u.re : ℂ)‖ + ‖(u.im : ℂ)‖ * ‖varpi‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ = u.re + u.im := by
        rw [norm_varpi, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          mul_one, abs_of_nonneg h1, abs_of_nonneg h3]
    _ ≤ 2 := by linarith

/-- **Tiling**: `∫_ℂ G = Σ_{t∈ℤ[ω]} ∫_P G(y + σ(t)) dy`. -/
theorem lintegral_tile {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP, G (y + σO t) := by
  have h1 : ∀ x, G x = ∑' t : 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞) (x + σO (-t)) * G x := by
    intro x
    have e := (Equiv.neg (𝓞 K)).tsum_eq (fun t => fundP.indicator (1 : ℂ → ℝ≥0∞) (x + σO t))
    simp only [Equiv.neg_apply] at e
    rw [ENNReal.tsum_mul_right, e, tsum_fundP, one_mul]
  have hm : ∀ t : 𝓞 K, Measurable fun x => fundP.indicator (1 : ℂ → ℝ≥0∞) (x + σO (-t)) * G x :=
    fun t => ((measurable_one.indicator measurableSet_fundP).comp (measurable_add_const _)).mul hG
  calc ∫⁻ x, G x = ∫⁻ x, ∑' t : 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞) (x + σO (-t)) * G x :=
        lintegral_congr fun x => h1 x
    _ = ∑' t : 𝓞 K, ∫⁻ x, fundP.indicator (1 : ℂ → ℝ≥0∞) (x + σO (-t)) * G x :=
        lintegral_tsum fun t => (hm t).aemeasurable
    _ = ∑' t : 𝓞 K, ∫⁻ y in fundP, G (y + σO t) := by
        refine tsum_congr fun t => ?_
        rw [← lintegral_add_right_eq_self _ (σO t)]
        rw [← lintegral_indicator measurableSet_fundP]
        refine lintegral_congr fun x => ?_
        simp only [map_neg, add_neg_cancel_right]
        by_cases hx : x ∈ fundP
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]

/-- `∫_0^∞ r(r² + A)^{−σ} dr = A^{1−σ}/(2(σ − 1))`. -/
theorem integral_Ioi_mul_rpow {A σ : ℝ} (hA : 0 < A) (hσ : 1 < σ) :
    ∫ r in Ioi (0 : ℝ), r * (r ^ 2 + A) ^ (-σ) = A ^ (1 - σ) / (2 * (σ - 1)) ∧
      IntegrableOn (fun r : ℝ => r * (r ^ 2 + A) ^ (-σ)) (Ioi 0) := by
  set g : ℝ → ℝ := fun r => -((r ^ 2 + A) ^ (1 - σ)) / (2 * (σ - 1))
  have hpos : ∀ r : ℝ, 0 < r ^ 2 + A := fun r => by positivity
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (x * (x ^ 2 + A) ^ (-σ)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + A) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const A
    have h2 := h1.rpow_const (p := 1 - σ) (Or.inl (hpos x).ne')
    have h3 := (h2.neg).div_const (2 * (σ - 1))
    convert h3 using 1
    have hσ' : 2 * (σ - 1) ≠ 0 := by
      have : 0 < σ - 1 := by linarith
      positivity
    rw [show (1 - σ - 1 : ℝ) = -σ by ring]
    have hσ1 : σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * (x ^ 2 + A) ^ (-σ) := fun x hx =>
    mul_nonneg (le_of_lt hx) (Real.rpow_nonneg (hpos x).le _)
  have hlim : Tendsto g atTop (nhds 0) := by
    have ht : Tendsto (fun r : ℝ => r ^ 2 + A) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
    have h0 := (tendsto_rpow_neg_atTop (y := σ - 1) (by linarith)).comp ht
    have h1 : Tendsto (fun r : ℝ => -((r ^ 2 + A) ^ (1 - σ)) / (2 * (σ - 1))) atTop
        (nhds (-0 / (2 * (σ - 1)))) := by
      refine (Tendsto.neg ?_).div_const _
      convert h0 using 2
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa using h1
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim]
  simp only [g]
  rw [show ((0 : ℝ) ^ 2 + A) = A by ring]
  ring

/-- **The radial integral**: `∫_ℂ (|x|² + A)^{−σ} dx = πA^{1−σ}/(σ − 1)` for `A > 0`, `σ > 1`. -/
theorem lintegral_normSq_add_rpow {A σ : ℝ} (hA : 0 < A) (hσ : 1 < σ) :
    ∫⁻ x : ℂ, ENNReal.ofReal ((Complex.normSq x + A) ^ (-σ)) =
      ENNReal.ofReal (Real.pi * A ^ (1 - σ) / (σ - 1)) := by
  obtain ⟨hI, hint⟩ := integral_Ioi_mul_rpow hA hσ
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hmeas (g := fun p : ℝ × ℝ =>
    ENNReal.ofReal (p.1 * (p.1 ^ 2 + A) ^ (-σ)) * 1) (fun p hp => ?_)]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * (r ^ 2 + A) ^ (-σ)))
        (g := fun _ : ℝ => (1 : ℝ≥0∞)) (by fun_prop) aemeasurable_const]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
      one_mul, ← ofReal_integral_eq_lintegral_ofReal hint, hI, ← ENNReal.ofReal_mul]
    · congr 1
      have : (σ - 1) ≠ 0 := by linarith
      field_simp
      ring
    · have : 0 < σ - 1 := by linarith
      positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_nonneg (le_of_lt hr) (Real.rpow_nonneg (by positivity) _)
  · have hr : 0 < p.1 := hp.1
    simp only [smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_mul hr.le]
    congr 2
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, abs_of_pos hr]

/-- `|x + y|² + A ≤ 33(|x|² + A)` for `|y| ≤ 2` and `A ≥ 1/4`. -/
theorem normSq_add_le_mul {x y : ℂ} {A : ℝ} (hA : 1 / 4 ≤ A) (hy : ‖y‖ ≤ 2) :
    Complex.normSq (x + y) + A ≤ 33 * (Complex.normSq x + A) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 : ‖x + y‖ ≤ ‖x‖ + 2 := (norm_add_le _ _).trans (by linarith)
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ - 2), norm_nonneg x]

/-- **The comparison**: `(|x|² + A)^{−σ} ≤ 33^σ(|x + y|² + A)^{−σ}` for `y ∈ P`, `A ≥ 1/4`. -/
theorem rpow_le_of_mem_fundP {x y : ℂ} {A σ : ℝ} (hA : 1 / 4 ≤ A) (hσ : 0 ≤ σ) (hy : y ∈ fundP) :
    (Complex.normSq x + A) ^ (-σ) ≤ 33 ^ σ * (Complex.normSq (x + y) + A) ^ (-σ) := by
  have hpos : 0 < Complex.normSq x + A := by
    have := Complex.normSq_nonneg x
    linarith
  have hpos' : 0 < Complex.normSq (x + y) + A := by
    have := Complex.normSq_nonneg (x + y)
    linarith
  have hle := normSq_add_le_mul (x := x) hA (norm_le_two_of_mem_fundP hy)
  calc (Complex.normSq x + A) ^ (-σ) = 33 ^ σ * (33 * (Complex.normSq x + A)) ^ (-σ) := by
        rw [Real.mul_rpow (by norm_num) hpos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 33) σ,
          ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ 33 ^ σ * (Complex.normSq (x + y) + A) ^ (-σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos' hle (by linarith))
          (by positivity)

theorem measurable_normSq_add_rpow (A σ : ℝ) :
    Measurable fun x : ℂ => ENNReal.ofReal ((Complex.normSq x + A) ^ (-σ)) :=
  ENNReal.measurable_ofReal.comp
    ((Complex.continuous_normSq.measurable.add_const A).pow_const (-σ))

/-- **The lattice sum against the integral**:
`(√3/2)·Σ_{d∈ℤ[ω]} (|w + σ(d)|² + A)^{−σ} ≤ 33^σ·πA^{1−σ}/(σ − 1)` for `A ≥ 1/4`. -/
theorem tsum_normSq_add_rpow_le {A σ : ℝ} (hA : 1 / 4 ≤ A) (hσ : 1 < σ) (w : ℂ) :
    ENNReal.ofReal (Real.sqrt 3 / 2) *
        ∑' d : 𝓞 K, ENNReal.ofReal ((Complex.normSq (w + σO d) + A) ^ (-σ)) ≤
      ENNReal.ofReal (33 ^ σ) * ENNReal.ofReal (Real.pi * A ^ (1 - σ) / (σ - 1)) := by
  set G : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal ((Complex.normSq x + A) ^ (-σ))
  have hG : Measurable G := measurable_normSq_add_rpow A σ
  rw [← lintegral_normSq_add_rpow (by linarith) hσ, ← lintegral_add_right_eq_self G w,
    lintegral_tile (G := fun x => G (x + w)) (hG.comp (measurable_add_const w)),
    ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun d => ?_
  rw [← volume_fundP, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono (by fun_prop) fun y hy => ?_
  simp only [G]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := rpow_le_of_mem_fundP (x := w + σO d) hA (by linarith) hy
  rw [show y + σO d + w = w + σO d + y by ring]
  exact this

/-- The constant of the sum over `d`: `33^σπ/((σ − 1)·√3/2)`. -/
def cuspK (σ : ℝ) : ℝ := 33 ^ σ * Real.pi / ((σ - 1) * (Real.sqrt 3 / 2))

theorem cuspK_pos {σ : ℝ} (hσ : 1 < σ) : 0 < cuspK σ := by
  have : 0 < σ - 1 := by linarith
  unfold cuspK
  positivity

/-- `v^σ(a²v²)^{1−σ} = a^{−(2σ−2)}v^{2−σ}`. -/
theorem rpow_mul_sq_rpow {a v σ : ℝ} (ha : 0 ≤ a) (hv : 0 < v) :
    v ^ σ * (a ^ 2 * v ^ 2) ^ (1 - σ) = a ^ (-(2 * σ - 2)) * v ^ (2 - σ) := by
  rw [show a ^ 2 * v ^ 2 = (a * v) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
    ← Real.rpow_mul (mul_nonneg ha hv.le), Real.mul_rpow ha hv.le, mul_left_comm,
    ← Real.rpow_add hv]
  congr 2 <;> ring

/-- **The sum over `d`** for `c ≠ 0` and `v ≥ 1/2`:
`Σ_d (v/Q_w(c, d))^σ ≤ cuspK(σ)·|σc|^{−(2σ−2)}·v^{2−σ}`. -/
theorem tsum_height_c_le {σ : ℝ} (hσ : 1 < σ) {c : 𝓞 K} (hc : c ≠ 0) (z : ℂ) {v : ℝ}
    (hv : 1 / 2 ≤ v) :
    ∑' d : 𝓞 K, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ σ) ≤
      ENNReal.ofReal (cuspK σ * (‖σO c‖ ^ (-(2 * σ - 2)) * v ^ (2 - σ))) := by
  have hv0 : 0 < v := by linarith
  have hc1 : 1 ≤ ‖σO c‖ := one_le_norm_σO hc
  set A := Complex.normSq (σO c) * v ^ 2 with hAdef
  have hA2 : A = ‖σO c‖ ^ 2 * v ^ 2 := by rw [hAdef, Complex.normSq_eq_norm_sq]
  have hA : 1 / 4 ≤ A := by
    rw [hA2]
    have h1 : 1 ≤ ‖σO c‖ ^ 2 := by nlinarith
    have h2 : 1 / 4 ≤ v ^ 2 := by nlinarith
    nlinarith
  have hterm : ∀ d : 𝓞 K, (v / uhsDen (σO c) (σO d) z v) ^ σ =
      v ^ σ * (Complex.normSq (σO c * z + σO d) + A) ^ (-σ) := by
    intro d
    have hpos : 0 < Complex.normSq (σO c * z + σO d) + A := by
      have := Complex.normSq_nonneg (σO c * z + σO d)
      linarith
    unfold uhsDen
    rw [Real.div_rpow hv0.le hpos.le, Real.rpow_neg hpos.le, div_eq_mul_inv]
  simp_rw [hterm, ENNReal.ofReal_mul (Real.rpow_nonneg hv0.le σ)]
  rw [ENNReal.tsum_mul_left]
  have h := tsum_normSq_add_rpow_le hA hσ (σO c * z)
  have hσ1 : 0 < σ - 1 := by linarith
  have hS : ∑' d : 𝓞 K, ENNReal.ofReal ((Complex.normSq (σO c * z + σO d) + A) ^ (-σ)) ≤
      ENNReal.ofReal (33 ^ σ * (Real.pi * A ^ (1 - σ) / (σ - 1)) / (Real.sqrt 3 / 2)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
        (Or.inl ENNReal.ofReal_ne_top),
      mul_comm, ENNReal.ofReal_mul (by positivity)]
    exact h
  calc ENNReal.ofReal (v ^ σ) *
        ∑' d : 𝓞 K, ENNReal.ofReal ((Complex.normSq (σO c * z + σO d) + A) ^ (-σ))
      ≤ ENNReal.ofReal (v ^ σ) *
          ENNReal.ofReal (33 ^ σ * (Real.pi * A ^ (1 - σ) / (σ - 1)) / (Real.sqrt 3 / 2)) :=
        mul_le_mul_right hS _
    _ = ENNReal.ofReal (cuspK σ * (‖σO c‖ ^ (-(2 * σ - 2)) * v ^ (2 - σ))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hv0.le σ)]
        congr 1
        rw [← rpow_mul_sq_rpow (norm_nonneg _) hv0, ← hA2]
        unfold cuspK
        field_simp

open Classical in
/-- `Σ_{c≠0} |σc|^{−τ} ≤ 2^τ·Σ_c (1 + |σc|)^{−τ}` for `τ > 2`. -/
theorem tsum_norm_σO_rpow_le {τ : ℝ} (hτ : 2 < τ) :
    ∑' c : 𝓞 K, (if c = 0 then 0 else ENNReal.ofReal (‖σO c‖ ^ (-τ))) ≤
      ENNReal.ofReal (2 ^ τ * ∑' c : 𝓞 K, (1 + ‖σO c‖) ^ (-τ)) := by
  have hs := summable_O_rpow hτ
  rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun c => by positivity) (hs.mul_left _)]
  refine ENNReal.tsum_le_tsum fun c => ?_
  split_ifs with hc
  · exact zero_le
  · refine ENNReal.ofReal_le_ofReal ?_
    have h1 := one_le_norm_σO hc
    have h0 : 0 < ‖σO c‖ := by linarith
    calc ‖σO c‖ ^ (-τ) = 2 ^ τ * (2 * ‖σO c‖) ^ (-τ) := by
          rw [Real.mul_rpow (by norm_num) h0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ 2 ^ τ * (1 + ‖σO c‖) ^ (-τ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)) (by positivity)

/-- The constant of the cusp bound: `cuspK(σ)·2^{2σ−2}·Σ_c (1 + |σc|)^{−(2σ−2)}`. -/
def cuspC (σ : ℝ) : ℝ :=
  cuspK σ * (2 ^ (2 * σ - 2) * ∑' c : 𝓞 K, (1 + ‖σO c‖) ^ (-(2 * σ - 2)))

theorem cuspC_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ cuspC σ := by
  unfold cuspC
  have := cuspK_pos hσ
  have : 0 ≤ ∑' c : 𝓞 K, (1 + ‖σO c‖) ^ (-(2 * σ - 2)) := tsum_nonneg fun c => by positivity
  positivity

open Classical in
/-- **The rows with `c ≠ 0`**, for `σ > 2` and `v ≥ 1/2`:
`Σ_{c≠0, d} (v/Q_w(c, d))^σ ≤ cuspC(σ)·v^{2−σ}`. -/
theorem tsum_height_ne_le {σ : ℝ} (hσ : 2 < σ) (z : ℂ) {v : ℝ} (hv : 1 / 2 ≤ v) :
    ∑' e : 𝓞 K × 𝓞 K,
        (if e.1 = 0 then 0 else ENNReal.ofReal ((v / uhsDen (σO e.1) (σO e.2) z v) ^ σ)) ≤
      ENNReal.ofReal (cuspC σ * v ^ (2 - σ)) := by
  have hv0 : 0 < v := by linarith
  have hK := cuspK_pos (by linarith : 1 < σ)
  rw [ENNReal.tsum_prod']
  calc ∑' (c : 𝓞 K) (d : 𝓞 K), (if (c, d).1 = 0 then 0 else
          ENNReal.ofReal ((v / uhsDen (σO (c, d).1) (σO (c, d).2) z v) ^ σ))
      ≤ ∑' c : 𝓞 K, ENNReal.ofReal (cuspK σ * v ^ (2 - σ)) *
          (if c = 0 then 0 else ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2)))) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        by_cases hc : c = 0
        · simp [hc]
        · simp only [hc, ↓reduceIte]
          calc ∑' d : 𝓞 K, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ σ)
              ≤ ENNReal.ofReal (cuspK σ * (‖σO c‖ ^ (-(2 * σ - 2)) * v ^ (2 - σ))) :=
                tsum_height_c_le (by linarith) hc z hv
            _ = ENNReal.ofReal (cuspK σ * v ^ (2 - σ)) *
                  ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2))) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                ring
    _ = ENNReal.ofReal (cuspK σ * v ^ (2 - σ)) *
          ∑' c : 𝓞 K, (if c = 0 then 0 else ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2)))) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (cuspK σ * v ^ (2 - σ)) *
          ENNReal.ofReal (2 ^ (2 * σ - 2) * ∑' c : 𝓞 K, (1 + ‖σO c‖) ^ (-(2 * σ - 2))) :=
        mul_le_mul_right (tsum_norm_σO_rpow_le (by linarith)) _
    _ = ENNReal.ofReal (cuspC σ * v ^ (2 - σ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold cuspC
        ring

open Classical in
/-- **The rows with `c ≠ 0`, summed**: summable, with sum at most `cuspC(σ)·v^{2−σ}`, for `σ > 2` and
`v ≥ 1/2`. -/
theorem summable_height_ne {σ : ℝ} (hσ : 2 < σ) (z : ℂ) {v : ℝ} (hv : 1 / 2 ≤ v) :
    Summable (fun e : 𝓞 K × 𝓞 K =>
        if e.1 = 0 then 0 else (v / uhsDen (σO e.1) (σO e.2) z v) ^ σ) ∧
      ∑' e : 𝓞 K × 𝓞 K, (if e.1 = 0 then 0 else (v / uhsDen (σO e.1) (σO e.2) z v) ^ σ) ≤
        cuspC σ * v ^ (2 - σ) := by
  have hv0 : 0 < v := by linarith
  set f : 𝓞 K × 𝓞 K → ℝ := fun e => if e.1 = 0 then 0 else (v / uhsDen (σO e.1) (σO e.2) z v) ^ σ
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    simp only [f]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (div_nonneg hv0.le (uhsDen_nonneg _ _ _ _)) _
  have he : ∀ e, ENNReal.ofReal (f e) =
      if e.1 = 0 then 0 else ENNReal.ofReal ((v / uhsDen (σO e.1) (σO e.2) z v) ^ σ) := by
    intro e
    simp only [f]
    split_ifs <;> simp
  have hB := tsum_height_ne_le hσ z hv
  simp_rw [← he] at hB
  have hfin : ∑' e, ENNReal.ofReal (f e) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  have hsum : Summable f := by
    have := ENNReal.summable_toReal hfin
    simpa only [ENNReal.toReal_ofReal (hf0 _)] using this
  refine ⟨hsum, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum] at hB
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (cuspC_nonneg (by linarith)) (Real.rpow_nonneg hv0.le _))).1 hB

/-- **Growth at `∞`**: `|E(w, s) − v^s| ≤ cuspC(σ)·v^{2−σ}` for `σ = Re s > 2` and `v ≥ 1/2`. -/
theorem norm_eis1_sub_le {s : ℂ} (hs : 2 < s.re) {p : ℂ × ℝ} (hv : 1 / 2 ≤ p.2) :
    ‖eis1 s p - ((p.2 : ℝ) : ℂ) ^ s‖ ≤ cuspC s.re * p.2 ^ (2 - s.re) := by
  have hp : p ∈ UHS := show 0 < p.2 by linarith
  rw [eis1_eq hs hp, add_sub_cancel_left]
  obtain ⟨hsum, hle⟩ := summable_height_ne hs p.1 hv
  refine (tsum_of_norm_bounded hsum.hasSum fun cd => ?_).trans hle
  by_cases h1 : cd.1 = 0
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    refine (norm_eisTerm_le s hp cd).trans ?_
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (div_nonneg hp.le (uhsDen_nonneg _ _ _ _)) _

open Classical in
/-- **The coefficient of `v^s` at the cusp `g·∞`**: `Σ (c/d)₃` over the bottom rows `(c, d)` of
`Γ_1(3)` with `(c, d)·g = (0, *)`. -/
def cuspA (g : SL(2, 𝓞 K)) : ℂ :=
  ∑' cd : 𝓞 K × 𝓞 K, if BRow cd ∧ (rowMul g cd).1 = 0 then σO (cub cd.1 (span {cd.2})) else 0

open Classical in
/-- At `g = 1` the coefficient is `1`: the only bottom row `(0, d)` is `(0, 1)`. -/
theorem cuspA_one : cuspA 1 = 1 := by
  unfold cuspA
  rw [tsum_eq_single ((0 : 𝓞 K), (1 : 𝓞 K)) fun cd hcd => ?_]
  · have h : BRow ((0 : 𝓞 K), (1 : 𝓞 K)) := bRow_zero_iff.2 rfl
    simp only [rowMul_one, h, true_and, ↓reduceIte]
    change σO (cub 0 (span {1})) = 1
    rw [cub_one_right, map_one]
  · rw [rowMul_one]
    refine ite_eq_right_iff.2 fun ⟨hb, h0⟩ => (hcd ?_).elim
    obtain ⟨c, d⟩ := cd
    simp only at h0
    subst h0
    rw [bRow_zero_iff.1 hb]

/-- A bottom row with `(c, d)·g = (0, e)` has `e` a unit. -/
theorem isUnit_rowMul_snd {g : SL(2, 𝓞 K)} {cd : 𝓞 K × 𝓞 K} (h : BRow cd)
    (h0 : (rowMul g cd).1 = 0) : IsUnit (rowMul g cd).2 := by
  have e : cd = rowMul g⁻¹ (rowMul g cd) := by rw [← rowMul_mul, mul_inv_cancel, rowMul_one]
  generalize rowMul g cd = r at h0 e ⊢
  subst e
  refine h.1.isUnit_of_dvd' ?_ ?_ <;>
    simp only [rowMul, h0, zero_mul, zero_add] <;> exact dvd_mul_right _ _

/-- The terms of the cusp `g·∞`: `(c/d)₃·v^s` at the rows with `(c, d)·g = (0, *)`. -/
theorem eisTerm_slAct_of_fst {g : SL(2, 𝓞 K)} {cd : 𝓞 K × 𝓞 K} (h : BRow cd)
    (h0 : (rowMul g cd).1 = 0) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eisTerm s (slAct g p) cd = σO (cub cd.1 (span {cd.2})) * ((p.2 : ℝ) : ℂ) ^ s := by
  unfold eisTerm
  simp only [h, ↓reduceIte]
  rw [height_rowMul g h hp, h0]
  obtain ⟨u, hu⟩ := isUnit_rowMul_snd h h0
  have hD : uhsDen (σO 0) (σO (u : 𝓞 K)) p.1 p.2 = 1 := by
    unfold uhsDen
    rw [map_zero, zero_mul, zero_add, normSq_σO_unit, Complex.normSq_zero, zero_mul, add_zero]
  rw [← hu, hD, div_one]

open Classical in
/-- **Growth at the cusp `g·∞`**: `|E(g·w, s) − a_g·v^s| ≤ cuspC(σ)·v^{2−σ}` for every
`g ∈ SL_2(ℤ[ω])`, `σ = Re s > 2` and `v ≥ 1/2`, with `a_g = cuspA g`. -/
theorem norm_eis1_slAct_sub_le {s : ℂ} (hs : 2 < s.re) (g : SL(2, 𝓞 K)) {p : ℂ × ℝ}
    (hv : 1 / 2 ≤ p.2) :
    ‖eis1 s (slAct g p) - cuspA g * ((p.2 : ℝ) : ℂ) ^ s‖ ≤ cuspC s.re * p.2 ^ (2 - s.re) := by
  have hp : p ∈ UHS := show 0 < p.2 by linarith
  have hgp : slAct g p ∈ UHS := slAct_mem g hp
  have hS := summable_eisTerm hs hgp
  set F := fun cd : 𝓞 K × 𝓞 K => eisTerm s (slAct g p) cd
  have hA : ∑' cd, (if (rowMul g cd).1 = 0 then F cd else 0) = cuspA g * ((p.2 : ℝ) : ℂ) ^ s := by
    unfold cuspA
    rw [← tsum_mul_right]
    refine tsum_congr fun cd => ?_
    by_cases h0 : (rowMul g cd).1 = 0
    · by_cases hb : BRow cd
      · simp only [h0, hb, and_self, ↓reduceIte, F]
        exact eisTerm_slAct_of_fst hb h0 s hp
      · simp only [h0, hb, and_true, ↓reduceIte, zero_mul, F]
        unfold eisTerm
        simp [hb]
    · simp [h0]
  have hN : Summable fun cd => ‖F cd‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_eisTerm_le s hgp)
      (summable_height_rpow hs hgp)
  have h1 : Summable fun cd => if (rowMul g cd).1 = 0 then F cd else 0 :=
    Summable.of_norm_bounded hN fun cd => by split_ifs <;> simp
  have h2 : Summable fun cd => if (rowMul g cd).1 = 0 then 0 else F cd :=
    Summable.of_norm_bounded hN fun cd => by split_ifs <;> simp
  have hsplit : eis1 s (slAct g p) = ∑' cd, (if (rowMul g cd).1 = 0 then F cd else 0) +
      ∑' cd, (if (rowMul g cd).1 = 0 then 0 else F cd) := by
    rw [← h1.tsum_add h2]
    refine tsum_congr fun cd => ?_
    split_ifs <;> simp [F]
  rw [hsplit, hA, add_sub_cancel_left]
  obtain ⟨hsum, hle⟩ := summable_height_ne hs p.1 hv
  refine (tsum_of_norm_bounded ((rowEquiv g).hasSum_iff.2 hsum.hasSum) fun cd => ?_).trans hle
  change _ ≤ (if (rowMul g cd).1 = 0 then 0 else
    (p.2 / uhsDen (σO (rowMul g cd).1) (σO (rowMul g cd).2) p.1 p.2) ^ s.re)
  by_cases h0 : (rowMul g cd).1 = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, F]
    refine (norm_eisTerm_le s hgp cd).trans ?_
    split_ifs with hb
    · rw [height_rowMul g hb hp]
    · exact Real.rpow_nonneg (div_nonneg hp.le (uhsDen_nonneg _ _ _ _)) _

end Eis

end

#print axioms Eis.fundP_eq_image
#print axioms Eis.volume_fundP
#print axioms Eis.norm_varpi
#print axioms Eis.norm_le_two_of_mem_fundP
#print axioms Eis.lintegral_tile
#print axioms Eis.integral_Ioi_mul_rpow
#print axioms Eis.lintegral_normSq_add_rpow
#print axioms Eis.normSq_add_le_mul
#print axioms Eis.rpow_le_of_mem_fundP
#print axioms Eis.measurable_normSq_add_rpow
#print axioms Eis.tsum_normSq_add_rpow_le
#print axioms Eis.cuspK_pos
#print axioms Eis.rpow_mul_sq_rpow
#print axioms Eis.tsum_height_c_le
#print axioms Eis.tsum_norm_σO_rpow_le
#print axioms Eis.cuspC_nonneg
#print axioms Eis.tsum_height_ne_le
#print axioms Eis.summable_height_ne
#print axioms Eis.norm_eis1_sub_le
#print axioms Eis.cuspA_one
#print axioms Eis.isUnit_rowMul_snd
#print axioms Eis.eisTerm_slAct_of_fst
#print axioms Eis.norm_eis1_slAct_sub_le
