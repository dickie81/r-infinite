import KubotaGrowth

/-! # The constant term of the cubic Eisenstein series at `∞` (round 389)

S5f-9b of round 360's plan, part 2. For `Re s > 2` and `v > 0`, the mean of round 387's `E(·, v; s)` over a
period parallelogram of `3ℤ[ω]` is `v^s + φ(s)v^{2−s}`, with `φ(s) = π/((9√3/2)(s − 1))·Σ_c S(c)N(c)^{−s}` and
`S(c) = Σ_{d mod 3c} (c/d)₃`.

* **Periodicity in `d`** (**`eisTerm_add`**, with `bRow_add_iff`, `cub_add_of_bRow` and `uhsDen_add`): the
  term at `(c, d + 3cx)` and `w` is the term at `(c, d)` and `w + 3σ(x)`, by round 382's
  `cub_add_three_mul`.
* **The period parallelogram of `3ℤ[ω]`** (`fundP3`, a definition; **`volume_fundP3`**, **`lintegral_tile3`**
  and **`integral_tile3`**, with `measurableSet_fundP3`, `fundP3_eq`, `σO_three_mul`, `tsum_fundP3`,
  `iUnion_fundP3` and `pairwise_disjoint_fundP3`): `3P` has area `9√3/2`, and its translates by `3ℤ[ω]`
  tile `ℂ`, for integrals of functions `≥ 0` and of integrable functions.
* **The radial integral at a complex exponent** (**`integral_normSq_add_cpow`**, with
  `integral_Ioi_mul_cpow`): `∫_ℂ (|x|² + B)^{−s} dx = πB^{1−s}/(s − 1)` for `B > 0` and `Re s > 1`.
* **One term over `ℂ`** (**`integral_height_cpow`** and **`lintegral_height_rpow`**, with
  `cpow_ofReal_eq_exp`, `integrable_normSq_add_rpow`, `uhsDen_eq_mul`, `height_cpow_eq`, `height_rpow_eq`
  and `integrable_height_cpow`): `∫_ℂ (v/Q_w(c, d))^s dz = πv^{2−s}|c|^{−2s}/(s − 1)` for `c ≠ 0`, `v > 0`
  and `Re s > 1`.
* **The sum over `d`** (`cuspS` and `resClassEquiv`, definitions; **`hasSum_integral_eisTerm_c`** and
  **`tsum_lintegral_height_c`**, with `three_mul_ne_zero`, `finite_quot_three_mul`, `card_quot_three_mul`,
  `resClassEquiv_apply`, `uhsDen_res`, `σO_ne_zero`, `measurable_height_rpow` and
  `norm_eisTerm_le_height`): for `c ≠ 0`, `Σ_d ∫_{3P} (term at (c, d)) dz = S(c)·πv^{2−s}N(c)^{−s}/(s − 1)`,
  with `d = rep(r) + 3cu` over the classes `r` modulo `3c`.
* **The constant term** (`eisPhi`, a definition; **`integral_eis1_fundP3`** and **`constTerm_eis1`**, with
  `measurable_eisTerm`, `eisTerm_zero_fst`, `rpow_normSq_eq` and `tsum_lintegral_eisTerm_ne_top`): the sum
  over `c` converges absolutely for `Re s > 2`, and `(9√3/2)⁻¹∫_{3P} E(z, v; s) dz = v^s + φ(s)v^{2−s}`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups Pointwise

noncomputable section

namespace Eis

/-! ### Periodicity in `d` modulo `3c` -/

theorem bRow_add_iff {c d : 𝓞 K} (x : 𝓞 K) : BRow (c, d + 3 * c * x) ↔ BRow (c, d) := by
  have key : ∀ {d : 𝓞 K} (x : 𝓞 K), BRow (c, d) → BRow (c, d + 3 * c * x) := by
    intro d x ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩
    · have := h1.add_mul_left_right (3 * x)
      convert this using 2
      ring
    · obtain ⟨t, ht⟩ := h3
      exact ⟨t + c * x, by linear_combination ht⟩
  constructor
  · intro h
    have := key (-x) h
    rwa [show d + 3 * c * x + 3 * c * -x = d by ring] at this
  · exact key x

theorem cub_add_of_bRow {c d : 𝓞 K} (h : BRow (c, d)) (x : 𝓞 K) :
    cub c (span {d + 3 * c * x}) = cub c (span {d}) :=
  cub_add_three_mul h.2.2 h.1.symm h.2.1 x

theorem uhsDen_add (c d x z : ℂ) (v : ℝ) :
    uhsDen c (d + c * x) z v = uhsDen c d (z + x) v := by
  unfold uhsDen
  congr 2
  ring

open Classical in
/-- **Periodicity**: the term at `(c, d + 3cx)` and `w` is the term at `(c, d)` and `w + 3σ(x)`. -/
theorem eisTerm_add (s : ℂ) (p : ℂ × ℝ) (c d x : 𝓞 K) :
    eisTerm s p (c, d + 3 * c * x) = eisTerm s (p.1 + σO (3 * x), p.2) (c, d) := by
  unfold eisTerm
  by_cases h : BRow (c, d)
  · have h' : BRow (c, d + 3 * c * x) := (bRow_add_iff x).2 h
    simp only [h, h', ↓reduceIte]
    rw [cub_add_of_bRow h x]
    congr 3
    rw [show d + 3 * c * x = d + c * (3 * x) by ring, map_add, map_mul, uhsDen_add]
  · have h' : ¬ BRow (c, d + 3 * c * x) := fun h'' => h ((bRow_add_iff x).1 h'')
    simp only [h, h', ↓reduceIte]

/-! ### The period parallelogram of `3ℤ[ω]` -/

/-- **The period parallelogram of `3ℤ[ω]`**: `3P`. -/
def fundP3 : Set ℂ := {z | z / 3 ∈ fundP}

theorem measurableSet_fundP3 : MeasurableSet fundP3 :=
  measurableSet_fundP.preimage (measurable_id.div_const 3)

theorem fundP3_eq : fundP3 = (3 : ℝ) • fundP := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by norm_num : (3 : ℝ) ≠ 0)]
  change z / 3 ∈ fundP ↔ _
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  rfl

/-- `vol(3P) = 9·√3/2`. -/
theorem volume_fundP3 : volume fundP3 = ENNReal.ofReal (9 * (Real.sqrt 3 / 2)) := by
  rw [fundP3_eq, Measure.addHaar_smul, volume_fundP, Complex.finrank_real_complex,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem σO_three_mul (t : 𝓞 K) : σO (3 * t) = 3 * σO t := by
  rw [map_mul, map_ofNat]

/-- **Translates of `3P`**: `Σ_{t∈ℤ[ω]} 1_{3P}(w + 3σ(t)) = 1`. -/
theorem tsum_fundP3 (w : ℂ) :
    ∑' t : 𝓞 K, fundP3.indicator (1 : ℂ → ℝ≥0∞) (w + σO (3 * t)) = 1 := by
  rw [← tsum_fundP (w / 3)]
  refine tsum_congr fun t => ?_
  have e : (w + σO (3 * t)) / 3 = w / 3 + σO t := by rw [σO_three_mul]; ring
  by_cases h : w / 3 + σO t ∈ fundP
  · have h' : w + σO (3 * t) ∈ fundP3 := by change _ / 3 ∈ fundP; rw [e]; exact h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rfl
  · have h' : w + σO (3 * t) ∉ fundP3 := by change ¬ _ / 3 ∈ fundP; rw [e]; exact h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **Tiling by `3P`**: `∫_ℂ G = Σ_{t∈ℤ[ω]} ∫_{3P} G(y + 3σ(t)) dy`. -/
theorem lintegral_tile3 {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∑' t : 𝓞 K, ∫⁻ y in fundP3, G (y + σO (3 * t)) := by
  have h1 : ∀ x, G x = ∑' t : 𝓞 K, fundP3.indicator (1 : ℂ → ℝ≥0∞) (x + σO (3 * -t)) * G x := by
    intro x
    have e := (Equiv.neg (𝓞 K)).tsum_eq
      (fun t => fundP3.indicator (1 : ℂ → ℝ≥0∞) (x + σO (3 * t)))
    simp only [Equiv.neg_apply] at e
    rw [ENNReal.tsum_mul_right, e, tsum_fundP3, one_mul]
  have hm : ∀ t : 𝓞 K,
      Measurable fun x => fundP3.indicator (1 : ℂ → ℝ≥0∞) (x + σO (3 * -t)) * G x :=
    fun t => ((measurable_one.indicator measurableSet_fundP3).comp (measurable_add_const _)).mul hG
  calc ∫⁻ x, G x = ∫⁻ x, ∑' t : 𝓞 K, fundP3.indicator (1 : ℂ → ℝ≥0∞) (x + σO (3 * -t)) * G x :=
        lintegral_congr fun x => h1 x
    _ = ∑' t : 𝓞 K, ∫⁻ x, fundP3.indicator (1 : ℂ → ℝ≥0∞) (x + σO (3 * -t)) * G x :=
        lintegral_tsum fun t => (hm t).aemeasurable
    _ = ∑' t : 𝓞 K, ∫⁻ y in fundP3, G (y + σO (3 * t)) := by
        refine tsum_congr fun t => ?_
        rw [← lintegral_add_right_eq_self _ (σO (3 * t))]
        rw [← lintegral_indicator measurableSet_fundP3]
        refine lintegral_congr fun x => ?_
        rw [show σO (3 * -t) = -σO (3 * t) by rw [mul_neg, map_neg], add_neg_cancel_right]
        by_cases hx : x ∈ fundP3
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]

/-- The translates `3P − 3σ(t)` cover `ℂ`. -/
theorem iUnion_fundP3 : (⋃ t : 𝓞 K, (fun x => x + σO (3 * t)) ⁻¹' fundP3) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t, ht⟩ := exists_transl_mem_fundP (x / 3)
  refine mem_iUnion.2 ⟨t, ?_⟩
  change (x + σO (3 * t)) / 3 ∈ fundP
  rw [σO_three_mul, show (x + 3 * σO t) / 3 = x / 3 + σO t by ring]
  exact ht

/-- The translates `3P − 3σ(t)` are disjoint. -/
theorem pairwise_disjoint_fundP3 :
    Pairwise (Function.onFun Disjoint fun t : 𝓞 K => (fun x => x + σO (3 * t)) ⁻¹' fundP3) := by
  intro t t' htt'
  refine Set.disjoint_left.2 fun x h h' => htt' ?_
  change (x + σO (3 * t)) / 3 ∈ fundP at h
  change (x + σO (3 * t')) / 3 ∈ fundP at h'
  have e : (x + σO (3 * t)) / 3 + σO (t' - t) = (x + σO (3 * t')) / 3 := by
    rw [σO_three_mul, σO_three_mul, map_sub]; ring
  rw [← e] at h'
  exact (sub_eq_zero.1 (eq_zero_of_mem_fundP h h')).symm

/-- **Tiling by `3P`, for integrable `f`**: `∫_ℂ f = Σ_{t∈ℤ[ω]} ∫_{3P} f(y − 3σ(t)) dy`. -/
theorem integral_tile3 {f : ℂ → ℂ} (hf : Integrable f) :
    ∫ x, f x = ∑' t : 𝓞 K, ∫ y in fundP3, f (y - σO (3 * t)) := by
  have hm : ∀ t : 𝓞 K, MeasurableSet ((fun x => x + σO (3 * t)) ⁻¹' fundP3) :=
    fun t => measurableSet_fundP3.preimage (measurable_add_const _)
  rw [← setIntegral_univ, ← iUnion_fundP3,
    integral_iUnion hm pairwise_disjoint_fundP3 hf.integrableOn]
  refine tsum_congr fun t => ?_
  have h := (measurePreserving_add_right volume (σO (3 * t))).setIntegral_preimage_emb
    (measurableEmbedding_addRight (σO (3 * t))) (fun y => f (y - σO (3 * t))) fundP3
  simp only [add_sub_cancel_right] at h
  exact h

/-- `∫_0^∞ r(r² + B)^{−s} dr = B^{1−s}/(2(s − 1))` for `Re s > 1`. -/
theorem integral_Ioi_mul_cpow {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 < s.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((r ^ 2 + B : ℝ) : ℂ) ^ (-s) =
      (B : ℂ) ^ (1 - s) / (2 * (s - 1)) := by
  have hpos : ∀ r : ℝ, 0 < r ^ 2 + B := fun r => by positivity
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  set g : ℝ → ℂ := fun r => -(((r ^ 2 + B : ℝ) : ℂ) ^ (1 - s)) / (2 * (s - 1))
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g ((x : ℂ) * ((x ^ 2 + B : ℝ) : ℂ) ^ (-s)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => ((r ^ 2 + B : ℝ) : ℂ)) ((2 * x : ℝ) : ℂ) x := by
      have := ((hasDerivAt_pow 2 x).add_const B).ofReal_comp
      simpa using this
    have hslit : ((x ^ 2 + B : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (hpos x)
    have h2 := ((Complex.hasStrictDerivAt_cpow_const (c := 1 - s) hslit).hasDerivAt).comp x h1
    have h3 := (h2.neg).div_const (2 * (s - 1))
    convert h3 using 1
    · rfl
    rw [show (1 - s - 1 : ℂ) = -s by ring]
    field_simp
    push_cast
    ring
  have hσ : 1 < s.re := hs
  have hint : IntegrableOn (fun r : ℝ => (r : ℂ) * ((r ^ 2 + B : ℝ) : ℂ) ^ (-s)) (Ioi 0) := by
    refine Integrable.mono' (integral_Ioi_mul_rpow hB hσ).2 ?_ ?_
    · exact (by fun_prop : Measurable fun r : ℝ =>
        (r : ℂ) * ((r ^ 2 + B : ℝ) : ℂ) ^ (-s)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_cpow_eq_rpow_re_of_pos (hpos r), Complex.neg_re]
  have hlim : Tendsto g atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun r : ℝ => r ^ 2 + B) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
    have h0 := ((tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp ht).div_const
      ‖2 * (s - 1)‖
    rw [zero_div] at h0
    refine h0.congr fun r => ?_
    simp only [g, Function.comp_apply, norm_div, norm_neg]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos r)]
    congr 2
    simp
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [g]
  rw [show ((0 : ℝ) ^ 2 + B) = B by ring]
  ring

/-- **The radial integral at a complex exponent**: `∫_ℂ (|x|² + B)^{−s} dx = πB^{1−s}/(s − 1)` for
`B > 0` and `Re s > 1`. -/
theorem integral_normSq_add_cpow {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 < s.re) :
    ∫ x : ℂ, ((Complex.normSq x + B : ℝ) : ℂ) ^ (-s) =
      Real.pi * (B : ℂ) ^ (1 - s) / (s - 1) := by
  have hI := integral_Ioi_mul_cpow hB hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun hmeas (g := fun p : ℝ × ℝ =>
    ((p.1 : ℂ) * ((p.1 ^ 2 + B : ℝ) : ℂ) ^ (-s)) * (1 : ℂ)) (fun p hp => ?_)]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      integral_prod_mul (fun r : ℝ => (r : ℂ) * ((r ^ 2 + B : ℝ) : ℂ) ^ (-s)) (fun _ : ℝ => (1 : ℂ)),
      hI, integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    rw [Complex.real_smul, mul_one]
    push_cast
    field_simp
    ring
  · have hr : 0 < p.1 := hp.1
    simp only [mul_one]
    rw [Complex.real_smul, Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, abs_of_pos hr]

theorem cpow_ofReal_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (Real.log x * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le]

/-- `(|x|² + A)^{−σ}` is integrable on `ℂ` for `A > 0` and `σ > 1`. -/
theorem integrable_normSq_add_rpow {A σ : ℝ} (hA : 0 < A) (hσ : 1 < σ) :
    Integrable fun x : ℂ => (Complex.normSq x + A) ^ (-σ) := by
  refine ⟨(by fun_prop : Measurable fun x : ℂ => (Complex.normSq x + A) ^ (-σ)).aestronglyMeasurable,
    ?_⟩
  have h := lintegral_normSq_add_rpow hA hσ
  unfold HasFiniteIntegral
  have e : ∀ x : ℂ, ‖(Complex.normSq x + A) ^ (-σ)‖ₑ =
      ENNReal.ofReal ((Complex.normSq x + A) ^ (-σ)) := fun x =>
    Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith [Complex.normSq_nonneg x]) _)
  simp_rw [e, h]
  exact ENNReal.ofReal_lt_top

/-- `Q_w(c, d) = |c|²(|z + d/c|² + v²)`. -/
theorem uhsDen_eq_mul {c : ℂ} (hc : c ≠ 0) (d z : ℂ) (v : ℝ) :
    uhsDen c d z v = Complex.normSq c * (Complex.normSq (z + d / c) + v ^ 2) := by
  unfold uhsDen
  rw [show c * z + d = c * (z + d / c) by field_simp, Complex.normSq_mul]
  ring

/-- `(v/Q_w(c, d))^s = (v/|c|²)^s·(|z + d/c|² + v²)^{−s}`. -/
theorem height_cpow_eq {c : ℂ} (hc : c ≠ 0) (d z : ℂ) {v : ℝ} (hv : 0 < v) (s : ℂ) :
    ((v / uhsDen c d z v : ℝ) : ℂ) ^ s =
      ((v / Complex.normSq c : ℝ) : ℂ) ^ s *
        ((Complex.normSq (z + d / c) + v ^ 2 : ℝ) : ℂ) ^ (-s) := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  have hX : 0 < Complex.normSq (z + d / c) + v ^ 2 := by
    have := Complex.normSq_nonneg (z + d / c)
    positivity
  rw [uhsDen_eq_mul hc, show v / (Complex.normSq c * (Complex.normSq (z + d / c) + v ^ 2)) =
      (v / Complex.normSq c) * (Complex.normSq (z + d / c) + v ^ 2)⁻¹ by field_simp,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    cpow_ofReal_eq_exp (inv_pos.2 hX), cpow_ofReal_eq_exp hX, Real.log_inv]
  congr 2
  push_cast
  ring

/-- The terms are integrable over `ℂ` in `z`, for `c ≠ 0` and `Re s > 1`. -/
theorem integrable_height_cpow {c : ℂ} (hc : c ≠ 0) (d : ℂ) {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    Integrable fun z : ℂ => ((v / uhsDen c d z v : ℝ) : ℂ) ^ s := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  have hg := ((integrable_normSq_add_rpow (A := v ^ 2) (by positivity) hs).comp_add_right
    (d / c)).const_mul ((v / Complex.normSq c) ^ s.re)
  refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
  · have hm : Measurable fun z : ℂ => ((v / uhsDen c d z v : ℝ) : ℂ) ^ s := by
      unfold uhsDen
      fun_prop
    exact hm.aestronglyMeasurable
  · have hX : 0 < Complex.normSq (z + d / c) + v ^ 2 := by
      have := Complex.normSq_nonneg (z + d / c)
      positivity
    rw [height_cpow_eq hc d z hv s, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hv hN),
      Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.neg_re]

/-- **The integral of a term over `ℂ`**: `∫_ℂ (v/Q_w(c, d))^s dz = πv^{2−s}|c|^{−2s}/(s − 1)` for
`c ≠ 0`, `v > 0` and `Re s > 1`. -/
theorem integral_height_cpow {c : ℂ} (hc : c ≠ 0) (d : ℂ) {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ z : ℂ, ((v / uhsDen c d z v : ℝ) : ℂ) ^ s =
      Real.pi * (v : ℂ) ^ (2 - s) * ((Complex.normSq c : ℝ) : ℂ) ^ (-s) / (s - 1) := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  simp_rw [height_cpow_eq hc d _ hv s]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun z : ℂ => ((Complex.normSq z + v ^ 2 : ℝ) : ℂ) ^ (-s)) (d / c),
    integral_normSq_add_cpow (by positivity) hs]
  have key : ((v / Complex.normSq c : ℝ) : ℂ) ^ s * ((v ^ 2 : ℝ) : ℂ) ^ (1 - s) =
      (v : ℂ) ^ (2 - s) * ((Complex.normSq c : ℝ) : ℂ) ^ (-s) := by
    rw [cpow_ofReal_eq_exp (div_pos hv hN), cpow_ofReal_eq_exp (pow_pos hv 2),
      cpow_ofReal_eq_exp hv, cpow_ofReal_eq_exp hN, ← Complex.exp_add, ← Complex.exp_add,
      Real.log_div hv.ne' hN.ne', Real.log_pow]
    congr 1
    push_cast
    ring
  rw [show ((v / Complex.normSq c : ℝ) : ℂ) ^ s * (Real.pi * ((v ^ 2 : ℝ) : ℂ) ^ (1 - s) / (s - 1)) =
      Real.pi * (((v / Complex.normSq c : ℝ) : ℂ) ^ s * ((v ^ 2 : ℝ) : ℂ) ^ (1 - s)) / (s - 1) by ring,
    key]
  ring

theorem three_mul_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : (3 : 𝓞 K) * c ≠ 0 := by
  have h3 : (3 : 𝓞 K) ≠ 0 := fun h0 => by
    have := congrArg ((↑) : 𝓞 K → K) h0; norm_num at this
  exact mul_ne_zero h3 hc

theorem finite_quot_three_mul {c : 𝓞 K} (hc : c ≠ 0) : Finite (𝓞 K ⧸ span {3 * c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact three_mul_ne_zero hc)

/-- `#(ℤ[ω]/3c) = 9N(c)`. -/
theorem card_quot_three_mul (c : 𝓞 K) :
    (Nat.card (𝓞 K ⧸ span {3 * c}) : ℝ) = 9 * Complex.normSq (σO c) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← normSq_σO, map_mul, Complex.normSq_mul,
    map_ofNat]
  norm_num [Complex.normSq_apply]

open Classical in
/-- **The sum of the character over the classes modulo `3c`**:
`S(c) = Σ_{d mod 3c} (c/d)₃` over the classes of the `d` with `(c, d)` a bottom row of `Γ_1(3)`. -/
def cuspS (c : 𝓞 K) : ℂ :=
  ∑' r : 𝓞 K ⧸ span {3 * c},
    if BRow (c, repQ (3 * c) r) then σO (cub c (span {repQ (3 * c) r})) else 0

/-- The decomposition `d = rep(r) + 3cu`, `r` a class modulo `3c`. -/
def resClassEquiv {c : 𝓞 K} (hc : c ≠ 0) : (𝓞 K ⧸ span {3 * c}) × 𝓞 K ≃ 𝓞 K :=
  Equiv.ofBijective _ (repQ_bijective (3 * c) (three_mul_ne_zero hc))

theorem resClassEquiv_apply {c : 𝓞 K} (hc : c ≠ 0) (p : (𝓞 K ⧸ span {3 * c}) × 𝓞 K) :
    resClassEquiv hc p = repQ (3 * c) p.1 + 3 * c * p.2 := rfl

theorem uhsDen_res (c ρ u : 𝓞 K) (z : ℂ) (v : ℝ) :
    uhsDen (σO c) (σO (ρ + 3 * c * u)) z v = uhsDen (σO c) (σO ρ) (z + σO (3 * u)) v := by
  rw [show ρ + 3 * c * u = ρ + c * (3 * u) by ring, map_add, map_mul, uhsDen_add]

/-- `(v/Q_w(c, d))^σ = (v/|c|²)^σ·(|z + d/c|² + v²)^{−σ}`. -/
theorem height_rpow_eq {c : ℂ} (hc : c ≠ 0) (d z : ℂ) {v : ℝ} (hv : 0 < v) (σ : ℝ) :
    (v / uhsDen c d z v) ^ σ =
      (v / Complex.normSq c) ^ σ * (Complex.normSq (z + d / c) + v ^ 2) ^ (-σ) := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  have hX : 0 < Complex.normSq (z + d / c) + v ^ 2 := by
    have := Complex.normSq_nonneg (z + d / c)
    positivity
  rw [uhsDen_eq_mul hc, show v / (Complex.normSq c * (Complex.normSq (z + d / c) + v ^ 2)) =
      (v / Complex.normSq c) * (Complex.normSq (z + d / c) + v ^ 2)⁻¹ by field_simp,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hX.le, Real.rpow_neg hX.le]

/-- `∫_ℂ (v/Q_w(c, d))^σ dz = πv^{2−σ}|c|^{−2σ}/(σ − 1)` for `c ≠ 0`, `v > 0` and `σ > 1`. -/
theorem lintegral_height_rpow {c : ℂ} (hc : c ≠ 0) (d : ℂ) {v σ : ℝ} (hv : 0 < v) (hσ : 1 < σ) :
    ∫⁻ z : ℂ, ENNReal.ofReal ((v / uhsDen c d z v) ^ σ) =
      ENNReal.ofReal (Real.pi * v ^ (2 - σ) * Complex.normSq c ^ (-σ) / (σ - 1)) := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  simp_rw [height_rpow_eq hc d _ hv σ, ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hv hN).le σ)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right_eq_self (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z + v ^ 2) ^ (-σ))) (d / c),
    lintegral_normSq_add_rpow (by positivity) hσ, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hσ1 : 0 < σ - 1 := by linarith
  rw [Real.div_rpow hv.le hN.le, show (v ^ 2) ^ (1 - σ) = v ^ (2 - 2 * σ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]; norm_num; ring_nf,
    show v ^ (2 - σ) = v ^ σ * v ^ (2 - 2 * σ) by rw [← Real.rpow_add hv]; ring_nf,
    Real.rpow_neg hN.le]
  field_simp

theorem σO_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : σO c ≠ 0 :=
  fun h => hc (σO_injective (h.trans (map_zero σO).symm))

theorem measurable_height_rpow (c d : ℂ) (v σ : ℝ) :
    Measurable fun z : ℂ => ENNReal.ofReal ((v / uhsDen c d z v) ^ σ) := by
  unfold uhsDen
  fun_prop

/-- **The sum over `d` against `3P`, in `[0, ∞]`**: for `c ≠ 0`, `v > 0` and `σ > 1`,
`Σ_d ∫_{3P} (v/Q_w(c, d))^σ dz = 9πv^{2−σ}N(c)^{1−σ}/(σ − 1)`. -/
theorem tsum_lintegral_height_c {c : 𝓞 K} (hc : c ≠ 0) {v σ : ℝ} (hv : 0 < v) (hσ : 1 < σ) :
    ∑' d : 𝓞 K, ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ σ) =
      ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) * Complex.normSq (σO c) ^ (1 - σ) / (σ - 1)) := by
  have := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  have hN : 0 < Complex.normSq (σO c) := Complex.normSq_pos.2 (σO_ne_zero hc)
  have hσ1 : 0 < σ - 1 := by linarith
  have hr : ∀ r : 𝓞 K ⧸ span {3 * c}, ∑' u : 𝓞 K, ∫⁻ z in fundP3,
      ENNReal.ofReal ((v / uhsDen (σO c) (σO (repQ (3 * c) r + 3 * c * u)) z v) ^ σ) =
        ENNReal.ofReal (Real.pi * v ^ (2 - σ) * Complex.normSq (σO c) ^ (-σ) / (σ - 1)) := by
    intro r
    simp_rw [uhsDen_res]
    rw [← lintegral_tile3 (measurable_height_rpow _ _ v σ),
      lintegral_height_rpow (σO_ne_zero hc) _ hv hσ]
  rw [← (resClassEquiv hc).tsum_eq, ENNReal.tsum_prod']
  simp_rw [resClassEquiv_apply]
  simp_rw [hr]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    show (Fintype.card (𝓞 K ⧸ span {3 * c}) : ℝ≥0∞) =
      ENNReal.ofReal (Fintype.card (𝓞 K ⧸ span {3 * c}) : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity), ← Nat.card_eq_fintype_card, card_quot_three_mul]
  congr 1
  rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add hN, Real.rpow_one]
  field_simp

theorem norm_eisTerm_le_height (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    ‖eisTerm s p cd‖ ≤ (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ s.re := by
  refine (norm_eisTerm_le s hp cd).trans ?_
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (div_nonneg (le_of_lt hp) (uhsDen_nonneg _ _ _ _)) _

open Classical in
/-- **The sum over `d` of the integrals over `3P`**: for `c ≠ 0`, `v > 0` and `Re s > 1`,
`Σ_d ∫_{3P} (term at (c, d)) dz = S(c)·πv^{2−s}N(c)^{−s}/(s − 1)`. -/
theorem hasSum_integral_eisTerm_c {c : 𝓞 K} (hc : c ≠ 0) {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun d : 𝓞 K => ∫ z in fundP3, eisTerm s (z, v) (c, d))
      (cuspS c * (Real.pi * (v : ℂ) ^ (2 - s) * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) /
        (s - 1))) := by
  have := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  set F := fun d : 𝓞 K => ∫ z in fundP3, eisTerm s (z, v) (c, d) with hF
  set G := fun d : 𝓞 K =>
    ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ s.re) with hG
  have hGtop : ∑' d, G d ≠ ⊤ := by
    rw [hG, tsum_lintegral_height_c hc hv hs]
    exact ENNReal.ofReal_ne_top
  have hB : ∀ d, ‖F d‖ ≤ (G d).toReal := by
    intro d
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.ne_top_of_tsum_ne_top hGtop d) (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_))
    exact norm_eisTerm_le_height s (p := (z, v)) hv (c, d)
  have hsum : Summable F := Summable.of_norm_bounded (ENNReal.summable_toReal hGtop) hB
  have hsum' : Summable fun p => F (resClassEquiv hc p) := (resClassEquiv hc).summable_iff.2 hsum
  rw [hsum.hasSum_iff, ← (resClassEquiv hc).tsum_eq, hsum'.tsum_prod' hsum'.prod_factor, tsum_fintype]
  unfold cuspS
  rw [tsum_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  set f : ℂ → ℂ := fun z => eisTerm s (z, v) (c, repQ (3 * c) r) with hf_def
  have hf : Integrable f := by
    simp only [hf_def]
    unfold eisTerm
    split_ifs
    · exact (integrable_height_cpow (σO_ne_zero hc) _ hv hs).const_mul _
    · exact integrable_zero _ _ _
  have h1 : ∀ u : 𝓞 K, F (resClassEquiv hc (r, u)) = ∫ y in fundP3, f (y - σO (3 * -u)) := by
    intro u
    simp only [hF, resClassEquiv_apply, hf_def]
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [eisTerm_add, mul_neg, map_neg, sub_neg_eq_add]
  have h2 := (Equiv.neg (𝓞 K)).tsum_eq (fun t => ∫ y in fundP3, f (y - σO (3 * t)))
  simp only [Equiv.neg_apply] at h2
  rw [tsum_congr h1, h2, ← integral_tile3 hf]
  simp only [hf_def]
  unfold eisTerm
  split_ifs with hb
  · rw [integral_const_mul, integral_height_cpow (σO_ne_zero hc) _ hv hs]
  · simp

theorem measurable_eisTerm (s : ℂ) (v : ℝ) (cd : 𝓞 K × 𝓞 K) :
    Measurable fun z : ℂ => eisTerm s (z, v) cd := by
  unfold eisTerm
  split_ifs
  · refine measurable_const.mul ?_
    have : Measurable fun z : ℂ => (v / uhsDen (σO cd.1) (σO cd.2) z v) := by
      unfold uhsDen
      fun_prop
    exact (Complex.measurable_ofReal.comp this).pow_const s
  · exact measurable_const

open Classical in
/-- The rows with `c = 0`: only `(0, 1)` contributes, with the term `v^s`. -/
theorem eisTerm_zero_fst (s : ℂ) (p : ℂ × ℝ) (d : 𝓞 K) :
    eisTerm s p (0, d) = if d = 1 then ((p.2 : ℝ) : ℂ) ^ s else 0 := by
  split_ifs with h
  · rw [h, eisTerm_zero_one]
  · have hb : ¬ BRow ((0 : 𝓞 K), d) := fun hb => h (bRow_zero_iff.1 hb)
    unfold eisTerm
    simp only [hb, ↓reduceIte]

theorem rpow_normSq_eq (x : ℂ) (σ : ℝ) :
    Complex.normSq x ^ (1 - σ) = ‖x‖ ^ (-(2 * σ - 2)) := by
  rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

open Classical in
/-- **The majorant of the integrals over `3P`**, in `[0, ∞]`: finite for `σ = Re s > 2` and `v > 0`. -/
theorem tsum_lintegral_eisTerm_ne_top {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3, ‖eisTerm s (z, v) cd‖ₑ ≠ ⊤ := by
  set σ := s.re with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσ1' : 0 < σ - 1 := by linarith
  set A : ℝ≥0∞ := ENNReal.ofReal (v ^ σ) * volume fundP3
  set B : ℝ≥0∞ := ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) / (σ - 1))
  have hslice : ∀ c : 𝓞 K, ∑' d : 𝓞 K, ∫⁻ z in fundP3, ‖eisTerm s (z, v) (c, d)‖ₑ ≤
      (if c = 0 then A else 0) + B * (if c = 0 then 0 else ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2)))) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [↓reduceIte, mul_zero, add_zero]
      simp_rw [eisTerm_zero_fst]
      have e : ∀ d : 𝓞 K, ∫⁻ z in fundP3, ‖(if d = 1 then ((v : ℝ) : ℂ) ^ s else 0)‖ₑ =
          if d = 1 then A else 0 := by
        intro d
        split_ifs
        · rw [setLIntegral_const, ← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hv]
        · simp
      simp_rw [e]
      rw [tsum_ite_eq]
    · simp only [hc, ↓reduceIte, zero_add]
      calc ∑' d : 𝓞 K, ∫⁻ z in fundP3, ‖eisTerm s (z, v) (c, d)‖ₑ
          ≤ ∑' d : 𝓞 K, ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ σ) := by
            refine ENNReal.tsum_le_tsum fun d => lintegral_mono fun z => ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_eisTerm_le_height s (p := (z, v)) hv (c, d))
        _ = ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) * Complex.normSq (σO c) ^ (1 - σ) / (σ - 1)) :=
            tsum_lintegral_height_c hc hv hσ1
        _ = B * ENNReal.ofReal (‖σO c‖ ^ (-(2 * σ - 2))) := by
            rw [← ENNReal.ofReal_mul (by positivity),
              rpow_normSq_eq]
            congr 1
            ring
  refine ne_top_of_le_ne_top ?_ ((ENNReal.tsum_prod').le.trans (ENNReal.tsum_le_tsum hslice))
  rw [ENNReal.tsum_add, tsum_ite_eq, ENNReal.tsum_mul_left]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (volume_fundP3 ▸ ENNReal.ofReal_ne_top), ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_norm_σO_rpow_le (by linarith))

open Classical in
/-- **The integral of `E` over a period**: for `Re s > 2` and `v > 0`,
`∫_{3P} E(z, v; s) dz = (9√3/2)v^s + πv^{2−s}/(s − 1)·Σ_c S(c)N(c)^{−s}`. -/
theorem integral_eis1_fundP3 {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, eis1 s (z, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s +
        Real.pi * (v : ℂ) ^ (2 - s) / (s - 1) *
          ∑' c : 𝓞 K, cuspS c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  have hfin := tsum_lintegral_eisTerm_ne_top hs hv
  set I := fun cd : 𝓞 K × 𝓞 K => ∫ z in fundP3, eisTerm s (z, v) cd with hI
  have hI_le : ∀ cd, ‖I cd‖ ≤ (∫⁻ z in fundP3, ‖eisTerm s (z, v) cd‖ₑ).toReal := by
    intro cd
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp_rw [ofReal_norm]
  have hIsum : Summable I := Summable.of_norm_bounded (ENNReal.summable_toReal hfin) hI_le
  have h1 : ∫ z in fundP3, eis1 s (z, v) = ∑' cd, I cd := by
    unfold eis1
    exact integral_tsum (fun cd => (measurable_eisTerm s v cd).aestronglyMeasurable) hfin
  set J := fun c : 𝓞 K => ∑' d : 𝓞 K, I (c, d) with hJ
  have hJsum : Summable J := hIsum.prod
  have hJ0 : J 0 = ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s := by
    have e : ∀ d : 𝓞 K, I (0, d) = if d = 1 then ∫ _ in fundP3, ((v : ℝ) : ℂ) ^ s else 0 := by
      intro d
      simp only [hI, eisTerm_zero_fst]
      split_ifs <;> simp
    simp only [hJ, e, tsum_ite_eq]
    rw [setIntegral_const, Measure.real, volume_fundP3, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul]
  have hJc : ∀ c : 𝓞 K, c ≠ 0 → J c = Real.pi * (v : ℂ) ^ (2 - s) / (s - 1) *
      (cuspS c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) := by
    intro c hc
    show ∑' d : 𝓞 K, ∫ z in fundP3, eisTerm s (z, v) (c, d) = _
    rw [(hasSum_integral_eisTerm_c hc hv (by linarith)).tsum_eq]
    ring
  have hs0 : -s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [h1, hIsum.tsum_prod' hIsum.prod_factor]
  change ∑' c, J c = _
  rw [hJsum.tsum_eq_add_tsum_ite 0, hJ0, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun c => ?_
  split_ifs with hc
  · rw [hc, map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0]
    ring
  · exact hJc c hc

/-- **The scattering coefficient at `∞`**: `φ(s) = π/((9√3/2)(s − 1))·Σ_c S(c)N(c)^{−s}`. -/
def eisPhi (s : ℂ) : ℂ :=
  Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1)) *
    ∑' c : 𝓞 K, cuspS c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)

/-- **The constant term at `∞`**: the mean of `E(·, v; s)` over a period of `3ℤ[ω]` is
`v^s + φ(s)v^{2−s}`, for `Re s > 2` and `v > 0`. -/
theorem constTerm_eis1 {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ))⁻¹ * ∫ z in fundP3, eis1 s (z, v) =
      ((v : ℝ) : ℂ) ^ s + eisPhi s * ((v : ℝ) : ℂ) ^ (2 - s) := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h9 : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  rw [integral_eis1_fundP3 hs hv]
  unfold eisPhi
  field_simp

end Eis

end

#print axioms Eis.bRow_add_iff
#print axioms Eis.cub_add_of_bRow
#print axioms Eis.uhsDen_add
#print axioms Eis.eisTerm_add
#print axioms Eis.measurableSet_fundP3
#print axioms Eis.fundP3_eq
#print axioms Eis.volume_fundP3
#print axioms Eis.σO_three_mul
#print axioms Eis.tsum_fundP3
#print axioms Eis.lintegral_tile3
#print axioms Eis.iUnion_fundP3
#print axioms Eis.pairwise_disjoint_fundP3
#print axioms Eis.integral_tile3
#print axioms Eis.integral_Ioi_mul_cpow
#print axioms Eis.integral_normSq_add_cpow
#print axioms Eis.cpow_ofReal_eq_exp
#print axioms Eis.integrable_normSq_add_rpow
#print axioms Eis.uhsDen_eq_mul
#print axioms Eis.height_cpow_eq
#print axioms Eis.integrable_height_cpow
#print axioms Eis.integral_height_cpow
#print axioms Eis.three_mul_ne_zero
#print axioms Eis.finite_quot_three_mul
#print axioms Eis.card_quot_three_mul
#print axioms Eis.resClassEquiv_apply
#print axioms Eis.uhsDen_res
#print axioms Eis.height_rpow_eq
#print axioms Eis.lintegral_height_rpow
#print axioms Eis.σO_ne_zero
#print axioms Eis.measurable_height_rpow
#print axioms Eis.tsum_lintegral_height_c
#print axioms Eis.norm_eisTerm_le_height
#print axioms Eis.hasSum_integral_eisTerm_c
#print axioms Eis.measurable_eisTerm
#print axioms Eis.eisTerm_zero_fst
#print axioms Eis.rpow_normSq_eq
#print axioms Eis.tsum_lintegral_eisTerm_ne_top
#print axioms Eis.integral_eis1_fundP3
#print axioms Eis.constTerm_eis1
