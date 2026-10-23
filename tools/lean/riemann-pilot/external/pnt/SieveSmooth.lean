/-
# Round 588: the smooth cut-off of `frontier/linnik/SIEVE-ROUTE.md` §10, and the separation of two variables

Plain statement. Let `g` be Mathlib's `Real.smoothTransition`, which is `0` on `(−∞, 0]` and `1` on `[1, ∞)`. For
`θ > 0` and `Λ ≥ 0` put `G(u) = g(u/θ) − g((u − 2Λ)/θ)` (`G`, and `GC` with complex values). Then:

* `G` is smooth, takes values in `[0, 1]` when `θ ≤ 2Λ`, and vanishes outside `[0, 2Λ + θ]` (`contDiff_G`, `G_nonneg`,
  `G_le_one`, `G_eq_zero`).
* For `u ≤ Λ`, the indicator `1[u > 0]` or `1[u ≥ 0]` minus `G(u)` lies in `[0, 1]` and vanishes unless `0 ≤ u < θ`
  (`indicator_sub_G`). This is the smoothing error of SIEVE-ROUTE.md's Lemma 4′.
* `G^{(K)}(u) = θ^{−K}(g^{(K)}(u/θ) − g^{(K)}((u − 2Λ)/θ))` (`iteratedDeriv_GC`), and for `K ≥ 1` the derivative
  `g^{(K)}` vanishes outside `[0, 1]` and is integrable, so `‖G^{(K)}‖₁ ≤ 2θ^{1−K}‖g^{(K)}‖₁`
  (`integral_norm_iteratedDeriv_GC_le`).
* `(2π|ξ|)^K‖𝓕G(ξ)‖ ≤ 2θ^{1−K}‖g^{(K)}‖₁` for `K ≥ 1` (`pow_mul_norm_fourier_GC_le`), from
  `(2π|ξ|)^K‖𝓕f(ξ)‖ ≤ ‖f^{(K)}‖₁` (`pow_mul_norm_fourier_le`, by Mathlib's `Real.fourier_iteratedDeriv`).
* `𝓕G` is integrable (`integrable_fourier_GC`): `(1 + ξ²)‖𝓕G(ξ)‖ ≤ ‖G‖₁ + ‖G″‖₁/(4π²)`.
* **Separation.** `G(a − b) = ∫ e^{2πiξa} e^{−2πiξb} 𝓕G(ξ) dξ` for real `a` and `b` (`GC_sub_eq_integral`, by
  Mathlib's `Continuous.fourierInv_fourier_eq`). With `a = log Z` and `b = log Y`, the smoothed comparison
  `G(log Z − log Y)` is an integral of `Z^{2πiξ}Y^{−2πiξ}` against `𝓕G`, which decays like `(θ|ξ|)^{−K}`.

SIEVE-ROUTE.md §10 writes the cut-off as `g(u/θ)c(u/Λ)` with a second bump `c`. On `u ≤ Λ` the two agree, and every
property §10 uses holds for this form, with support `[0, 2Λ + θ]` in place of `[0, 2Λ]`. Mathlib's `𝓕` is
`ξ ↦ ∫ e^{−2πixξ}f(x) dx`, so its heights are `2πξ`. The file imports only Mathlib.
-/
import Mathlib

open MeasureTheory Real Complex FourierTransform Set

namespace SieveSmooth

/-- `(2π|ξ|)^K ‖𝓕 f(ξ)‖ ≤ ∫ ‖f^{(K)}‖` for `f` of class `C^K` with integrable derivatives up to order `K`. -/
theorem pow_mul_norm_fourier_le {f : ℝ → ℂ} {K : ℕ} (hf : ContDiff ℝ K f)
    (hint : ∀ n : ℕ, n ≤ K → Integrable (iteratedDeriv n f)) (ξ : ℝ) :
    (2 * π * |ξ|) ^ K * ‖𝓕 f ξ‖ ≤ ∫ x, ‖iteratedDeriv K f x‖ := by
  have h := Real.fourier_iteratedDeriv (N := (K : ℕ∞)) (n := K) (by exact_mod_cast hf)
    (fun n hn => hint n (by exact_mod_cast hn)) le_rfl
  have hle : ‖𝓕 (iteratedDeriv K f) ξ‖ ≤ ∫ x, ‖iteratedDeriv K f x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [h] at hle
  have hn : ‖(2 * π * I * (ξ : ℂ)) ^ K‖ = (2 * π * |ξ|) ^ K := by
    rw [norm_pow]
    congr 1
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  simpa [norm_smul, hn] using hle

end SieveSmooth

namespace SieveSmooth

/-- The cut-off `G θ Λ u = g(u/θ) − g((u − 2Λ)/θ)`, `g = Real.smoothTransition`. -/
noncomputable def G (θ Λ : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition (u / θ) - Real.smoothTransition ((u - 2 * Λ) / θ)

variable {θ Λ : ℝ}

theorem contDiff_G {n : ℕ∞} : ContDiff ℝ n (G θ Λ) := by
  unfold G
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.div_const θ)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const θ))

/-- Below `2Λ`, `G` is `g(u/θ)`. -/
theorem G_of_le (hθ : 0 < θ) {u : ℝ} (hu : u ≤ 2 * Λ) : G θ Λ u = Real.smoothTransition (u / θ) := by
  have h : (u - 2 * Λ) / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
  rw [G, Real.smoothTransition.zero_of_nonpos h, sub_zero]

theorem G_nonneg (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) (u : ℝ) : 0 ≤ G θ Λ u := by
  by_cases hu : u ≤ 2 * Λ
  · rw [G_of_le hθ hu]; exact Real.smoothTransition.nonneg _
  · have h1 : 1 ≤ u / θ := by rw [le_div_iff₀ hθ]; linarith
    rw [G, Real.smoothTransition.one_of_one_le h1]
    linarith [Real.smoothTransition.le_one ((u - 2 * Λ) / θ)]

theorem G_le_one (u : ℝ) : G θ Λ u ≤ 1 := by
  unfold G
  linarith [Real.smoothTransition.le_one (u / θ), Real.smoothTransition.nonneg ((u - 2 * Λ) / θ)]

/-- `G` vanishes outside `[0, 2Λ + θ]`. -/
theorem G_eq_zero (hθ : 0 < θ) (hΛ : 0 ≤ Λ) {u : ℝ} (hu : u ∉ Icc 0 (2 * Λ + θ)) : G θ Λ u = 0 := by
  rcases not_and_or.1 hu with h | h
  · replace h : u < 0 := lt_of_not_ge h
    have h0 : u / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h.le hθ.le
    rw [G_of_le hθ (by linarith), Real.smoothTransition.zero_of_nonpos h0]
  · replace h : 2 * Λ + θ < u := lt_of_not_ge h
    have h1 : 1 ≤ u / θ := by rw [le_div_iff₀ hθ]; linarith
    have h2 : 1 ≤ (u - 2 * Λ) / θ := by rw [le_div_iff₀ hθ]; linarith
    rw [G, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, sub_self]

/-- **The cut-off against the indicator.** For `u ≤ Λ`, `1[u > 0] − G(u)` and `1[u ≥ 0] − G(u)` lie in `[0, 1]`
and vanish unless `0 ≤ u < θ`. -/
theorem indicator_sub_G (hθ : 0 < θ) (hΛ : 0 ≤ Λ) {u : ℝ} (hu : u ≤ Λ) (P : Prop) [Decidable P]
    (hP : (0 < u → P) ∧ (P → 0 ≤ u)) :
    0 ≤ (if P then (1 : ℝ) else 0) - G θ Λ u ∧ (if P then (1 : ℝ) else 0) - G θ Λ u ≤ 1 ∧
      (u < 0 ∨ θ ≤ u → (if P then (1 : ℝ) else 0) - G θ Λ u = 0) := by
  have hG := G_of_le (Λ := Λ) hθ (by linarith : u ≤ 2 * Λ)
  rw [hG]
  have g0 := Real.smoothTransition.nonneg (u / θ)
  have g1 := Real.smoothTransition.le_one (u / θ)
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with h
    · linarith
    · have hu0 : u ≤ 0 := by by_contra h'; exact h (hP.1 (lt_of_not_ge h'))
      rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hu0 hθ.le)]; norm_num
  · split_ifs <;> linarith
  · rintro (h | h)
    · have hnP : ¬P := fun p => absurd (hP.2 p) (not_le.2 h)
      simp only [hnP, ↓reduceIte, Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg h.le hθ.le), sub_zero]
    · have hp : P := hP.1 (lt_of_lt_of_le hθ h)
      have h1 : 1 ≤ u / θ := by rw [le_div_iff₀ hθ]; linarith
      simp only [hp, ↓reduceIte, Real.smoothTransition.one_of_one_le h1, sub_self]

end SieveSmooth

namespace SieveSmooth

open Filter Topology

/-- `g` as a complex-valued function. -/
noncomputable def gc (v : ℝ) : ℂ := (Real.smoothTransition v : ℂ)

theorem contDiff_gc {n : ℕ∞} : ContDiff ℝ n gc :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

/-- For `K ≥ 1` the `K`-th derivative of `g` vanishes outside `[0, 1]`. -/
theorem iteratedDeriv_gc_eq_zero {K : ℕ} (hK : K ≠ 0) {v : ℝ} (hv : v ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv K gc v = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rcases not_and_or.1 hv with h | h
  · have hloc : gc =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge h)] with w hw
      simp [gc, Real.smoothTransition.zero_of_nonpos (le_of_lt hw)]
    rw [hloc.iteratedFDeriv ℝ K |>.eq_of_nhds]
    simp
  · have hloc : gc =ᶠ[𝓝 v] fun _ => (1 : ℂ) := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with w hw
      simp [gc, Real.smoothTransition.one_of_one_le (le_of_lt hw)]
    rw [hloc.iteratedFDeriv ℝ K |>.eq_of_nhds, iteratedFDeriv_const_of_ne hK]
    simp

theorem integrable_iteratedDeriv_gc {K : ℕ} (hK : K ≠ 0) : Integrable (iteratedDeriv K gc) := by
  refine (contDiff_gc (n := ⊤).continuous_iteratedDeriv K (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun v hv => ?_
  exact iteratedDeriv_gc_eq_zero hK hv

end SieveSmooth

namespace SieveSmooth

open Filter Topology

variable {θ Λ : ℝ}

/-- `G` as a complex-valued function. -/
noncomputable def GC (θ Λ : ℝ) (u : ℝ) : ℂ := gc (θ⁻¹ * u) - gc (θ⁻¹ * (u - 2 * Λ))

theorem GC_eq_G (θ Λ u : ℝ) : GC θ Λ u = (G θ Λ u : ℂ) := by
  simp [GC, G, gc, div_eq_inv_mul]

theorem contDiff_GC {n : ℕ∞} : ContDiff ℝ n (GC θ Λ) := by
  unfold GC
  exact (contDiff_gc.comp (contDiff_const.mul contDiff_id)).sub
    (contDiff_gc.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))

/-- **The derivatives of the cut-off**: `G^{(K)}(u) = θ^{−K}(g^{(K)}(u/θ) − g^{(K)}((u − 2Λ)/θ))`. -/
theorem iteratedDeriv_GC (K : ℕ) (u : ℝ) :
    iteratedDeriv K (GC θ Λ) u =
      θ⁻¹ ^ K • (iteratedDeriv K gc (θ⁻¹ * u) - iteratedDeriv K gc (θ⁻¹ * (u - 2 * Λ))) := by
  have hA : iteratedDeriv K (fun u => gc (θ⁻¹ * u)) = fun u => θ⁻¹ ^ K • iteratedDeriv K gc (θ⁻¹ * u) :=
    iteratedDeriv_comp_const_smul (contDiff_gc (n := K)) θ⁻¹
  have hB : iteratedDeriv K (fun u => (fun z => gc (θ⁻¹ * z)) (u - 2 * Λ)) =
      fun t => iteratedDeriv K (fun z => gc (θ⁻¹ * z)) (t - 2 * Λ) :=
    iteratedDeriv_comp_sub_const K (fun z => gc (θ⁻¹ * z)) (2 * Λ)
  have hc1 : ContDiffAt ℝ K (fun u => gc (θ⁻¹ * u)) u :=
    (contDiff_gc.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hc2 : ContDiffAt ℝ K (fun u => gc (θ⁻¹ * (u - 2 * Λ))) u :=
    (contDiff_gc.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).contDiffAt
  have hsub := iteratedDeriv_fun_sub hc1 hc2
  show iteratedDeriv K (fun u => gc (θ⁻¹ * u) - gc (θ⁻¹ * (u - 2 * Λ))) u = _
  rw [hsub, hA]
  have h2 : iteratedDeriv K (fun u => gc (θ⁻¹ * (u - 2 * Λ))) u =
      θ⁻¹ ^ K • iteratedDeriv K gc (θ⁻¹ * (u - 2 * Λ)) := by
    have := congrFun hB u
    simp only at this
    rw [this, hA]
  rw [h2, smul_sub]

/-- **The `L¹` norm of a derivative of the cut-off**: at most `2θ^{1−K}‖g^{(K)}‖₁` for `K ≥ 1`. -/
theorem integral_norm_iteratedDeriv_GC_le (hθ : 0 < θ) {K : ℕ} (hK : K ≠ 0) :
    ∫ u, ‖iteratedDeriv K (GC θ Λ) u‖ ≤ 2 * (θ⁻¹ ^ K * θ) * ∫ v, ‖iteratedDeriv K gc v‖ := by
  set A := iteratedDeriv K gc with hAdef
  have hAi : Integrable A := integrable_iteratedDeriv_gc hK
  have hθi : θ⁻¹ ≠ 0 := inv_ne_zero hθ.ne'
  have hi1 : Integrable fun u => ‖A (θ⁻¹ * u)‖ := (hAi.norm.comp_mul_left' hθi)
  have hi2 : Integrable fun u => ‖A (θ⁻¹ * (u - 2 * Λ))‖ := hi1.comp_sub_right (2 * Λ)
  have hpt : ∀ u, ‖iteratedDeriv K (GC θ Λ) u‖ ≤ θ⁻¹ ^ K * (‖A (θ⁻¹ * u)‖ + ‖A (θ⁻¹ * (u - 2 * Λ))‖) := by
    intro u
    rw [iteratedDeriv_GC, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 hθ) K)]
    gcongr
    exact norm_sub_le _ _
  have hint : Integrable fun u => θ⁻¹ ^ K * (‖A (θ⁻¹ * u)‖ + ‖A (θ⁻¹ * (u - 2 * Λ))‖) :=
    (hi1.add hi2).const_mul _
  have h1 : ∫ u, ‖A (θ⁻¹ * u)‖ = θ * ∫ v, ‖A v‖ := by
    rw [Measure.integral_comp_inv_mul_left (fun v => ‖A v‖) θ, abs_of_pos hθ, smul_eq_mul]
  have h2 : ∫ u, ‖A (θ⁻¹ * (u - 2 * Λ))‖ = θ * ∫ v, ‖A v‖ := by
    rw [integral_sub_right_eq_self (fun u => ‖A (θ⁻¹ * u)‖) (2 * Λ), h1]
  calc ∫ u, ‖iteratedDeriv K (GC θ Λ) u‖
      ≤ ∫ u, θ⁻¹ ^ K * (‖A (θ⁻¹ * u)‖ + ‖A (θ⁻¹ * (u - 2 * Λ))‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = θ⁻¹ ^ K * ((∫ u, ‖A (θ⁻¹ * u)‖) + ∫ u, ‖A (θ⁻¹ * (u - 2 * Λ))‖) := by
        rw [integral_const_mul, integral_add hi1 hi2]
    _ = 2 * (θ⁻¹ ^ K * θ) * ∫ v, ‖A v‖ := by rw [h1, h2]; ring

end SieveSmooth

namespace SieveSmooth

open Filter Topology

variable {θ Λ : ℝ}

theorem hasCompactSupport_GC (hθ : 0 < θ) (hΛ : 0 ≤ Λ) : HasCompactSupport (GC θ Λ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Λ + θ)) fun u hu => ?_
  rw [GC_eq_G, G_eq_zero hθ hΛ hu]
  simp

theorem integrable_iteratedDeriv_GC (hθ : 0 < θ) (hΛ : 0 ≤ Λ) (n : ℕ) :
    Integrable (iteratedDeriv n (GC θ Λ)) := by
  refine ((contDiff_GC (θ := θ) (Λ := Λ) (n := ⊤)).continuous_iteratedDeriv n
    (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
  refine ((hasCompactSupport_GC hθ hΛ).iteratedFDeriv (𝕜 := ℝ) n).mono' ?_
  intro x hx
  apply subset_tsupport
  intro h0
  apply hx
  simp [iteratedDeriv_eq_iteratedFDeriv, h0]

theorem integrable_GC (hθ : 0 < θ) (hΛ : 0 ≤ Λ) : Integrable (GC θ Λ) := by
  simpa using integrable_iteratedDeriv_GC hθ hΛ 0

/-- **Decay of the cut-off's Fourier transform**: `(2π|ξ|)^K‖𝓕G(ξ)‖ ≤ 2θ^{1−K}‖g^{(K)}‖₁` for `K ≥ 1`. -/
theorem pow_mul_norm_fourier_GC_le (hθ : 0 < θ) (hΛ : 0 ≤ Λ) {K : ℕ} (hK : K ≠ 0) (ξ : ℝ) :
    (2 * π * |ξ|) ^ K * ‖𝓕 (GC θ Λ) ξ‖ ≤ 2 * (θ⁻¹ ^ K * θ) * ∫ v, ‖iteratedDeriv K gc v‖ :=
  (pow_mul_norm_fourier_le contDiff_GC
    (fun n _ => integrable_iteratedDeriv_GC hθ hΛ n) ξ).trans (integral_norm_iteratedDeriv_GC_le hθ hK)

theorem norm_fourier_GC_le (ξ : ℝ) : ‖𝓕 (GC θ Λ) ξ‖ ≤ ∫ u, ‖GC θ Λ u‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem integrable_fourier_GC (hθ : 0 < θ) (hΛ : 0 ≤ Λ) : Integrable (𝓕 (GC θ Λ)) := by
  set N₀ := ∫ u, ‖GC θ Λ u‖ with hN₀
  set N₂ := 2 * (θ⁻¹ ^ 2 * θ) * ∫ v, ‖iteratedDeriv 2 gc v‖ with hN₂
  have hc : Continuous (𝓕 (GC θ Λ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (integrable_GC hθ hΛ)
  have hpi : 0 < 4 * π ^ 2 := by positivity
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (N₀ + N₂ / (4 * π ^ 2)))
    hc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have h0 := norm_fourier_GC_le (θ := θ) (Λ := Λ) ξ
  have h2 := pow_mul_norm_fourier_GC_le hθ hΛ (K := 2) (by norm_num) ξ
  have hsq : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hsq] at h2
  have hF := norm_nonneg (𝓕 (GC θ Λ) ξ)
  have h2' : ξ ^ 2 * ‖𝓕 (GC θ Λ) ξ‖ ≤ N₂ / (4 * π ^ 2) := by
    rw [le_div_iff₀ hpi]; nlinarith
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

/-- **Separation by Fourier inversion**: `G(a − b) = ∫ 𝓕G(ξ) e^{2πiξa} e^{−2πiξb} dξ`. -/
theorem GC_sub_eq_integral (hθ : 0 < θ) (hΛ : 0 ≤ Λ) (a b : ℝ) :
    GC θ Λ (a - b) = ∫ ξ : ℝ, Complex.exp (2 * π * I * ξ * a) * Complex.exp (-(2 * π * I * ξ * b)) *
      𝓕 (GC θ Λ) ξ := by
  have hinv := Continuous.fourierInv_fourier_eq (contDiff_GC (θ := θ) (Λ := Λ) (n := 0)).continuous
    (integrable_GC hθ hΛ) (integrable_fourier_GC hθ hΛ)
  rw [← congrFun hinv (a - b), Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

end SieveSmooth
