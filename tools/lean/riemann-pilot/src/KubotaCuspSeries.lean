import KubotaCuspTheta

/-! # θ's Fourier series at the cusps `γ_±` (round 465)

S5f-15 of round 360's plan, part 6. Round 464's next step planned θ's Fourier series at the cusps `γ_±` from
round 464's coefficients. This round proves it, for `tt′ = 1`, `m₀ = ±1` in the class of the cusp `γ_t` (round
461's `CuspClass`) and `θ` round 436's Fourier series `thS`, and with it the clauses of round 361's
`KubotaTheta` at `γ_±`:

* **Theta-type series supported on `m₀ + δ₃ℤ[ω]`** (**`integral_ebr_thTerm_shift`**,
  **`integral_ebr_thSer_shift`** and **`thSer_add_period_shift`**): for `d` with `|d(m)| ≤ C|m|⁵`, `d(0) = 0`
  and `d(m) ≠ 0` only for `m ∈ m₀ + δ₃ℤ[ω]`, and `v > 0`,
  `∫_{3P} ĕ(−(m₀ + δ₃x)z/9)·thSer 0 d z v dz = (9√3/2)·d(m₀ + δ₃x)·v·K_{1/3}(4π|m₀ + δ₃x|v/9)` (round 435's
  `integral_fundP3_ebr_mul`, as in round 436's `integral_ebr_thSer`), and
  `thSer 0 d (z + 3u) v = ĕ(m₀·3u/9)·thSer 0 d z v` (round 428's `ebr_period`).
* **The coefficients** (`tauCusp`, a definition; **`exists_norm_tauCusp_le`**, with `lam_not_dvd_of_class`,
  `ne_zero_of_class`, `cuspClass_add`, `tauCusp_of_dvd`, `dvd_of_tauCusp_ne_zero` and `tauCusp_zero`):
  `τ_t(m) = ρ_t(m)/(9√3/2)` on `m₀ + δ₃ℤ[ω]`, which lies in the class and meets `λℤ[ω]` nowhere, and
  `τ_t(m) = 0` elsewhere, with `|τ_t(m)| ≤ C|m|⁵` (round 434's `norm_rhoM_le`, round 463's `norm_σO_cuspIdx`).
* **θ's Fourier series at `γ_t`** (**`thS_lowT_eq`**, with `integrable_fundP3_of_continuous`):
  `θ(γ_t(z, v)) = thSer 0 τ_t z v` for every `z` and every `v > 0`. The difference times `ĕ(−m₀z/9)` is
  periodic modulo `3ℤ[ω]` (round 460's `thS_lowT_add`), its coefficient at `δ₃x` is the difference of the two
  coefficients at `m₀ + δ₃x`, which is `0` (round 464's `coef_lowT`), so it vanishes almost everywhere (round
  435's `ae_eq_zero_of_coef` and `ae_eq_zero_of_periodic`), and everywhere since it is continuous.
* **The support and size condition** (**`thetaSupp_tauCusp`**): `ThetaSupp K τ_t` for some `K` (round 458's
  `exists_unit_lam_pow_primary` and `rhoM_supp_norm`, round 459's `rhoM_lam_bound`).
* **The cusps `γ_±`** (**`exists_cusp_series`** and **`cusp_clauses`**, with `ThetaSupp.mono` and
  `mul_sq_eq_one_of_cusp`): at `γ_+ = (1, 0; ω, 1)` and `γ_− = (1, 0; ω², 1)`, in round 361's notation `atG`,
  θ is `thSer 0 tP` and `thSer 0 tM` with `ThetaSupp K tP` and `ThetaSupp K tM` for one `K` (round 460's
  `exists_cuspClass`, and `t′ = t²`).
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Theta-type series supported on a class modulo `δ₃` -/

open Classical in
/-- **One term's coefficient**, for `d` supported on `m₀ + δ₃ℤ[ω]`: `∫_{3P} ĕ(−σ(m₀ + δ₃x)z/9)·T_m(z, v) dz`
is `(9√3/2)·d(m)·v·K_{1/3}(4π|m|v/9)` if `m = m₀ + δ₃x`, and `0` otherwise (round 435's
`integral_fundP3_ebr_mul`). -/
theorem integral_ebr_thTerm_shift {m₀ : 𝓞 K} {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m - m₀)
    (x m : 𝓞 K) (v : ℝ) :
    ∫ z in fundP3, ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thTerm d m (z, v) =
      if m = m₀ + δ3 * x then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
        (d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)) else 0 := by
  by_cases hd : d m = 0
  · simp [thTerm, hd]
  obtain ⟨x', hx'⟩ := hsupp _ hd
  obtain rfl : m = m₀ + δ3 * x' := by linear_combination hx'
  have e : ∀ z, ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thTerm d (m₀ + δ3 * x') (z, v) =
      (d (m₀ + δ3 * x') * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (m₀ + δ3 * x')‖ * v / 9)) *
        (ebr (-(σO (δ3 * x) / 9 * z)) * ebr (σO (δ3 * x') * z / 9)) := by
    intro z
    have h : ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * ebr (σO (m₀ + δ3 * x') * z / 9) =
        ebr (-(σO (δ3 * x) / 9 * z)) * ebr (σO (δ3 * x') * z / 9) := by
      rw [← ebr_add, ← ebr_add, map_add, map_add]
      congr 1
      ring
    simp only [thTerm]
    linear_combination (d (m₀ + δ3 * x') * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO (m₀ + δ3 * x')‖ * v / 9)) * h
  simp_rw [e]
  rw [integral_const_mul, integral_fundP3_ebr_mul]
  have hiff : m₀ + δ3 * x' = m₀ + δ3 * x ↔ x = x' := by
    constructor
    · intro h
      exact (mul_left_cancel₀ δ3_ne_zero (add_left_cancel h)).symm
    · intro h
      rw [h]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (hiff.2 h1) h2
  · exact absurd (hiff.1 h2) h1
  · ring

/-- **The Fourier coefficients of a theta-type series supported on `m₀ + δ₃ℤ[ω]`**: for `d` with
`|d(m)| ≤ C|m|⁵`, `d(0) = 0` and `d(m) ≠ 0` only for `m ∈ m₀ + δ₃ℤ[ω]`, and `v > 0`,
`∫_{3P} ĕ(−σ(m₀ + δ₃x)z/9)·thSer 0 d z v dz = (9√3/2)·d(m₀ + δ₃x)·v·K_{1/3}(4π|m₀ + δ₃x|v/9)` (as round 436's
`integral_ebr_thSer`). -/
theorem integral_ebr_thSer_shift {m₀ : 𝓞 K} {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5) (hd0 : d 0 = 0) (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m - m₀) (x : 𝓞 K)
    {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thSer 0 d z v =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
        (d (m₀ + δ3 * x) * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (m₀ + δ3 * x)‖ * v / 9)) := by
  classical
  obtain ⟨e, he⟩ : ∃ e : ℂ → ℂ, e = fun z => ebr (-(σO (m₀ + δ3 * x) / 9 * z)) := ⟨_, rfl⟩
  have hec : Continuous e := by rw [he]; unfold ebr; fun_prop
  have hne : ∀ z, ‖e z‖ = 1 := fun z => by rw [he]; exact norm_ebr _
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K → ℝ,
      a = fun m => ‖d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ := exists_norm_thTerm_le hC hd hd0 hv v
  have hsa : Summable a := by
    refine Summable.of_nonneg_of_le (fun m => by rw [ha]; exact norm_nonneg _) (fun m => ?_)
      (summable_rpow_neg_three B)
    simp only [ha]
    rw [← norm_thTerm_eq d m 0 v]
    exact hB m (0, v) le_rfl le_rfl
  obtain ⟨F, hF⟩ : ∃ F : 𝓞 K → ℂ → ℂ, F = fun m z => e z * thTerm d m (z, v) := ⟨_, rfl⟩
  have hFn : ∀ m z, ‖F m z‖ = a m := fun m z => by
    rw [hF, ha, norm_mul, hne, one_mul, norm_thTerm_eq]
  have hFc : ∀ m, Continuous (F m) := fun m => by
    rw [hF]; exact hec.mul (continuous_thTerm_fst d m v)
  have hfin : IsFiniteMeasure (volume.restrict fundP3) :=
    isFiniteMeasure_restrict.2 (by rw [volume_fundP3]; exact ENNReal.ofReal_ne_top)
  have hFi : ∀ m, Integrable (F m) (volume.restrict fundP3) := fun m =>
    (integrable_const (a m)).mono' (hFc m).aestronglyMeasurable (ae_of_all _ fun z => (hFn m z).le)
  have hsum : Summable fun m => ∫ z in fundP3, ‖F m z‖ := by
    simp_rw [hFn]
    simp only [integral_const, smul_eq_mul]
    exact hsa.mul_left _
  have hsplit : ∀ z, e z * thSer 0 d z v = ∑' m, F m z := by
    intro z
    rw [thSer_eq, zero_mul, zero_add, hF]
    exact tsum_mul_left.symm
  have hterms : ∀ m, ∫ z in fundP3, F m z = if m = m₀ + δ3 * x then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
      (d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)) else 0 := fun m => by
    rw [hF, he]
    exact integral_ebr_thTerm_shift hsupp x m v
  have hgoal : ∫ z in fundP3, ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thSer 0 d z v =
      ∫ z in fundP3, ∑' m, F m z := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [← hsplit z, he]
  rw [hgoal, ← integral_tsum_of_summable_integral_norm hFi hsum, tsum_congr hterms,
    tsum_eq_single (m₀ + δ3 * x) fun m hm => by simp [hm]]
  simp

/-- **The translation law of a theta-type series supported on `m₀ + δ₃ℤ[ω]`**:
`thSer 0 d (z + 3u) v = ĕ(m₀·3u/9)·thSer 0 d z v` (round 428's `ebr_period`). -/
theorem thSer_add_period_shift {m₀ : 𝓞 K} {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m - m₀) (z : ℂ)
    (u : 𝓞 K) (v : ℝ) :
    thSer 0 d (z + σO (3 * u)) v = ebr (σO m₀ * σO (3 * u) / 9) * thSer 0 d z v := by
  simp only [thSer_eq, zero_mul, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  by_cases h : d m = 0
  · simp [thTerm, h]
  obtain ⟨x, hx⟩ := hsupp m h
  obtain rfl : m = m₀ + δ3 * x := by linear_combination hx
  simp only [thTerm]
  have e : ebr (σO (m₀ + δ3 * x) * (z + σO (3 * u)) / 9) =
      ebr (σO m₀ * σO (3 * u) / 9) * ebr (σO (m₀ + δ3 * x) * z / 9) := by
    rw [show σO (m₀ + δ3 * x) * (z + σO (3 * u)) / 9 =
        σO (m₀ + δ3 * x) * z / 9 + (σO m₀ * σO (3 * u) / 9 + σO (δ3 * x) * σO (3 * u) / 9) by
      rw [map_add]; ring, ebr_add, ebr_add, ebr_period, mul_one]
    ring
  rw [e]
  ring

/-! ### The coefficients at `γ_t` -/

/-- `λ ∤ m` for `m ∈ m₀ + δ₃ℤ[ω]` with `m₀ = ±1`: `λ ∣ δ₃` (round 364's `lam_dvd_δ3`), and `λ ∤ ±1` since
`N(λ) = 3` (round 458's `absNorm_span_lam`). -/
theorem lam_not_dvd_of_class {m₀ m : 𝓞 K} (hm₀ : m₀ = 1 ∨ m₀ = -1) (h : δ3 ∣ m - m₀) :
    ¬ (ω - 1 : 𝓞 K) ∣ m := by
  intro hl
  have h1 : (ω - 1 : 𝓞 K) ∣ m₀ := by
    have := dvd_sub hl (lam_dvd_δ3.trans h)
    rwa [sub_sub_cancel] at this
  have hu : IsUnit (ω - 1 : 𝓞 K) := by
    rcases hm₀ with rfl | rfl
    · exact isUnit_of_dvd_one h1
    · exact isUnit_of_dvd_one ((dvd_neg).1 h1)
  have := absNorm_span_lam
  rw [Ideal.span_singleton_eq_top.2 hu, Ideal.absNorm_top] at this
  norm_num at this

/-- `m ≠ 0` for `m ∈ m₀ + δ₃ℤ[ω]` with `m₀ = ±1`. -/
theorem ne_zero_of_class {m₀ m : 𝓞 K} (hm₀ : m₀ = 1 ∨ m₀ = -1) (h : δ3 ∣ m - m₀) : m ≠ 0 := by
  rintro rfl
  exact lam_not_dvd_of_class hm₀ h (dvd_zero _)

/-- The class of the cusp `γ_t` contains `m₀ + δ₃ℤ[ω]` (round 428's `ebr_period`). -/
theorem cuspClass_add {t m₀ : 𝓞 K} (hm₀ : CuspClass t m₀) (x : 𝓞 K) : CuspClass t (m₀ + δ3 * x) := by
  intro y
  rw [map_add, add_mul, add_div, ebr_add, ebr_period, mul_one]
  exact hm₀ y

open Classical in
/-- **θ's coefficients at `γ_t`** in the index of round 361's `thSer`: `τ_t(m) = ρ_t(m)/(9√3/2)` for
`m ∈ m₀ + δ₃ℤ[ω]`, and `0` at the other indices. -/
def tauCusp (t t' m₀ : 𝓞 K) (r Y : ℝ) (hY : 0 < Y) (m : 𝓞 K) : ℂ :=
  if δ3 ∣ m - m₀ then rhoCusp t t' m r Y hY / ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) else 0

/-- `τ_t(m) = ρ_t(m)/(9√3/2)` for `m ∈ m₀ + δ₃ℤ[ω]`. -/
theorem tauCusp_of_dvd {t t' m₀ : 𝓞 K} {r Y : ℝ} {hY : 0 < Y} {m : 𝓞 K} (h : δ3 ∣ m - m₀) :
    tauCusp t t' m₀ r Y hY m = rhoCusp t t' m r Y hY / ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) := by
  classical
  rw [tauCusp, ite_eq_left h]

/-- `τ_t` is supported on `m₀ + δ₃ℤ[ω]`. -/
theorem dvd_of_tauCusp_ne_zero {t t' m₀ : 𝓞 K} {r Y : ℝ} {hY : 0 < Y} {m : 𝓞 K}
    (h : tauCusp t t' m₀ r Y hY m ≠ 0) : δ3 ∣ m - m₀ := by
  classical
  by_contra hd
  exact h (by rw [tauCusp, ite_eq_right hd])

/-- `τ_t(0) = 0` for `m₀ = ±1`. -/
theorem tauCusp_zero {t t' m₀ : 𝓞 K} (hm₀ : m₀ = 1 ∨ m₀ = -1) (r Y : ℝ) (hY : 0 < Y) :
    tauCusp t t' m₀ r Y hY 0 = 0 := by
  classical
  rw [tauCusp, ite_eq_right fun h => ne_zero_of_class hm₀ h rfl]

/-- **`|τ_t(m)| ≤ C|m|⁵`**, from round 434's `norm_rhoM_le` and round 463's `norm_σO_cuspIdx`. -/
theorem exists_norm_tauCusp_le {t t' m₀ : 𝓞 K} (htt : t * t' = 1) (hm₀ : m₀ = 1 ∨ m₀ = -1) {r : ℝ}
    (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖tauCusp t t' m₀ r Y hY m‖ ≤ C * ‖σO m‖ ^ 5 := by
  obtain ⟨C, hC⟩ := norm_rhoM_le hr hY
  have hc9 : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
  have hs : (Real.sqrt 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp)
  refine ⟨max C 0 * (3 * Real.sqrt 3) ^ 5 / (9 * (Real.sqrt 3 / 2)), by positivity, fun m => ?_⟩
  by_cases h : δ3 ∣ m - m₀
  · have hm0 : m ≠ 0 := ne_zero_of_class hm₀ h
    have hn : ‖σO (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))‖ = 3 * Real.sqrt 3 * ‖σO m‖ := by
      have := norm_σO_cuspIdx htt m
      rw [norm_div, norm_div, show ‖(9 : ℂ)‖ = 9 by norm_num] at this
      linarith [this]
    have h1 := hC _ (cuspIdx_ne_zero htt hm0)
    rw [hn] at h1
    rw [tauCusp_of_dvd h, norm_div, Complex.norm_real, Real.norm_of_nonneg hc9.le, rhoCusp, norm_mul,
      norm_mul, norm_ebr, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_le_iff₀ hc9]
    have h0 := norm_nonneg (rhoM (ω ^ 2 * t * (ω - 1) ^ 2 * m) r Y hY)
    calc (Real.sqrt 3)⁻¹ * ‖rhoM (ω ^ 2 * t * (ω - 1) ^ 2 * m) r Y hY‖
        ≤ 1 * (max C 0 * (3 * Real.sqrt 3 * ‖σO m‖) ^ 5) :=
          mul_le_mul hs (h1.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))) h0
            zero_le_one
      _ = max C 0 * (3 * Real.sqrt 3) ^ 5 / (9 * (Real.sqrt 3 / 2)) * ‖σO m‖ ^ 5 *
          (9 * (Real.sqrt 3 / 2)) := by
          field_simp
  · classical
    rw [tauCusp, ite_eq_right h, norm_zero]
    positivity

/-! ### θ's Fourier series at `γ_t` -/

/-- A continuous function is integrable on `3P` (round 430's `norm_le_six_of_mem_fundP3`). -/
theorem integrable_fundP3_of_continuous {f : ℂ → ℂ} (hf : Continuous f) :
    Integrable f (volume.restrict fundP3) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 6)).mono_set
    fun _ hz => mem_closedBall_zero_iff.2 (norm_le_six_of_mem_fundP3 hz)

/-- **θ's Fourier series at `γ_t`**: for `tt′ = 1`, `m₀ = ±1` in the class of the cusp `γ_t` (round 461's
`CuspClass`), `r > 0`, `Y > 0`, every `z` and every `v > 0`, `θ(γ_t(z, v)) = thSer 0 τ_t z v` with θ's Fourier
series. The difference times `ĕ(−m₀z/9)` is periodic modulo `3ℤ[ω]` (round 460's `thS_lowT_add`,
`thSer_add_period_shift`), its coefficients vanish (round 464's `coef_lowT`, `integral_ebr_thSer_shift`), so
it vanishes almost everywhere (round 435's `ae_eq_zero_of_coef` and `ae_eq_zero_of_periodic`), and everywhere
since it is continuous. -/
theorem thS_lowT_eq {t t' m₀ : 𝓞 K} (htt : t * t' = 1) (hm₀ : m₀ = 1 ∨ m₀ = -1) (hcl : CuspClass t m₀)
    {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    thS r Y hY (slAct (lowT t) (z, v)) = thSer 0 (tauCusp t t' m₀ r Y hY) z v := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tauCusp_le htt hm₀ hr hY
  have hd0 := tauCusp_zero (t := t) (t' := t') hm₀ r Y hY
  have hsupp : ∀ m, tauCusp t t' m₀ r Y hY m ≠ 0 → δ3 ∣ m - m₀ := fun _ h => dvd_of_tauCusp_ne_zero h
  set τ := tauCusp t t' m₀ r Y hY with hτ
  have hA : Continuous fun z : ℂ => thS r Y hY (slAct (lowT t) (z, v)) :=
    ((continuousOn_thS hr hY).comp (continuousOn_slAct (lowT t)) fun p hp => slAct_mem _ hp).comp_continuous
      (continuous_id.prodMk continuous_const) fun _ => hv
  have hB : Continuous fun z : ℂ => thSer 0 τ z v :=
    (continuousOn_thSer 0 hC0 hC hd0).comp_continuous (continuous_id.prodMk continuous_const) fun _ => hv
  have hE : ∀ k : ℂ, Continuous fun z : ℂ => ebr (-(k / 9 * z)) := fun k => by unfold ebr; fun_prop
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun z =>
      (thS r Y hY (slAct (lowT t) (z, v)) - thSer 0 τ z v) * ebr (-(σO m₀ / 9 * z)) := ⟨_, rfl⟩
  have hgc : Continuous g := by rw [hgdef]; exact (hA.sub hB).mul (hE _)
  -- `g` is square-integrable on `3P`
  have hg2 : ∫⁻ z in fundP3, ‖g z‖ₑ ^ 2 < ⊤ := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 6).exists_bound_of_continuousOn hgc.continuousOn
    calc ∫⁻ z in fundP3, ‖g z‖ₑ ^ 2
        ≤ ∫⁻ _ in fundP3, ENNReal.ofReal M ^ 2 :=
          setLIntegral_mono measurable_const fun z hz => by
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal
              (hM z (mem_closedBall_zero_iff.2 (norm_le_six_of_mem_fundP3 hz)))
      _ < ⊤ := by
          rw [setLIntegral_const, volume_fundP3]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  -- `g` is periodic
  have hper : ∀ z u, g (z + σO (3 * u)) = g z := by
    intro z u
    rw [hgdef]
    dsimp only
    rw [thS_lowT_add hr hY t u z hv, thSer_add_period_shift hsupp z u v, ← hcl u]
    have e : ebr (-(σO m₀ / 9 * (z + σO (3 * u)))) =
        ebr (-(σO m₀ / 9 * z)) * ebr (-(σO m₀ * σO (3 * u) / 9)) := by
      rw [← ebr_add]
      congr 1
      ring
    have e2 : ebr (σO m₀ * σO (3 * u) / 9) * ebr (-(σO m₀ * σO (3 * u) / 9)) = 1 := by
      rw [← ebr_add, add_neg_cancel, ebr_zero]
    rw [e]
    linear_combination (thS r Y hY (slAct (lowT t) (z, v)) - thSer 0 τ z v) * ebr (-(σO m₀ / 9 * z)) * e2
  -- the coefficients of `g` vanish
  have hcoef : ∀ x : 𝓞 K, ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * g z = 0 := by
    intro x
    have hdx : δ3 ∣ m₀ + δ3 * x - m₀ := by simp
    have hm0 : m₀ + δ3 * x ≠ 0 := ne_zero_of_class hm₀ hdx
    have e : ∀ z, ebr (-(σO (δ3 * x) / 9 * z)) * g z =
        ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thS r Y hY (slAct (lowT t) (z, v)) -
          ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thSer 0 τ z v := by
      intro z
      have h : ebr (-(σO (δ3 * x) / 9 * z)) * ebr (-(σO m₀ / 9 * z)) =
          ebr (-(σO (m₀ + δ3 * x) / 9 * z)) := by
        rw [← ebr_add, map_add]
        congr 1
        ring
      rw [hgdef]
      linear_combination (thS r Y hY (slAct (lowT t) (z, v)) - thSer 0 τ z v) * h
    have hi1 : Integrable (fun z => ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thS r Y hY (slAct (lowT t) (z, v)))
        (volume.restrict fundP3) := integrable_fundP3_of_continuous ((hE _).mul hA)
    have hi2 : Integrable (fun z => ebr (-(σO (m₀ + δ3 * x) / 9 * z)) * thSer 0 τ z v)
        (volume.restrict fundP3) := integrable_fundP3_of_continuous ((hE _).mul hB)
    simp_rw [e]
    rw [integral_sub hi1 hi2, coef_lowT htt (cuspClass_add hcl x) hm0 hr hY hv,
      integral_ebr_thSer_shift hC0 hC hd0 hsupp x hv, hτ, tauCusp_of_dvd hdx]
    have harg : 4 * Real.pi * ‖σO (m₀ + δ3 * x)‖ * v / 9 = 4 * Real.pi * ‖σO (m₀ + δ3 * x) / 9‖ * v := by
      rw [norm_div, show ‖(9 : ℂ)‖ = 9 by norm_num]
      ring
    have hc9 : ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
      exact_mod_cast this.ne'
    rw [harg]
    field_simp
    ring
  have hae := ae_eq_zero_of_periodic hgc.measurable hper (ae_eq_zero_of_coef hgc.measurable hg2 hcoef)
  have hg0 : g = fun _ => 0 := (Continuous.ae_eq_iff_eq volume hgc continuous_const).1 hae
  have hz := congrFun hg0 z
  rw [hgdef] at hz
  have hne : ebr (-(σO m₀ / 9 * z)) ≠ 0 := by
    intro h0
    have := norm_ebr (-(σO m₀ / 9 * z))
    rw [h0, norm_zero] at this
    norm_num at this
  exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hne)

/-! ### The support and size condition at `γ_t` -/

/-- **Round 361's support and size condition for `τ_t`**: for `tt′ = 1` and `m₀ = ±1`, `ThetaSupp K τ_t` for
some `K`. For `τ_t(m) ≠ 0`, `m ∈ m₀ + δ₃ℤ[ω]` is prime to `λ`, so `m = u·y` with `u` a unit and `y` primary
(round 458's `exists_unit_lam_pow_primary`), `m′ = u′λ²·y` with `u′ = ω²tu`, and round 458's `rhoM_supp_norm`
gives `y = n·b³` with `(n)` squarefree and `|ρ(m′)| = |b|·|ρ(u′λ²)|`; round 459's `rhoM_lam_bound` bounds
`|ρ(u′λ²)|`, and `m` is round 341's `dualPt` at `(u, 0, (n), (b))`. -/
theorem thetaSupp_tauCusp {t t' m₀ : 𝓞 K} (htt : t * t' = 1) (hm₀ : m₀ = 1 ∨ m₀ = -1) {r : ℝ} (hr : 0 < r)
    {Y : ℝ} (hY : 0 < Y) : ∃ Kc : ℝ, ThetaSupp Kc (tauCusp t t' m₀ r Y hY) := by
  obtain ⟨A, hA0, hA⟩ := rhoM_lam_bound hr hY
  have hc : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
  have hs : (Real.sqrt 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp)
  have hl0 : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by
    have := absNorm_span_lam
    rw [h, Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
    norm_num at this
  refine ⟨A * (3 : ℝ) ^ ((2 : ℝ) / 6) / (9 * (Real.sqrt 3 / 2)), by positivity, fun m hm => ?_⟩
  have hd := dvd_of_tauCusp_ne_zero hm
  have hl := lam_not_dvd_of_class hm₀ hd
  obtain ⟨u, j, y, hy, rfl⟩ := exists_unit_lam_pow_primary (ne_zero_of_class hm₀ hd)
  obtain rfl : j = 0 := by
    by_contra hj
    exact hl (((dvd_pow_self _ hj).mul_left _).mul_right _)
  set u' : (𝓞 K)ˣ := ωu ^ 2 * Units.mkOfMulEqOne t t' htt * u with hu'
  have hx : ω ^ 2 * t * (ω - 1) ^ 2 * ((u : 𝓞 K) * (ω - 1) ^ 0 * y) = (u' : 𝓞 K) * (ω - 1) ^ 2 * y := by
    simp only [hu', Units.val_mul, Units.val_pow_eq_pow_val, coe_ωu, Units.val_mkOfMulEqOne]
    ring
  have hρ : rhoM ((u' : 𝓞 K) * (ω - 1) ^ 2 * y) r Y hY ≠ 0 := by
    rw [← hx]
    intro h0
    apply hm
    rw [tauCusp_of_dvd hd, rhoCusp, h0, mul_zero, zero_div]
  have hz0 : (u' : 𝓞 K) * (ω - 1) ^ 2 ≠ 0 := mul_ne_zero u'.ne_zero (pow_ne_zero 2 hl0)
  obtain ⟨n, b, hn, hb, hsq, rfl, hnorm⟩ :=
    rhoM_supp_norm hr hY hz0 (fun p hp hpp => not_dvd_unit_mul_lam_pow hp hpp u' 2) hy hρ
  refine ⟨(u, 0, span {n}, span {b}), ?_, hsq, coprime_three_of_primary hn, coprime_three_of_primary hb, ?_⟩
  · simp only [dualPt, pgen_eq hn, pgen_eq hb]
    ring
  · have h2 : ‖rhoM ((u' : 𝓞 K) * (ω - 1) ^ 2) r Y hY‖ ≤ A * (3 : ℝ) ^ ((2 : ℝ) / 6) := by
      have := hA u' 2
      push_cast at this
      exact this
    rw [tauCusp_of_dvd hd, rhoCusp, hx, norm_div, norm_mul, norm_mul, norm_ebr, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hc.le, hnorm,
      norm_σO_eq_sqrt, div_le_iff₀ hc]
    have hN := Real.sqrt_nonneg (absNorm (span {b}) : ℝ)
    calc (Real.sqrt 3)⁻¹ * (Real.sqrt (absNorm (span {b})) * ‖rhoM ((u' : 𝓞 K) * (ω - 1) ^ 2) r Y hY‖)
        ≤ 1 * (Real.sqrt (absNorm (span {b})) * (A * (3 : ℝ) ^ ((2 : ℝ) / 6))) :=
          mul_le_mul hs (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
      _ = A * (3 : ℝ) ^ ((2 : ℝ) / 6) / (9 * (Real.sqrt 3 / 2)) * (3 : ℝ) ^ (((0 : ℕ) : ℝ) / 6) *
          Real.sqrt (absNorm (span {b})) * (9 * (Real.sqrt 3 / 2)) := by
          rw [Nat.cast_zero, zero_div, Real.rpow_zero]
          field_simp

/-! ### The cusps `γ_±` -/

/-- Round 361's `ThetaSupp` is monotone in its constant. -/
theorem ThetaSupp.mono {Kc Kc' : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (hK : Kc ≤ Kc') : ThetaSupp Kc' d := by
  refine ⟨h.1.trans hK, fun m hm => ?_⟩
  obtain ⟨q, h1, h2, h3, h4, h5⟩ := h.2 m hm
  exact ⟨q, h1, h2, h3, h4, h5.trans (by gcongr)⟩

/-- `t·t² = 1` for `t = ω` and `t = ω²`. -/
theorem mul_sq_eq_one_of_cusp {t : 𝓞 K} (ht : t = ω ∨ t = ω ^ 2) : t * t ^ 2 = 1 := by
  rcases ht with rfl | rfl
  · linear_combination ω_cube
  · linear_combination (ω ^ 3 + 1) * ω_cube

/-- **θ's Fourier series at the cusp `γ_t`** for `t = ω` and `t = ω²`, in round 361's notation `atG`: a
theta-type series `thSer 0 d` with `ThetaSupp K d` for some `K` (`thS_lowT_eq` at round 460's
`exists_cuspClass`, `thetaSupp_tauCusp`). -/
theorem exists_cusp_series {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {t : 𝓞 K} (ht : t = ω ∨ t = ω ^ 2) :
    ∃ (Kc : ℝ) (d : 𝓞 K → ℂ), ThetaSupp Kc d ∧ ∀ z v, 0 < v →
      atG (fun z v => thS r Y hY (z, v)) (((lowT t : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) z v =
        thSer 0 d z v := by
  obtain ⟨m₀, hm₀, hcl⟩ := exists_cuspClass t ht
  obtain ⟨Kc, hK⟩ := thetaSupp_tauCusp (m₀ := m₀) (mul_sq_eq_one_of_cusp ht) hm₀ hr hY
  exact ⟨Kc, _, hK, fun z v hv => thS_lowT_eq (mul_sq_eq_one_of_cusp ht) hm₀ hcl hr hY z hv⟩

/-- **The clauses of round 361's `KubotaTheta` at `γ_±`**, for θ's Fourier series: at `γ_+ = (1, 0; ω, 1)`
and `γ_− = (1, 0; ω², 1)`, θ is a theta-type series with constant term `0` and coefficients satisfying the
support and size condition, with one constant for both. -/
theorem cusp_clauses {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ (Kc : ℝ) (tP tM : 𝓞 K → ℂ), ThetaSupp Kc tP ∧ ThetaSupp Kc tM ∧
      (∀ z v, 0 < v → atG (fun z v => thS r Y hY (z, v)) (gamPlus.map σO) z v = thSer 0 tP z v) ∧
      (∀ z v, 0 < v → atG (fun z v => thS r Y hY (z, v)) (gamMinus.map σO) z v = thSer 0 tM z v) := by
  obtain ⟨K₁, tP, h₁, hP⟩ := exists_cusp_series hr hY (Or.inl rfl)
  obtain ⟨K₂, tM, h₂, hM⟩ := exists_cusp_series hr hY (Or.inr rfl)
  exact ⟨max K₁ K₂, tP, tM, h₁.mono (le_max_left _ _), h₂.mono (le_max_right _ _), hP, hM⟩

end Eis

end

#print axioms Eis.integral_ebr_thTerm_shift
#print axioms Eis.integral_ebr_thSer_shift
#print axioms Eis.thSer_add_period_shift
#print axioms Eis.lam_not_dvd_of_class
#print axioms Eis.ne_zero_of_class
#print axioms Eis.cuspClass_add
#print axioms Eis.tauCusp_of_dvd
#print axioms Eis.dvd_of_tauCusp_ne_zero
#print axioms Eis.tauCusp_zero
#print axioms Eis.exists_norm_tauCusp_le
#print axioms Eis.integrable_fundP3_of_continuous
#print axioms Eis.thS_lowT_eq
#print axioms Eis.thetaSupp_tauCusp
#print axioms Eis.ThetaSupp.mono
#print axioms Eis.mul_sq_eq_one_of_cusp
#print axioms Eis.exists_cusp_series
#print axioms Eis.cusp_clauses
