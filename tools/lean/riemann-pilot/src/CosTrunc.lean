import Mathlib
import GapBound

/-! # Density of the cosine truncations

Round 60's Galerkin transfer (`lam2Ge_of_trunc`, `simple_of_trunc_gap`) assumed `TruncDense`: every
probe is a limit, in `L²` plus archimedean energy, of vectors from the truncation spaces. This file
proves it for the basis of the paper's Gram code (`tools/research/weil_prime_gram.py`):

  `cosTrunc a K = span{1_{[−a,a]}·cos(kπt/a) : k < K}`   (`cosTrunc_dense`).

The proof has four steps.

* **Smooth approximant** (round 55, `av3_dense`, `av3_C2`). A probe is approximated by `h = Av_δ³ψ`,
  which is `C²` with `h, h', h''` vanishing outside `[−a, a]`.
* **Cosine series** (`cos_series`). Two integrations by parts (Mathlib's
  `fourierCoeffOn_of_hasDerivAt`; the edge terms vanish because `h, h'` vanish at `±a`) give
  `|ĉ_n| ≤ (a/π)² sup|h''|/n²`. Mathlib's pointwise Fourier theorem for summable coefficients, on the
  circle of length `2a`, then gives `h(t) = Σ d_n cos(nπt/a) − r` on `[−a, a]`. Evenness removes the
  sines.
* **Tails** (`trunc_error`). The error `S_K − h` is uniformly `≤ μ_K = Σ_{n≥K}|d_n|`, and `½`-Hölder
  with constant `ν_K = Σ_{n≥K}|d_n|√(2nπ/a)`, from `|cos x − cos y| ≤ √(2|x − y|)`. Both tails tend
  to `0` since `|d_n| = O(n⁻²)`.
* **Energy of a truncated Hölder function** (`ind_energy`). If `φ² ≤ M` and
  `(φ(t) − φ(s))² ≤ D|t − s|` on `[−a, a]`, then `1_{[−a,a]}φ` has `f(0) − f(u) ≤ (aD + M)u`. So
  `E_arch ≤ (aD + M)·∫16e^{−u/4}` and `‖·‖² ≤ 2aM`. The jump at `±a` costs only `M·u`.

A diagonal choice (`truncDense_of_approx`) turns "every accuracy is reached in some `T K`" into
`TruncDense`, using that the spaces increase. Corollaries: `simple_of_cos_gap` and `lam2Ge_of_cos`,
round 60's transfer for this basis with no density hypothesis left.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## Energy of a truncated `½`-Hölder function -/

/-- If `φ² ≤ M` and `(φ t − φ s)² ≤ D|t − s|` on `[−a, a]`, the truncation `1_{[−a,a]}φ` has
`f(0) − f(u) ≤ (aD + M)u`. -/
theorem ind_autocorr_le {a D M : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hM : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M)
    (hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ D * |t - s|)
    (hD0 : 0 ≤ D) {u : ℝ} (hu : 0 < u) :
    autocorr ((Icc (-a) a).indicator φ) 0 - autocorr ((Icc (-a) a).indicator φ) u
      ≤ (a * D + M) * u := by
  set g := (Icc (-a) a).indicator φ with hg
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) (hM (-a) ⟨le_rfl, by linarith⟩)
  have hb : MemLp g 2 volume :=
    memLp_indicator_of_continuous hc measurableSet_Icc measure_Icc_lt_top.ne
      (C := Real.sqrt M) fun x hx => Real.abs_le_sqrt (hM x hx)
  rw [show autocorr g 0 - autocorr g u = normSq (fun t => g t - g (t + u)) / 2 by
    rw [normSq_sub_shift hb u]; ring]
  set B : ℝ → ℝ := fun t => D * u * (Icc (-a) a).indicator 1 t
    + M * ((Icc (a - u) a).indicator 1 t + (Icc (-a - u) (-a)).indicator 1 t) with hB
  have hi : ∀ p q : ℝ, Integrable ((Icc p q).indicator (1 : ℝ → ℝ)) := fun p q =>
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hBint : Integrable B :=
    ((hi _ _).const_mul (D * u)).add (((hi _ _).add (hi _ _)).const_mul M)
  have hpt : ∀ t, (g t - g (t + u)) ^ 2 ≤ B t := by
    intro t
    simp only [hB, hg, Set.indicator_apply, Pi.one_apply]
    by_cases h1 : t ∈ Icc (-a) a <;> by_cases h2 : t + u ∈ Icc (-a) a
    · simp only [h1, h2, ite_true]
      have := hD t h1 (t + u) h2
      rw [show t - (t + u) = -u by ring, abs_neg, abs_of_pos hu] at this
      have e1 : 0 ≤ M * ((if t ∈ Icc (a - u) a then (1 : ℝ) else 0)
          + (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0)) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
    · simp only [h1, h2, ite_true, ite_false, sub_zero]
      have ht : t ∈ Icc (a - u) a := by
        simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2 ⊢
        rcases h2 with h2 | h2 <;> [linarith [h1.1]; exact ⟨by linarith, h1.2⟩]
      simp only [ht, ite_true]
      have := hM t h1
      have e1 : 0 ≤ M * (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith [mul_nonneg (mul_nonneg hD0 hu.le) (zero_le_one' ℝ)]
    · simp only [h1, h2, ite_true, ite_false, zero_sub, neg_sq]
      have ht : t ∈ Icc (-a - u) (-a) := by
        simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · exact ⟨by linarith [h2.1], h1.le⟩
        · linarith [h2.2]
      simp only [ht, ite_true]
      have := hM (t + u) h2
      have e1 : 0 ≤ M * (if t ∈ Icc (a - u) a then (1 : ℝ) else 0) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
    · simp only [h1, h2, ite_false, sub_self]
      have e1 : 0 ≤ M * ((if t ∈ Icc (a - u) a then (1 : ℝ) else 0)
          + (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0)) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
  have hle : normSq (fun t => g t - g (t + u)) ≤ ∫ t, B t :=
    integral_mono ((hb.sub (memLp_shift hb u)).integrable_sq) hBint hpt
  have hBv : ∫ t, B t = D * u * (2 * a) + M * (2 * u) := by
    have v : ∀ p q : ℝ, p ≤ q → ∫ t, (Icc p q).indicator (1 : ℝ → ℝ) t = q - p := by
      intro p q hpq
      rw [integral_indicator_one measurableSet_Icc, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
    have e1 : ∫ t, B t = D * u * (∫ t, (Icc (-a) a).indicator (1 : ℝ → ℝ) t)
        + M * ((∫ t, (Icc (a - u) a).indicator (1 : ℝ → ℝ) t)
          + ∫ t, (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t) := by
      have I1 : Integrable (fun t => D * u * (Icc (-a) a).indicator (1 : ℝ → ℝ) t) :=
        (hi _ _).const_mul _
      have I2 : Integrable (fun t => (Icc (a - u) a).indicator (1 : ℝ → ℝ) t) := hi _ _
      have I3 : Integrable (fun t => (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t) := hi _ _
      have I23 : Integrable (fun t => M * ((Icc (a - u) a).indicator (1 : ℝ → ℝ) t
          + (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t)) := (I2.add I3).const_mul M
      rw [hB, integral_add I1 I23, integral_const_mul, integral_const_mul, integral_add I2 I3]
    rw [e1, v _ _ (by linarith), v _ _ (by linarith), v _ _ (by linarith)]
    ring
  rw [hBv] at hle
  nlinarith

/-- The constant `E₀ = ∫_{u>0} 16e^{−u/4}`. -/
def E0 : ℝ := ∫ u in Ioi (0 : ℝ), 16 * Real.exp (-(1 / 4) * u)

/-- **Energy of a truncated `½`-Hölder function**: the archimedean integrand is integrable and
`archE ≤ (aD + M)E₀`; also `‖1_{[−a,a]}φ‖² ≤ 2aM`. -/
theorem ind_energy {a D M : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hM : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M)
    (hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ D * |t - s|) (hD0 : 0 ≤ D) :
    MemLp ((Icc (-a) a).indicator φ) 2 volume ∧
    IntegrableOn (archIntegrand ((Icc (-a) a).indicator φ)) (Ioi 0) ∧
    archE ((Icc (-a) a).indicator φ) ≤ (a * D + M) * E0 ∧
    normSq ((Icc (-a) a).indicator φ) ≤ 2 * a * M := by
  set g := (Icc (-a) a).indicator φ with hg
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) (hM (-a) ⟨le_rfl, by linarith⟩)
  have hb : MemLp g 2 volume :=
    memLp_indicator_of_continuous hc measurableSet_Icc measure_Icc_lt_top.ne
      (C := Real.sqrt M) fun x hx => Real.abs_le_sqrt (hM x hx)
  have hC : 0 ≤ a * D + M := by positivity
  have hE : IntegrableOn (fun u => (a * D + M) * (16 * Real.exp (-(1 / 4) * u))) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 16).const_mul _
  have hpt : ∀ u ∈ Ioi (0 : ℝ), archIntegrand g u ≤ (a * D + M) * (16 * Real.exp (-(1 / 4) * u)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
      div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
    unfold archIntegrand
    calc (autocorr g 0 - autocorr g u) * (Real.exp (u / 2) / Real.sinh u)
        ≤ ((a * D + M) * u) * (Real.exp (u / 2) / Real.sinh u) :=
          mul_le_mul_of_nonneg_right (ind_autocorr_le ha hc hM hD hD0 hu0) hK.le
      _ = (a * D + M) * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
      _ ≤ (a * D + M) * (16 * Real.exp (-(1 / 4) * u)) :=
          mul_le_mul_of_nonneg_left (u_archK_le hu0) hC
  have hint : IntegrableOn (archIntegrand g) (Ioi 0) := by
    refine hE.mono' (measurable_archIntegrand hb).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hb hu)]
    exact hpt u hu
  refine ⟨hb, hint, ?_, ?_⟩
  · have := setIntegral_Ioi_le hE (fun u hu => archIntegrand_nonneg hb hu) hpt
    unfold archE E0
    rw [integral_const_mul] at this
    exact this
  · unfold normSq
    have hsq : (fun t => g t ^ 2) ≤ (Icc (-a) a).indicator (fun _ => M) := by
      intro t
      simp only [hg, Set.indicator_apply]
      split_ifs with h
      · exact hM t h
      · norm_num
    calc (∫ t, g t ^ 2) ≤ ∫ t, (Icc (-a) a).indicator (fun _ => M) t :=
          integral_mono hb.integrable_sq
            ((integrable_indicator_iff measurableSet_Icc).2
              (integrableOn_const measure_Icc_lt_top.ne)) hsq
      _ = 2 * a * M := by
          rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring

/-! ## Fourier series of an edge-flat `C²` function on `[−a, a]` -/

theorem fco_congr {α b b' : ℝ} (e : b = b') (h1 : α < b) (h2 : α < b') (F : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn h1 F n = fourierCoeffOn h2 F n := by subst e; rfl

theorem fco_norm_le {a b : ℝ} (hab : a < b) {F : ℝ → ℂ} {M : ℝ} (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (n : ℤ) : ‖fourierCoeffOn hab F n‖ ≤ M := by
  have : Fact (0 < b - a) := ⟨by linarith⟩
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h1 : ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • F x‖ ≤ M * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    rw [uIoc_of_le hab.le] at hx
    exact hF x ⟨hx.1.le, hx.2⟩
  rw [abs_of_pos (by linarith)] at h1
  have hp : 0 < b - a := by linarith
  calc ‖(1 / (b - a) : ℝ)‖ * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • F x‖
      ≤ (1 / (b - a)) * (M * (b - a)) := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M := by field_simp

theorem fco_deriv {a : ℝ} (hab : -a < a) {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hc' : Continuous f') (h0 : f a = 0) (h1 : f (-a) = 0) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (fun t => (f t : ℂ)) n‖
      = a / (π * |(n : ℝ)|) * ‖fourierCoeffOn hab (fun t => (f' t : ℂ)) n‖ := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => (hd x).ofReal_comp)
    ((Complex.continuous_ofReal.comp hc').intervalIntegrable _ _)]
  simp only [h0, h1, Complex.ofReal_zero, sub_self, mul_zero, zero_sub]
  have ha : 0 < a := by linarith
  rw [norm_mul, norm_neg, norm_mul, norm_div, norm_one]
  have e1 : ‖(-2 * (π : ℂ) * Complex.I * n)‖ = 2 * π * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_neg, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos pi_pos]; ring
  have e2 : ‖((a : ℂ) - ((-a : ℝ) : ℂ))‖ = 2 * a := by
    rw [show ((a : ℂ) - ((-a : ℝ) : ℂ)) = ((2 * a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [e1, e2]
  have hn' : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  field_simp

theorem re_mul_exp (c : ℂ) (θ : ℝ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I)).re = c.re * Real.cos θ - c.im * Real.sin θ := by
  rw [Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]

/-- **Cosine series of an edge-flat `C²` even function.** -/
theorem cos_series {a : ℝ} (ha : 0 < a) {h h₁ h₂ : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt h (h₁ x) x)
    (hd2 : ∀ x, HasDerivAt h₁ (h₂ x) x) (hc2 : Continuous h₂) {M₂ : ℝ} (hM2 : ∀ x, |h₂ x| ≤ M₂)
    (z0 : h a = 0) (z1 : h (-a) = 0) (z2 : h₁ a = 0) (z3 : h₁ (-a) = 0)
    (heven : ∀ t, h (-t) = h t) :
    ∃ d : ℕ → ℝ, ∃ r C : ℝ, (∀ n : ℕ, 1 ≤ n → |d n| ≤ C / (n : ℝ) ^ 2) ∧
      ∀ x ∈ Icc (-a) a, HasSum (fun n : ℕ => d n * Real.cos (n * π * x / a)) (h x + r) := by
  have hab : -a < a := by linarith
  have hc1 : Continuous h₁ := continuous_iff_continuousAt.2 fun x => (hd2 x).continuousAt
  have hc0 : Continuous h := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  set F : ℝ → ℂ := fun t => (h t : ℂ) with hF
  set c : ℤ → ℂ := fun n => fourierCoeffOn hab F n with hcdef
  -- the coefficient bound
  have hM0 : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM2 0)
  have hbd : ∀ n : ℤ, n ≠ 0 → ‖c n‖ ≤ (a / π) ^ 2 * M₂ * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have e1 := fco_deriv hab hd1 hc1 z0 z1 hn
    have e2 := fco_deriv hab hd2 hc2 z2 z3 hn
    have b2 : ‖fourierCoeffOn hab (fun t => (h₂ t : ℂ)) n‖ ≤ M₂ :=
      fco_norm_le hab (fun x _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM2 x) n
    have hn' : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
    have hq : 0 ≤ a / (π * |(n : ℝ)|) := by positivity
    show ‖fourierCoeffOn hab (fun t => (h t : ℂ)) n‖ ≤ _
    rw [e1, e2]
    calc a / (π * |(n : ℝ)|) * (a / (π * |(n : ℝ)|) * ‖fourierCoeffOn hab (fun t => (h₂ t : ℂ)) n‖)
        ≤ a / (π * |(n : ℝ)|) * (a / (π * |(n : ℝ)|) * M₂) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b2 hq) hq
      _ = (a / π) ^ 2 * M₂ * (1 / (n : ℝ) ^ 2) := by
          rw [← sq_abs (n : ℝ)]; field_simp
  have hsum : Summable c := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_one_div_int_pow.2 (by norm_num : 1 < 2)).mul_left ((a / π) ^ 2 * M₂)) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn using hbd n hn
  -- the periodic lift
  have hT : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hFe : F (-a) = F (-a + 2 * a) := by
    rw [show -a + 2 * a = a by ring]; simp only [hF, z0, z1]
  let G : C(AddCircle (2 * a), ℂ) :=
    ⟨AddCircle.liftIco (2 * a) (-a) F,
      AddCircle.liftIco_continuous hFe (Complex.continuous_ofReal.comp hc0).continuousOn⟩
  have hcoef : ∀ n, fourierCoeff G n = c n := by
    intro n
    show fourierCoeff (AddCircle.liftIco (2 * a) (-a) F) n = _
    rw [fourierCoeff_liftIco_eq]
    exact fco_congr (by ring) _ _ F n
  have hS : Summable (fourierCoeff G) := hsum.congr fun n => (hcoef n).symm
  have hGx : ∀ x ∈ Icc (-a) a, G (x : AddCircle (2 * a)) = F x := by
    intro x hx
    show AddCircle.liftIco (2 * a) (-a) F x = F x
    rcases eq_or_lt_of_le hx.2 with hxa | hxa
    · have e : ((a : ℝ) : AddCircle (2 * a)) = ((-a : ℝ) : AddCircle (2 * a)) := by
        have := AddCircle.coe_add_period (2 * a) (-a)
        rw [show -a + 2 * a = a by ring] at this
        exact this
      rw [hxa, e, AddCircle.liftIco_coe_apply (by constructor <;> linarith), hFe,
        show -a + 2 * a = a by ring]
    · exact AddCircle.liftIco_coe_apply ⟨hx.1, by linarith⟩
  -- the real series with sines
  have hre : ∀ x ∈ Icc (-a) a, HasSum (fun n : ℤ => (c n).re * Real.cos (n * π * x / a)
      - (c n).im * Real.sin (n * π * x / a)) (h x) := by
    intro x hx
    have h1 := Complex.hasSum_re (has_pointwise_sum_fourier_series_of_summable hS (x : AddCircle (2 * a)))
    rw [hGx x hx] at h1
    convert h1 using 1
    · funext n
      rw [hcoef, fourier_coe_apply, smul_eq_mul,
        show 2 * (π : ℂ) * Complex.I * n * x / ((2 * a : ℝ) : ℂ) = ((n * π * x / a : ℝ) : ℂ) * Complex.I by
          push_cast; field_simp, re_mul_exp]
  -- symmetrise: the sines cancel
  have hcos : ∀ x ∈ Icc (-a) a, HasSum (fun n : ℤ => (c n).re * Real.cos (n * π * x / a)) (h x) := by
    intro x hx
    have hx' : -x ∈ Icc (-a) a := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h2 := ((hre x hx).add (hre (-x) hx')).div_const 2
    rw [heven, show (h x + h x) / 2 = h x by ring] at h2
    convert h2 using 1
    funext n
    rw [show (n : ℝ) * π * -x / a = -(n * π * x / a) by ring, Real.cos_neg, Real.sin_neg]
    ring
  refine ⟨fun n => (c n).re + (c (-(n : ℤ))).re, (c 0).re, 2 * ((a / π) ^ 2 * M₂), ?_, ?_⟩
  · intro n hn
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have b1 := hbd n hn0
    have b2 := hbd (-(n : ℤ)) (neg_ne_zero.2 hn0)
    have r1 := Complex.abs_re_le_norm (c n)
    have r2 := Complex.abs_re_le_norm (c (-(n : ℤ)))
    push_cast at b1 b2
    rw [neg_sq] at b2
    calc |(c n).re + (c (-(n : ℤ))).re| ≤ |(c n).re| + |(c (-(n : ℤ))).re| := abs_add_le _ _
      _ ≤ 2 * ((a / π) ^ 2 * M₂) / (n : ℝ) ^ 2 := by
          rw [show 2 * ((a / π) ^ 2 * M₂) / (n : ℝ) ^ 2
            = (a / π) ^ 2 * M₂ * (1 / (n : ℝ) ^ 2) + (a / π) ^ 2 * M₂ * (1 / (n : ℝ) ^ 2) by ring]
          linarith
  · intro x hx
    have h3 := (hcos x hx).nat_add_neg
    convert h3 using 1
    · funext n
      push_cast
      rw [show -(n : ℝ) * π * x / a = -(n * π * x / a) by ring, Real.cos_neg]
      ring
    · simp

/-- The `K`-term cosine partial sum `Σ_{n<K} d_n cos(nπt/a) − r`. -/
def cosSum (a : ℝ) (d : ℕ → ℝ) (r : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.range K, d n * Real.cos (n * π * t / a)) - r

theorem abs_cos_sub_cos_le_sqrt (x y : ℝ) : |Real.cos x - Real.cos y| ≤ Real.sqrt (2 * |x - y|) := by
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.abs_cos_sub_cos_le x y
  have h2 : |Real.cos x - Real.cos y| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [Real.cos_le_one x, Real.cos_le_one y, Real.neg_one_le_cos x,
      Real.neg_one_le_cos y]
  nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg (Real.cos x - Real.cos y)),
    sq_abs (Real.cos x - Real.cos y)]

theorem sqrt_div_sq_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n / (n : ℝ) ^ 2 = ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one, Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hp
  rw [e]
  field_simp
  rw [Real.sq_sqrt hp.le]

/-- **Tail bounds.** If `h + r = Σ d_n cos(nπt/a)` on `[−a, a]` with `|d_n| ≤ C/n²`, the error
`S_K − h` of the partial sums is `≤ μ_K` in size and `½`-Hölder with constant `ν_K`, and
`μ_K, ν_K → 0`. -/
theorem trunc_error {a : ℝ} (ha : 0 < a) {h : ℝ → ℝ} {d : ℕ → ℝ} {r C : ℝ}
    (hd : ∀ n : ℕ, 1 ≤ n → |d n| ≤ C / (n : ℝ) ^ 2)
    (hs : ∀ x ∈ Icc (-a) a, HasSum (fun n : ℕ => d n * Real.cos (n * π * x / a)) (h x + r)) :
    ∃ μ ν : ℕ → ℝ, Tendsto μ atTop (𝓝 0) ∧ Tendsto ν atTop (𝓝 0) ∧ ∀ K,
      (∀ t ∈ Icc (-a) a, (cosSum a d r K t - h t) ^ 2 ≤ μ K ^ 2) ∧
      (∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a,
        ((cosSum a d r K t - h t) - (cosSum a d r K s - h s)) ^ 2 ≤ ν K ^ 2 * |t - s|) := by
  have hC0 : 0 ≤ C := by
    have := hd 1 le_rfl; simp at this; linarith [abs_nonneg (d 1)]
  have ev1 : ∀ᶠ n : ℕ in cofinite, 1 ≤ n := by
    filter_upwards [eventually_cofinite_ne 0] with n hn using Nat.one_le_iff_ne_zero.2 hn
  have hsd : Summable fun n => |d n| := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).mul_left C) ?_
    filter_upwards [ev1] with n hn
    rw [Real.norm_eq_abs, abs_abs, mul_one_div]; exact hd n hn
  set κ := Real.sqrt (2 * π / a) with hκ
  set β : ℕ → ℝ := fun n => |d n| * (κ * Real.sqrt n) with hβ
  have hsb : Summable β := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left (C * κ)) ?_
    filter_upwards [ev1] with n hn
    have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sqrt_div_sq_le hn]
    calc |d n| * (κ * Real.sqrt n) ≤ C / (n : ℝ) ^ 2 * (κ * Real.sqrt n) :=
          mul_le_mul_of_nonneg_right (hd n hn) (by positivity)
      _ = C * κ * (Real.sqrt n / (n : ℝ) ^ 2) := by ring
  refine ⟨fun K => ∑' m, |d (m + K)|, fun K => ∑' m, β (m + K),
    tendsto_sum_nat_add (fun m => |d m|), tendsto_sum_nat_add β, fun K => ?_⟩
  have hsdK : Summable fun m => |d (m + K)| := (summable_nat_add_iff K).2 hsd
  have hsbK : Summable fun m => β (m + K) := (summable_nat_add_iff K).2 hsb
  -- the error is minus the tail
  have htail : ∀ t ∈ Icc (-a) a, cosSum a d r K t - h t
      = -∑' m, d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * t / a) := by
    intro t ht
    have e := (hs t ht).summable.sum_add_tsum_nat_add K
    rw [(hs t ht).tsum_eq] at e
    unfold cosSum
    linarith
  have hμ0 : 0 ≤ ∑' m, |d (m + K)| := tsum_nonneg fun _ => abs_nonneg _
  have hν0 : 0 ≤ ∑' m, β (m + K) := tsum_nonneg fun m => by
    simp only [hβ]; exact mul_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  constructor
  · intro t ht
    rw [htail t ht, neg_sq, ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have hsn : Summable fun m => ‖d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * t / a)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) hsdK
    refine (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (fun m => ?_) hsdK)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · intro t ht s hs'
    rw [htail t ht, htail s hs']
    set ft : ℕ → ℝ := fun m => d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * t / a)
    set fs : ℕ → ℝ := fun m => d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * s / a)
    have hft : Summable ft := (summable_nat_add_iff K).2 (hs t ht).summable
    have hfs : Summable fs := (summable_nat_add_iff K).2 (hs s hs').summable
    have hpt : ∀ m, ‖ft m - fs m‖ ≤ β (m + K) * Real.sqrt |t - s| := by
      intro m
      have hn : (0 : ℝ) ≤ ((m + K : ℕ) : ℝ) := Nat.cast_nonneg _
      have key : |Real.cos (((m + K : ℕ) : ℝ) * π * t / a) - Real.cos (((m + K : ℕ) : ℝ) * π * s / a)|
          ≤ κ * Real.sqrt ((m + K : ℕ) : ℝ) * Real.sqrt |t - s| := by
        refine (abs_cos_sub_cos_le_sqrt _ _).trans (le_of_eq ?_)
        rw [show ((m + K : ℕ) : ℝ) * π * t / a - ((m + K : ℕ) : ℝ) * π * s / a
            = ((m + K : ℕ) : ℝ) * (π / a) * (t - s) by ring, abs_mul, abs_mul,
          abs_of_nonneg hn, abs_of_pos (div_pos pi_pos ha),
          show 2 * (((m + K : ℕ) : ℝ) * (π / a) * |t - s|)
            = (2 * π / a) * (((m + K : ℕ) : ℝ) * |t - s|) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_mul hn]
        ring
      show ‖d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * t / a)
          - d (m + K) * Real.cos (((m + K : ℕ) : ℝ) * π * s / a)‖
        ≤ |d (m + K)| * (κ * Real.sqrt ((m + K : ℕ) : ℝ)) * Real.sqrt |t - s|
      have := mul_le_mul_of_nonneg_left key (abs_nonneg (d (m + K)))
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      linarith
    have hsd' : Summable fun m => ‖ft m - fs m‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsbK.mul_right _)
    have hle : |∑' m, ft m - ∑' m, fs m| ≤ (∑' m, β (m + K)) * Real.sqrt |t - s| := by
      rw [← hft.tsum_sub hfs, ← Real.norm_eq_abs, ← tsum_mul_right]
      exact (norm_tsum_le_tsum_norm hsd').trans (hsd'.tsum_le_tsum hpt (hsbK.mul_right _))
    rw [show -∑' m, ft m - -∑' m, fs m = -(∑' m, ft m - ∑' m, fs m) by ring, neg_sq, ← sq_abs]
    calc |∑' m, ft m - ∑' m, fs m| ^ 2 ≤ ((∑' m, β (m + K)) * Real.sqrt |t - s|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hle 2
      _ = (∑' m, β (m + K)) ^ 2 * |t - s| := by
          rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]

/-! ## The cosine truncation spaces -/

/-- The paper's basis function `φ_k = 1_{[−a,a]}·cos(kπt/a)` (`tools/research/weil_prime_gram.py`,
`omega_k = k pi / a`). -/
def cosB (a : ℝ) (k : ℕ) : ℝ → ℝ := (Icc (-a) a).indicator fun t => Real.cos (k * π * t / a)

/-- The truncation space `span{φ_0, …, φ_{K−1}}`. -/
def cosTrunc (a : ℝ) (K : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {g | ∃ k < K, g = cosB a k}

theorem cosTrunc_mono (a : ℝ) : Monotone (cosTrunc a) := fun _ _ hKL =>
  Submodule.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, lt_of_lt_of_le hk hKL, e⟩

theorem cosB_probe {a : ℝ} (ha : 0 < a) (k : ℕ) : Probe a (cosB a k) := by
  have hc : Continuous fun t => Real.cos (k * π * t / a) := by fun_prop
  obtain ⟨hm, hi, -, -⟩ := ind_energy (D := 2 * (k * π / a)) (M := 1) ha.le hc
    (fun t _ => by nlinarith [Real.cos_sq_le_one (k * π * t / a)])
    (fun t _ s _ => by
      have h1 := abs_cos_sub_cos_le_sqrt (k * π * t / a) (k * π * s / a)
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, Real.sq_sqrt (by positivity)] at h2
      have hk : (0 : ℝ) ≤ k * π / a := by positivity
      calc (Real.cos (k * π * t / a) - Real.cos (k * π * s / a)) ^ 2
          ≤ 2 * |k * π * t / a - k * π * s / a| := h2
        _ = 2 * (k * π / a) * |t - s| := by
            rw [show k * π * t / a - k * π * s / a = (k * π / a) * (t - s) by ring, abs_mul,
              abs_of_nonneg hk]; ring)
    (by positivity)
  refine ⟨fun u => ?_, fun u hu => ?_, hm, hi⟩
  · simp only [cosB, Set.indicator_apply, Set.mem_Icc]
    rw [show (k : ℝ) * π * -u / a = -(k * π * u / a) by ring, Real.cos_neg]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨by linarith [h1.2], by linarith [h1.1]⟩ h2
    · exact absurd ⟨by linarith [h2.2], by linarith [h2.1]⟩ h1
    · rfl
  · simp only [cosB, Set.indicator_apply, Set.mem_Icc]
    split_ifs with h
    · exact absurd (abs_le.2 h) (not_le.2 hu)
    · rfl

/-- Every element of a cosine truncation space is a probe. -/
theorem probe_of_mem_cosTrunc {a : ℝ} (ha : 0 < a) {K : ℕ} {g : ℝ → ℝ} (hg : g ∈ cosTrunc a K) :
    Probe a g := by
  induction hg using Submodule.span_induction with
  | mem x hx => obtain ⟨k, -, rfl⟩ := hx; exact cosB_probe ha k
  | zero =>
      have := probe_smul (cosB_probe ha 0) 0
      convert this using 1; funext t; simp
  | add x y _ _ hx hy => exact (probe_add_sub hx hy).1
  | smul c x _ hx => exact probe_smul hx c

/-- The truncated partial sum `1_{[−a,a]}·(Σ_{n<K} d_n cos(nπt/a) − r)` lies in `cosTrunc a K`. -/
theorem cosSum_mem {a : ℝ} (d : ℕ → ℝ) (r : ℝ) {K : ℕ} (hK : 1 ≤ K) :
    (Icc (-a) a).indicator (cosSum a d r K) ∈ cosTrunc a K := by
  have e : (Icc (-a) a).indicator (cosSum a d r K)
      = (∑ n ∈ Finset.range K, d n • cosB a n) - r • cosB a 0 := by
    funext t
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosB, cosSum,
      Set.indicator_apply]
    split_ifs
    · simp
    · simp
  rw [e]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨n, Finset.mem_range.1 hn, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, hK, rfl⟩))

/-! ## Density -/

/-- **A diagonal choice.** If every probe is approximated to every accuracy inside some member of
an increasing family of spaces of probes, the family is `TruncDense`. -/
theorem truncDense_of_approx {a : ℝ} {T : ℕ → Submodule ℝ (ℝ → ℝ)} (hmono : Monotone T)
    (hsub : ∀ K f, f ∈ T K → Probe a f)
    (happ : ∀ f, Probe a f → ∀ ε > 0, ∃ K, ∃ F ∈ T K,
      normSq (fun t => F t - f t) + archE (fun t => F t - f t) ≤ ε) : TruncDense a T := by
  intro f hf
  choose Kj Gj hGj hGe using fun j : ℕ => happ f hf (1 / ((j : ℝ) + 1)) (by positivity)
  set J : ℕ → ℕ := fun K => Nat.findGreatest (fun j => Kj j ≤ K) K with hJdef
  have hJ : ∀ K, Kj 0 ≤ K → Kj (J K) ≤ K := fun K hK =>
    Nat.findGreatest_spec (P := fun j => Kj j ≤ K) (Nat.zero_le K) hK
  have hJge : ∀ j K, j ≤ K → Kj j ≤ K → j ≤ J K := fun j K h1 h2 =>
    Nat.le_findGreatest (P := fun j => Kj j ≤ K) h1 h2
  refine ⟨fun K => Gj (J K), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (Kj 0)] with K hK
    exact hmono (hJ K hK) (hGj (J K))
  · have hJt : Tendsto J atTop atTop := by
      refine tendsto_atTop.2 fun j => ?_
      filter_upwards [eventually_ge_atTop (max j (Kj j))] with K hK
      exact hJge j K (le_of_max_le_left hK) (le_of_max_le_right hK)
    have hup : Tendsto (fun K => 1 / ((J K : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hJt
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · refine Eventually.of_forall fun K => ?_
      have hp : Probe a (Gj (J K)) := hsub _ _ (hGj (J K))
      have hd : Probe a (fun t => Gj (J K) t - f t) := (probe_add_sub hp hf).2
      exact add_nonneg (normSq_nonneg _) (archE_nonneg hd)
    · exact Eventually.of_forall fun K => hGe (J K)

theorem E0_nonneg : 0 ≤ E0 :=
  setIntegral_nonneg measurableSet_Ioi fun u _ => by positivity

/-- **Every probe is approximated by a cosine truncation**, in `L²` plus archimedean energy. -/
theorem cos_approx {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : Probe a f) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∃ F ∈ cosTrunc a K, normSq (fun t => F t - f t) + archE (fun t => F t - f t) ≤ ε := by
  -- a `C²` edge-flat approximant (round 55)
  obtain ⟨ρ, δ, ψ, hρ0, hδ, hρ, hψ, h1, h2⟩ := av3_dense ha hf (ε / 8) (by positivity)
  have hc := av3_C2 hδ hψ
  set h := Av δ (Av δ (Av δ ψ)) with hh
  set h₁ : ℝ → ℝ := fun x => δ⁻¹ * (Av δ (Av δ ψ) (x + δ / 2) - Av δ (Av δ ψ) (x - δ / 2))
  set h₂ : ℝ → ℝ := fun x => (δ⁻¹) ^ 2 * (Av δ ψ (x + δ) - 2 * Av δ ψ x + Av δ ψ (x - δ))
  have hp : Probe a h := (probe_Av (probe_Av (probe_Av hψ hδ) hδ) hδ).mono (by linarith)
  have hc0 : Continuous h := continuous_iff_continuousAt.2 fun x => (hc.d1 x).continuousAt
  have hR : 0 ≤ ρ + 3 * δ / 2 := by positivity
  have hea : ρ + 3 * δ / 2 ≤ |a| := by rw [abs_of_pos ha]; exact hρ
  have hea' : ρ + 3 * δ / 2 ≤ |-a| := by rw [abs_neg]; exact hea
  have z0 := zero_of_ge hR hc0 hc.supp a hea
  have z1 := zero_of_ge hR hc0 hc.supp (-a) hea'
  have z2 := zero_of_ge hR hc.toC2Fun.cont1 hc.supp1 a hea
  have z3 := zero_of_ge hR hc.toC2Fun.cont1 hc.supp1 (-a) hea'
  obtain ⟨M₂, hM₂⟩ := hc.cont2.bounded_above_of_compact_support
    (hasCompactSupport_of_supp (a := ρ + 3 * δ / 2) hc.supp2)
  -- its cosine series and the tails
  obtain ⟨d, r, C, hdC, hs⟩ := cos_series ha hc.d1 hc.d2 hc.cont2
    (fun x => by rw [← Real.norm_eq_abs]; exact hM₂ x) z0 z1 z2 z3 hp.even
  obtain ⟨μ, ν, hμ, hν, hb⟩ := trunc_error ha hdC hs
  -- choose `K`
  set η := ε / (2 * (4 * a + 2 * a * E0 + 2 * E0 + 1)) with hη
  have hE0 := E0_nonneg
  have hη0 : 0 < η := by positivity
  have ev1 : ∀ᶠ K in atTop, μ K ^ 2 < η := by
    have := hμ.pow 2; rw [zero_pow two_ne_zero] at this
    exact this.eventually (Iio_mem_nhds hη0)
  have ev2 : ∀ᶠ K in atTop, ν K ^ 2 < η := by
    have := hν.pow 2; rw [zero_pow two_ne_zero] at this
    exact this.eventually (Iio_mem_nhds hη0)
  obtain ⟨K, hK1, hK2, hK3⟩ := (ev1.and (ev2.and (eventually_ge_atTop 1))).exists
  refine ⟨K, _, cosSum_mem d r hK3, ?_⟩
  -- the error `e = 1_{[−a,a]}(S_K − h)`
  have hcS : Continuous (cosSum a d r K) := by unfold cosSum; fun_prop
  obtain ⟨hem, hei, heE, heN⟩ := ind_energy (φ := fun t => cosSum a d r K t - h t)
    (D := ν K ^ 2) (M := μ K ^ 2) ha.le (hcS.sub hc0) (hb K).1 (hb K).2 (sq_nonneg _)
  set e := (Icc (-a) a).indicator fun t => cosSum a d r K t - h t with he
  have pd : Probe a (fun t => h t - f t) := (probe_add_sub hp hf).2
  have hdec : (fun t => (Icc (-a) a).indicator (cosSum a d r K) t - f t)
      = fun t => e t + (h t - f t) := by
    funext t
    simp only [he, Set.indicator_apply]
    split_ifs with ht
    · ring
    · have : a < |t| := by
        by_contra hn; push Not at hn; exact ht (abs_le.1 hn)
      rw [hp.supp t this]; ring
  rw [hdec]
  have hN := normSq_add_le hem pd.memL2
  have hA : archE (fun t => e t + (h t - f t)) ≤ 2 * archE e + 2 * archE (fun t => h t - f t) := by
    have hsum : IntegrableOn (fun u => 2 * archIntegrand e u
        + 2 * archIntegrand (fun t => h t - f t) u) (Ioi 0) :=
      (hei.const_mul 2).add (pd.arch.const_mul 2)
    have hle := setIntegral_Ioi_le hsum
      (fun u hu => archIntegrand_nonneg (hem.add pd.memL2) hu)
      (fun u hu => archIntegrand_add_le hem pd.memL2 hu)
    have i1 : IntegrableOn (fun u => 2 * archIntegrand e u) (Ioi 0) := hei.const_mul 2
    have i2 : IntegrableOn (fun u => 2 * archIntegrand (fun t => h t - f t) u) (Ioi 0) :=
      pd.arch.const_mul 2
    unfold archE
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hle
    exact hle
  have hμη : μ K ^ 2 ≤ η := hK1.le
  have hνη : ν K ^ 2 ≤ η := hK2.le
  have key : 4 * a * μ K ^ 2 + 2 * (a * ν K ^ 2 + μ K ^ 2) * E0 ≤ ε / 2 := by
    have : 4 * a * μ K ^ 2 + 2 * (a * ν K ^ 2 + μ K ^ 2) * E0
        ≤ η * (4 * a + 2 * a * E0 + 2 * E0 + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hμη ha.le, mul_le_mul_of_nonneg_left hνη ha.le,
        mul_le_mul_of_nonneg_left hμη hE0, mul_le_mul_of_nonneg_left hνη (mul_nonneg ha.le hE0),
        hη0]
    have e2 : η * (4 * a + 2 * a * E0 + 2 * E0 + 1) = ε / 2 := by
      rw [hη]; field_simp
    linarith
  have h1' : normSq (fun t => h t - f t) ≤ ε / 8 := h1
  have h2' : archE (fun t => h t - f t) ≤ ε / 8 := h2
  nlinarith

/-- **`TruncDense` for the cosine truncations.** The spaces `span{1_{[−a,a]}cos(kπt/a) : k < K}`
approximate every probe in `L²` and archimedean energy. -/
theorem cosTrunc_dense {a : ℝ} (ha : 0 < a) : TruncDense a (cosTrunc a) :=
  truncDense_of_approx (cosTrunc_mono a) (fun _ _ hg => probe_of_mem_cosTrunc ha hg)
    (fun _ hf _ hε => cos_approx ha hf hε)

/-- **The Galerkin transfer, unconditional on density**, for the paper's cosine basis: if the
truncated forms have `λ₂(T_K) ≥ λ₁(T_K) + γ` eventually, the ground state of `Q` is simple. -/
theorem simple_of_cos_gap {a : ℝ} (ha : 0 < a) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ᶠ K in atTop, ∀ f ∈ cosTrunc a K, 0 < normSq f →
      Lam2GeT a (cosTrunc a K) (weilQ a f / normSq f + γ))
    {g : ℝ → ℝ} (hg : IsGroundState a g) : SimpleGround a g :=
  simple_of_trunc_gap ha (fun _ _ hf => probe_of_mem_cosTrunc ha hf) (cosTrunc_dense ha) hγ hgap hg

/-- The `λ₂` transfer for the cosine basis. -/
theorem lam2Ge_of_cos {a : ℝ} (ha : 0 < a) {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    (hT : ∀ᶠ K in atTop, Lam2GeT a (cosTrunc a K) (s K)) {ε : ℝ} (hε : 0 < ε) :
    Lam2Ge a (s₀ - ε) :=
  lam2Ge_of_trunc ha (fun _ _ hf => probe_of_mem_cosTrunc ha hf) (cosTrunc_dense ha) hs hT hε

end Pilot1ca

#print axioms Pilot1ca.ind_energy
#print axioms Pilot1ca.cos_series
#print axioms Pilot1ca.trunc_error
#print axioms Pilot1ca.cosB_probe
#print axioms Pilot1ca.truncDense_of_approx
#print axioms Pilot1ca.cos_approx
#print axioms Pilot1ca.cosTrunc_dense
#print axioms Pilot1ca.simple_of_cos_gap
#print axioms Pilot1ca.lam2Ge_of_cos
