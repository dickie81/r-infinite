import Mathlib

/-! # Landau's theorem for Laplace transforms (round 220)

Let `A ≥ 0` and `φ ≥ 0` on a measure space, and let `L(s) = ∫ A e^{−sφ} dμ`. With `φ(λ) = λ` on
`(0, ∞)` this is the Laplace transform of `A`; with `φ = log` on `(1, ∞)` it is the Mellin integral
`∫ A(x) x^{−s} dx`.

**Landau's theorem** (`landau`): if the integral converges for every real `σ > σ₀`, and `L` agrees
near `σ₀`, on the side `Re s > σ₀`, with a function holomorphic on a disc around `σ₀`, then the
integral converges at some real `σ < σ₀`. So the real point of the abscissa of convergence is always
a singularity.

The proof: at `c = σ₀ + η/4` the integral has the power series `Σ (−y)ⁿ/n!·∫Aφⁿe^{−cφ}` in `y = s − c`
(`lap_hasFPowerSeriesOnBall`). By uniqueness of power series it is the Taylor series of the
holomorphic extension, so it converges on a disc of radius `η/2`, beyond `σ₀`. At the real point
`c − δ`, `δ = 3η/8`, every term is nonnegative, and Tonelli turns the convergent series back into
the integral at `σ₀ − η/8`.

* `lap_hasFPowerSeriesOnBall`, `lap_differentiableOn`: `L` is holomorphic on `Re s > σ₀`.
* `landau`: the theorem.
* `landau_abscissa`: the global form. If the integral converges somewhere and `L` agrees on
  `Re s > σ₁` with a function holomorphic near every real point `> σ₀`, it converges for every
  `σ > σ₀`.
* `eqOn_convex` (the identity theorem on a convex open set) and `exists_pos_lb` (a positive lower
  bound for finitely many positive numbers): helpers for the applications.
* `residue_eq_zero`: the pole test used by all three applications. A function that equals `L`
  on a segment `p + (0, ε)` and has the form `G(z) + R/(z − p)` there, with `G` continuous at `p`
  and `L` continuous at `p`, has `R = 0`.
-/

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Nat NNReal ENNReal

noncomputable section

namespace LandauLaplace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {A ph : α → ℝ}

/-- The generalised Laplace transform `L(s) = ∫ A e^{−sph} dμ`. -/
def lap (μ : Measure α) (A ph : α → ℝ) (s : ℂ) : ℂ := ∫ x, (A x : ℂ) * cexp (-s * ph x) ∂μ

/-- Convergence at the real point `σ`. -/
def Conv (μ : Measure α) (A ph : α → ℝ) (σ : ℝ) : Prop :=
  Integrable (fun x => A x * Real.exp (-σ * ph x)) μ

/-- The moments `∫ A phⁿ e^{−sph} dμ`. -/
def mom (μ : Measure α) (A ph : α → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ x, (A x : ℂ) * (ph x : ℂ) ^ n * cexp (-s * ph x) ∂μ

/-- The standing hypotheses: `A ≥ 0`, `ph ≥ 0`, both measurable. -/
structure Hyp (μ : Measure α) (A ph : α → ℝ) : Prop where
  A_nonneg : ∀ᵐ x ∂μ, 0 ≤ A x
  ph_nonneg : ∀ᵐ x ∂μ, 0 ≤ ph x
  A_meas : AEStronglyMeasurable A μ
  ph_meas : AEStronglyMeasurable ph μ

/-! ## Convergence -/

theorem Hyp.meas_exp (h : Hyp μ A ph) (σ : ℝ) :
    AEStronglyMeasurable (fun x => A x * Real.exp (-σ * ph x)) μ :=
  h.A_meas.mul ((by fun_prop : Continuous fun y : ℝ => Real.exp (-σ * y)).comp_aestronglyMeasurable
    h.ph_meas)

theorem Hyp.meas_mom (h : Hyp μ A ph) (s : ℂ) (n : ℕ) :
    AEStronglyMeasurable (fun x => (A x : ℂ) * (ph x : ℂ) ^ n * cexp (-s * ph x)) μ :=
  ((Complex.continuous_ofReal.comp_aestronglyMeasurable h.A_meas).mul
    ((by fun_prop : Continuous fun y : ℝ => (y : ℂ) ^ n).comp_aestronglyMeasurable h.ph_meas)).mul
    ((by fun_prop : Continuous fun y : ℝ => cexp (-s * y)).comp_aestronglyMeasurable h.ph_meas)

/-- Convergence propagates to the right. -/
theorem conv_mono (h : Hyp μ A ph) {σ σ' : ℝ} (hc : Conv μ A ph σ) (hσ : σ ≤ σ') :
    Conv μ A ph σ' := by
  refine hc.mono' (h.meas_exp σ') ?_
  filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hA

omit [MeasurableSpace α] in
theorem norm_mom_integrand {s : ℂ} {n : ℕ} {x : α} (hA : 0 ≤ A x) (hph : 0 ≤ ph x) :
    ‖(A x : ℂ) * (ph x : ℂ) ^ n * cexp (-s * ph x)‖ = A x * ph x ^ n * Real.exp (-s.re * ph x) := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hA,
    Real.norm_of_nonneg hph, Complex.norm_exp]
  congr 2
  simp

/-- `yⁿ e^{−εy} ≤ n!/εⁿ` for `y ≥ 0`. -/
theorem pow_mul_exp_le {ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-ε * y) ≤ n ! / ε ^ n := by
  have h := Real.pow_div_factorial_le_exp (x := ε * y) (mul_nonneg hε.le hy) n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ (pow_pos hε n)]
  have he : Real.exp (ε * y) * Real.exp (-ε * y) = 1 := by rw [← Real.exp_add]; simp
  have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-ε * y)).le
  calc y ^ n * Real.exp (-ε * y) * ε ^ n = ε ^ n * y ^ n * Real.exp (-ε * y) := by ring
    _ ≤ Real.exp (ε * y) * n ! * Real.exp (-ε * y) := this
    _ = n ! := by rw [mul_right_comm, he, one_mul]

/-- The moments converge to the right of any point of convergence. -/
theorem integrable_mom (h : Hyp μ A ph) {σ : ℝ} (hc : Conv μ A ph σ) {s : ℂ} (hs : σ < s.re)
    (n : ℕ) : Integrable (fun x => (A x : ℂ) * (ph x : ℂ) ^ n * cexp (-s * ph x)) μ := by
  set ε := s.re - σ
  have hε : 0 < ε := by simp only [ε]; linarith
  refine (hc.const_mul (n ! / ε ^ n)).mono' (h.meas_mom s n) ?_
  filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
  rw [norm_mom_integrand hA hph]
  have hb := pow_mul_exp_le hε hph n
  have e : A x * ph x ^ n * Real.exp (-s.re * ph x)
      = A x * Real.exp (-σ * ph x) * (ph x ^ n * Real.exp (-ε * ph x)) := by
    rw [mul_mul_mul_comm, ← Real.exp_add]; simp only [ε]; ring_nf
  rw [e]
  calc A x * Real.exp (-σ * ph x) * (ph x ^ n * Real.exp (-ε * ph x))
      ≤ A x * Real.exp (-σ * ph x) * (n ! / ε ^ n) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The real moments `∫ A phⁿ e^{−cph}` at a real point. -/
def momR (μ : Measure α) (A ph : α → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  ∫ x, A x * ph x ^ n * Real.exp (-c * ph x) ∂μ

theorem mom_ofReal (c : ℝ) (n : ℕ) : mom μ A ph c n = momR μ A ph c n := by
  unfold mom momR
  rw [← integral_complex_ofReal]
  congr 1; funext x
  push_cast; ring_nf

theorem integrable_momR (h : Hyp μ A ph) {σ c : ℝ} (hc : Conv μ A ph σ) (hs : σ < c) (n : ℕ) :
    Integrable (fun x => A x * ph x ^ n * Real.exp (-c * ph x)) μ := by
  have := (integrable_mom h hc (s := c) (by simpa using hs) n).norm
  refine this.congr ?_
  filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
  rw [norm_mom_integrand hA hph]; simp

/-- `Σ_{n<N} (rph)ⁿ/n!·Aphⁿ... ≤ ∫ A e^{−(c−r)ph}`: the partial sums of the real moment series are
bounded by the integral at `c − r`. -/
theorem sum_momR_le (h : Hyp μ A ph) {σ c r : ℝ} (hc : Conv μ A ph σ) (hs : σ < c) (hr : 0 ≤ r)
    (hcr : Conv μ A ph (c - r)) (N : ℕ) :
    ∑ n ∈ Finset.range N, r ^ n / n ! * momR μ A ph c n
      ≤ ∫ x, A x * Real.exp (-(c - r) * ph x) ∂μ := by
  unfold momR
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun n _ => (integrable_momR h hc hs n).const_mul _]
  refine integral_mono_ae (integrable_finsetSum _ fun n _ => (integrable_momR h hc hs n).const_mul _)
    hcr ?_
  filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
  have e : ∀ n : ℕ, r ^ n / n ! * (A x * ph x ^ n * Real.exp (-c * ph x))
      = A x * Real.exp (-c * ph x) * ((r * ph x) ^ n / n !) := fun n => by rw [mul_pow]; ring
  simp_rw [e, ← Finset.mul_sum]
  have hexp : A x * Real.exp (-(c - r) * ph x) = A x * Real.exp (-c * ph x) * Real.exp (r * ph x) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) N) (by positivity)

/-! ## The power series -/

/-- **The power series of `L`**: for `‖w‖ < Re s − σ`,
`L(s − w) = Σ wⁿ/n!·∫Aphⁿe^{−sph}`. -/
theorem hasSum_lap (h : Hyp μ A ph) {σ : ℝ} (hc : Conv μ A ph σ) {s w : ℂ} (hw : σ < s.re - ‖w‖) :
    HasSum (fun n => w ^ n / n ! * mom μ A ph s n) (lap μ A ph (s - w)) := by
  have hs : σ < s.re := by linarith [norm_nonneg w]
  set F : ℕ → α → ℂ := fun n x => w ^ n / n ! * ((A x : ℂ) * (ph x : ℂ) ^ n * cexp (-s * ph x))
  have hint : ∀ n, Integrable (F n) μ := fun n => (integrable_mom h hc hs n).const_mul _
  have hnorm : ∀ n, ∫ x, ‖F n x‖ ∂μ = ‖w‖ ^ n / n ! * momR μ A ph s.re n := fun n => by
    unfold momR
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
    simp only [F]
    rw [norm_mul, norm_mom_integrand hA hph, norm_div, norm_pow, Complex.norm_natCast]
  have hsum : Summable fun n => ∫ x, ‖F n x‖ ∂μ := by
    simp_rw [hnorm]
    refine summable_of_sum_range_le (fun n => mul_nonneg (by positivity)
      (integral_nonneg_of_ae (by
        filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph; positivity)))
      (fun N => sum_momR_le h hc hs (norm_nonneg w)
        (conv_mono h hc (show σ ≤ s.re - ‖w‖ by linarith)) N)
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  have hpt : ∀ x, HasSum (fun n => F n x) ((A x : ℂ) * cexp (-(s - w) * ph x)) := fun x => by
    have he := NormedSpace.expSeries_div_hasSum_exp (w * (ph x : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at he
    have := he.mul_left ((A x : ℂ) * cexp (-s * ph x))
    convert this using 1
    · funext n; simp only [F]; rw [mul_pow]; ring
    · rw [mul_assoc, ← Complex.exp_add]; ring_nf
  have e1 : (fun n => ∫ x, F n x ∂μ) = fun n => w ^ n / n ! * mom μ A ph s n := by
    funext n; simp only [F]; rw [integral_const_mul]; rfl
  have e2 : ∫ x, ∑' n, F n x ∂μ = lap μ A ph (s - w) := by
    unfold lap; congr 1; funext x; exact (hpt x).tsum_eq
  rwa [e1, e2] at H

/-- The coefficients of the power series of `L` at `s`. -/
def coef (μ : Measure α) (A ph : α → ℝ) (s : ℂ) (n : ℕ) : ℂ := (-1) ^ n * mom μ A ph s n / n !

/-- **`L` is analytic**: on the disc of radius `r` around `s` when `σ < Re s − r` and the integral
converges at `σ`. -/
theorem lap_hasFPowerSeriesOnBall (h : Hyp μ A ph) {σ : ℝ} (hc : Conv μ A ph σ) {s : ℂ} {r : ℝ≥0}
    (hr0 : 0 < r) (hr : σ < s.re - r) :
    HasFPowerSeriesOnBall (lap μ A ph) (FormalMultilinearSeries.ofScalars ℂ (coef μ A ph s)) s r := by
  have hs : σ < s.re := by linarith [r.2]
  refine ⟨?_, by exact_mod_cast hr0, fun {y} hy => ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _
      (∫ x, A x * Real.exp (-(s.re - r) * ph x) ∂μ) fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    unfold coef
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    have hm : ‖mom μ A ph s n‖ ≤ momR μ A ph s.re n := by
      unfold mom momR
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
      filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
      exact norm_mom_integrand hA hph
    have hcr : Conv μ A ph (s.re - r) := conv_mono h hc hr.le
    have h1 := sum_momR_le h hc hs r.2 hcr (n + 1)
    rw [Finset.sum_range_succ] at h1
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, (r : ℝ) ^ k / k ! * momR μ A ph s.re k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (integral_nonneg_of_ae (by
        filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph; positivity))
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    calc ‖mom μ A ph s n‖ / n ! * (r : ℝ) ^ n ≤ momR μ A ph s.re n / n ! * (r : ℝ) ^ n := by gcongr
      _ = (r : ℝ) ^ n / n ! * momR μ A ph s.re n := by ring
      _ ≤ _ := (le_add_of_nonneg_left h0).trans h1
  · have hy' : ‖y‖ < r := by
      have := hy
      rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, dist_zero_right] at this
      exact this
    have H := hasSum_lap h hc (w := -y) (s := s) (by rw [norm_neg]; linarith)
    rw [sub_neg_eq_add] at H
    convert H using 1
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    unfold coef
    rw [neg_pow]; ring

/-- **`L` is holomorphic on its half-plane of convergence.** -/
theorem lap_differentiableOn (h : Hyp μ A ph) {σ₀ : ℝ} (hconv : ∀ σ, σ₀ < σ → Conv μ A ph σ) :
    DifferentiableOn ℂ (lap μ A ph) {s | σ₀ < s.re} := by
  intro s hs
  have hs' : σ₀ < s.re := hs
  set r : ℝ≥0 := ⟨(s.re - σ₀) / 4, by linarith⟩
  have H := lap_hasFPowerSeriesOnBall h (hconv ((σ₀ + s.re) / 2) (by linarith))
    (s := s) (r := r) (by rw [← NNReal.coe_pos]; show 0 < (s.re - σ₀) / 4; linarith)
    (by show (σ₀ + s.re) / 2 < s.re - (s.re - σ₀) / 4; linarith)
  exact H.analyticAt.differentiableAt.differentiableWithinAt

/-! ## Landau's theorem -/

/-- Tonelli for the real moment series: if `Σ δⁿ/n!·∫Aphⁿe^{−cph}` converges, the integral converges at
`c − δ`. -/
theorem conv_of_summable (h : Hyp μ A ph) {σ c δ : ℝ} (hc : Conv μ A ph σ) (hs : σ < c) (hδ : 0 ≤ δ)
    (hsum : Summable fun n => δ ^ n / n ! * momR μ A ph c n) : Conv μ A ph (c - δ) := by
  have hnn : ∀ n, 0 ≤ δ ^ n / n ! * momR μ A ph c n := fun n => mul_nonneg (by positivity)
    (integral_nonneg_of_ae (by filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph; positivity))
  refine ⟨h.meas_exp _, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (by
    filter_upwards [h.A_nonneg] with x hA; positivity)]
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (A x * Real.exp (-(c - δ) * ph x))
      = ∑' n, ENNReal.ofReal (A x * ph x ^ n * Real.exp (-c * ph x) * (δ ^ n / n !)) := by
    filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph
    have he := NormedSpace.expSeries_div_hasSum_exp (δ * ph x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have hx := he.mul_left (A x * Real.exp (-c * ph x))
    have hfx : HasSum (fun n => A x * ph x ^ n * Real.exp (-c * ph x) * (δ ^ n / n !)) (A x * Real.exp (-(c - δ) * ph x)) := by
      convert hx using 1
      · funext n; rw [mul_pow]; ring
      · rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [← hfx.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      hfx.summable]
  rw [lintegral_congr_ae hpt, lintegral_tsum fun n => ?_]
  · have hn : ∀ n, ∫⁻ x, ENNReal.ofReal (A x * ph x ^ n * Real.exp (-c * ph x) * (δ ^ n / n !)) ∂μ = ENNReal.ofReal (δ ^ n / n ! * momR μ A ph c n) :=
      fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_momR h hc hs n).mul_const _) (by
          filter_upwards [h.A_nonneg, h.ph_nonneg] with x hA hph; positivity)]
        congr 1
        unfold momR; rw [← integral_const_mul]; congr 1; funext x; ring
    simp_rw [hn]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    exact ENNReal.ofReal_lt_top
  · exact (((integrable_momR h hc hs n).mul_const _).aestronglyMeasurable.aemeasurable).ennreal_ofReal

/-- **Landau's theorem.** If `∫ A e^{−σph} dμ` converges for every real `σ > σ₀`, and a function
holomorphic on the disc of radius `η` around `σ₀` agrees there with `L` on `Re s > σ₀`, then the
integral converges at some real `σ < σ₀`. -/
theorem landau (h : Hyp μ A ph) {σ₀ : ℝ} (hconv : ∀ σ, σ₀ < σ → Conv μ A ph σ) {η : ℝ} (hη : 0 < η)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball (σ₀ : ℂ) η))
    (hFL : ∀ s ∈ ball (σ₀ : ℂ) η, σ₀ < s.re → F s = lap μ A ph s) :
    ∃ σ < σ₀, Conv μ A ph σ := by
  set c : ℝ := σ₀ + η / 4
  have hc : Conv μ A ph (σ₀ + η / 16) := hconv _ (by linarith)
  set r : ℝ≥0 := ⟨η / 8, by positivity⟩
  have hq := lap_hasFPowerSeriesOnBall h hc (s := (c : ℂ)) (r := r)
    (by rw [← NNReal.coe_pos]; show 0 < η / 8; positivity)
    (by show σ₀ + η / 16 < (c : ℂ).re - η / 8; simp only [ofReal_re, c]; linarith)
  -- `F = L` near `c`
  have hU : {s : ℂ | s ∈ ball (σ₀ : ℂ) η ∧ σ₀ < s.re} ∈ 𝓝 (c : ℂ) := by
    refine IsOpen.mem_nhds (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)) ⟨?_, ?_⟩
    · rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp only [c]; rw [show σ₀ + η / 4 - σ₀ = η / 4 by ring, abs_of_pos (by positivity)]; linarith
    · simp only [ofReal_re, c]; linarith
  have heq : lap μ A ph =ᶠ[𝓝 (c : ℂ)] F := Filter.mem_of_superset hU fun s hs => (hFL s hs.1 hs.2).symm
  -- the Taylor series of `F` on the disc of radius `η/2`
  set R : ℝ≥0 := ⟨η / 2, by positivity⟩
  have hsub : closedBall (c : ℂ) R ⊆ ball (σ₀ : ℂ) η := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    have : dist (c : ℂ) σ₀ = η / 4 := by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp only [c]; rw [show σ₀ + η / 4 - σ₀ = η / 4 by ring, abs_of_pos (by positivity)]
    have hz' : dist z c ≤ η / 2 := hz
    linarith [dist_triangle z c σ₀]
  have hp := (hF.mono hsub).hasFPowerSeriesOnBall (by rw [← NNReal.coe_pos]; show 0 < η / 2; positivity)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries (hq.hasFPowerSeriesAt.congr heq)
  rw [hpq] at hp
  -- evaluate at `c − δ`, `δ = 3η/8`
  set δ : ℝ := 3 * η / 8
  have hy : ((-δ : ℝ) : ℂ) ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    show δ < η / 2; simp only [δ]; linarith
  have hs := hp.hasSum hy
  have hterm : ∀ n, FormalMultilinearSeries.ofScalars ℂ (coef μ A ph c) n (fun _ => ((-δ : ℝ) : ℂ))
      = ((δ ^ n / n ! * momR μ A ph c n : ℝ) : ℂ) := fun n => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    unfold coef
    rw [mom_ofReal]
    push_cast
    rw [neg_pow (δ : ℂ) n]
    have h1 : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination ((δ : ℂ) ^ n / n ! * (momR μ A ph c n : ℂ)) * h1
  simp_rw [hterm] at hs
  have hsum : Summable fun n => δ ^ n / n ! * momR μ A ph c n := Complex.summable_ofReal.1 hs.summable
  refine ⟨c - δ, by simp only [c, δ]; linarith, conv_of_summable h hc (by simp only [c]; linarith)
    (by positivity) hsum⟩

/-- **The global form.** Suppose the integral converges at some real point, and for every real
`c > σ₀` at which it converges on `(c, ∞)` there is a disc around `c` carrying a holomorphic `F` that
agrees with `L` on `Re s > c`. Then the integral converges for every `σ > σ₀`. -/
theorem landau_abscissa (h : Hyp μ A ph) {σ₀ σ₁ : ℝ} (h₁ : Conv μ A ph σ₁)
    (hloc : ∀ c : ℝ, σ₀ < c → (∀ τ, c < τ → Conv μ A ph τ) →
      ∃ η > 0, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (c : ℂ) η) ∧
        ∀ s ∈ ball (c : ℂ) η, c < s.re → F s = lap μ A ph s) :
    ∀ σ, σ₀ < σ → Conv μ A ph σ := by
  intro σ hσ
  by_contra hno
  set S := {τ : ℝ | Conv μ A ph τ}
  have hSne : S.Nonempty := ⟨σ₁, h₁⟩
  -- `S` is upward closed and misses `σ`, so it lies above `σ`
  have hup : ∀ τ ∈ S, σ < τ := fun τ hτ => by
    by_contra hle; push Not at hle; exact hno (conv_mono h hτ hle)
  have hbdd : BddBelow S := ⟨σ, fun τ hτ => (hup τ hτ).le⟩
  set c := sInf S
  have hσc : σ ≤ c := le_csInf hSne fun τ hτ => (hup τ hτ).le
  have habove : ∀ τ, c < τ → Conv μ A ph τ := fun τ hτ => by
    obtain ⟨τ', hτ', hlt⟩ := exists_lt_of_csInf_lt hSne hτ
    exact conv_mono h hτ' hlt.le
  obtain ⟨η, hη, F, hF, hFL⟩ := hloc c (by linarith) habove
  obtain ⟨τ, hτ, hτc⟩ := landau h habove hη hF hFL
  exact absurd (csInf_le hbdd hτc) (not_le.2 hτ)

/-! ## The pole test -/

/-- **No pole where `L` is continuous.** If on `p + (0, ε)` a function `F` equals `L` and has the form
`G(z) + R/(z − p)`, with `G` and `L` continuous at `p`, then `R = 0`. -/
theorem residue_eq_zero {L G : ℂ → ℂ} {p R : ℂ} {ε : ℝ} (hε : 0 < ε) (hL : ContinuousAt L p)
    (hG : ContinuousAt G p)
    (hF : ∀ x : ℝ, 0 < x → x < ε → L (p + x) = G (p + x) + R / ((p + x) - p)) : R = 0 := by
  -- `R = x(L − G)(p + x) → 0` as `x → 0⁺`
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) * (L (p + x) - G (p + x))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => p + (x : ℂ)) (𝓝[>] 0) (𝓝 p) := by
      have : Tendsto (fun x : ℝ => p + (x : ℂ)) (𝓝 0) (𝓝 (p + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have := h2.mul ((hL.tendsto.comp h1).sub (hG.tendsto.comp h1))
    simpa using this
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, (x : ℂ) * (L (p + x) - G (p + x)) = R := by
    filter_upwards [Ioo_mem_nhdsGT hε] with x hx
    rw [hF x hx.1 hx.2, add_sub_cancel_left, add_sub_cancel_left]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    field_simp
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)) hlim

/-! ## Two helpers for the applications -/

theorem eqOn_convex {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hfg : f =ᶠ[𝓝 z0] g) : EqOn f g U :=
  (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hU) hc.isPreconnected
    hz0 hfg

/-- A positive lower bound for finitely many positive numbers. -/
theorem exists_pos_lb {β : Type*} (T : Finset β) (g : β → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ m > 0, ∀ i ∈ T, m ≤ g i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T _ ih =>
    obtain ⟨m, hm, h⟩ := ih
    refine ⟨min m (g a), lt_min hm (hg a), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

end LandauLaplace

#print axioms LandauLaplace.lap_differentiableOn
#print axioms LandauLaplace.landau
#print axioms LandauLaplace.landau_abscissa
#print axioms LandauLaplace.residue_eq_zero
