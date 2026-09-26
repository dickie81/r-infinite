import Mathlib
import HurwitzCross

/-! # Fourier inversion for the autocorrelation (round 127)

For `g` even, square-integrable and supported in `[−a, a]` (`ESupp`), with `f = autocorr g` and
`ĝ` real on the real line:

* `fourier_autocorr`: `∫ f(x)e^{irx} dx = ĝ(r)²` (Fubini on `g ⊗ g`);
* `integrable_hsq`: `∫ĝ² < ∞`, by Gaussian regularisation and monotone convergence (no Plancherel);
* `gh_hsq`: **Fourier inversion**, `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`, from Mathlib's
  `Continuous.fourierInv_fourier_eq`. So `f` is determined by `ĝ²` on the real line.

This is round 126's Part A, moved here from ExplicitBridge.lean and stated without the archimedean
hypothesis (which it never used), so that SwapRealize.lean can use it: there it proves the
autocorrelation identity R2 of the zero swap in a few lines (Walther's phase-retrieval ambiguity: a
compactly supported function is fixed by `|ĝ|` on `ℝ` only up to flipping zeros). The translation
continuity it needs (`tendsto_normSq_shift`, `continuous_autocorr`) moves here from Mollify.lean.
-/

open Real Filter Topology Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Pilot1ca

/-! ## Elementary `L²` and energy inequalities -/

theorem normSq_add_le {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    normSq (fun t => g t + h t) ≤ 2 * normSq g + 2 * normSq h := by
  unfold normSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.integrable_sq.const_mul _) (hh.integrable_sq.const_mul _)]
  exact integral_mono (hg.add hh).integrable_sq
    ((hg.integrable_sq.const_mul _).add (hh.integrable_sq.const_mul _))
    fun t => by nlinarith [sq_nonneg (g t - h t)]

theorem normSq_sub_le {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    normSq (fun t => g t - h t) ≤ 2 * normSq g + 2 * normSq h := by
  have := normSq_add_le hg (hh.neg)
  simpa [sub_eq_add_neg, normSq] using this

theorem normSq_add3_le {g h k : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hk : MemLp k 2 volume) :
    normSq (fun t => g t + h t + k t) ≤ 4 * normSq g + 4 * normSq h + 4 * normSq k := by
  have h1 := normSq_add_le (hg.add hh) hk
  have h2 := normSq_add_le hg hh
  have h3 := normSq_nonneg k
  have e : normSq (fun t => g t + h t + k t) = normSq (fun t => (g + h) t + k t) := rfl
  have e2 : normSq (g + h) = normSq (fun t => g t + h t) := rfl
  rw [e]; rw [e2] at h1; linarith

theorem archIntegrand_add_le {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    {u : ℝ} (hu : 0 < u) :
    archIntegrand (fun t => g t + h t) u ≤ 2 * archIntegrand g u + 2 * archIntegrand h u := by
  rw [archIntegrand_eq (g := fun t => g t + h t) (hg.add hh), archIntegrand_eq hg, archIntegrand_eq hh]
  have hk := (kerK_pos hu).le
  have e : (fun t => (g t + h t) - (g (t + u) + h (t + u)))
      = fun t => (g t - g (t + u)) + (h t - h (t + u)) := by funext t; ring
  have m1 : MemLp (fun t => g t - g (t + u)) 2 volume := hg.sub (memLp_shift hg u)
  have m2 : MemLp (fun t => h t - h (t + u)) 2 volume := hh.sub (memLp_shift hh u)
  have := normSq_add_le m1 m2
  simp only [e]
  nlinarith [mul_le_mul_of_nonneg_right this hk]

/-! ## Approximation by continuous compactly supported functions -/

theorem exists_cc_approx {g : ℝ → ℝ} (hg : MemLp g 2 volume) {η : ℝ} (hη : 0 < η) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ MemLp φ 2 volume ∧
      normSq (fun t => g t - φ t) ≤ η := by
  have h2 : MemLp g (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hg
  obtain ⟨φ, hs, hle, hc, hm⟩ := h2.exists_hasCompactSupport_integral_rpow_sub_le (by norm_num) hη
  refine ⟨φ, hc, hs, hc.memLp_of_hasCompactSupport hs, ?_⟩
  unfold normSq
  convert hle using 1
  congr 1; funext x
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_two, sq_abs]

/-- Data for a continuous compactly supported function: a support radius and a modulus of
continuity. -/
theorem cc_data {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    (∃ R, 0 < R ∧ ∀ x, R < |x| → φ x = 0) ∧
      ∀ ε > 0, ∃ ρ > 0, ∀ x y, |x - y| < ρ → |φ x - φ y| < ε := by
  refine ⟨?_, fun ε hε => ?_⟩
  · obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    refine ⟨max R 1, by positivity, fun x hx => ?_⟩
    by_contra hne
    have hx' : x ∈ tsupport φ := subset_tsupport _ hne
    have := hR hx'
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_max_left R 1]
  · have hu := hs.uniformContinuous_of_continuous hc
    obtain ⟨ρ, hρ, h⟩ := Metric.uniformContinuous_iff.1 hu ε hε
    exact ⟨ρ, hρ, fun x y hxy => by
      have := h (show dist x y < ρ by rw [Real.dist_eq]; exact hxy)
      rwa [Real.dist_eq] at this⟩

/-- A square-integrable function whose square is bounded by `c` on `[−S, S]` and vanishes outside. -/
theorem normSq_le_box {F : ℝ → ℝ} (hF : MemLp F 2 volume) {S c : ℝ} (hS : 0 ≤ S)
    (hb : ∀ t, F t ^ 2 ≤ (Icc (-S) S).indicator (fun _ => c) t) : normSq F ≤ c * (2 * S) := by
  have hbd : Integrable ((Icc (-S) S).indicator fun _ : ℝ => c) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have := integral_mono hF.integrable_sq hbd hb
  rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at this
  unfold normSq; linarith

theorem normSq_neg_sub (g h : ℝ → ℝ) : normSq (fun t => h t - g t) = normSq (fun t => g t - h t) := by
  unfold normSq; congr 1; funext t; ring

/-! ## Translation is continuous in `L²` -/

theorem tendsto_normSq_shift {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun s => normSq (fun t => g (t + s) - g t)) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, hc, hs, hφ, happ⟩ := exists_cc_approx hg (show 0 < ε / 24 by positivity)
  obtain ⟨⟨R, hR, hsupp⟩, huc⟩ := cc_data hc hs
  set ε' := min 1 (ε / (48 * (R + 1)))
  have hε' : 0 < ε' := lt_min one_pos (by positivity)
  obtain ⟨ρ, hρ, hmod⟩ := huc ε' hε'
  have hball : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < min ρ 1 := by
    have := Metric.ball_mem_nhds (0 : ℝ) (lt_min hρ one_pos)
    filter_upwards [this] with s hs
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  filter_upwards [hball] with s hs
  have hs1 : |s| < 1 := lt_of_lt_of_le hs (min_le_right _ _)
  have hsρ : |s| < ρ := lt_of_lt_of_le hs (min_le_left _ _)
  -- the continuous part
  have hφs : normSq (fun t => φ (t + s) - φ t) ≤ ε' * (2 * (R + 1)) := by
    refine normSq_le_box (F := fun t => φ (t + s) - φ t) ((memLp_shift hφ s).sub hφ) (by linarith) fun t => ?_
    by_cases ht : t ∈ Icc (-(R + 1)) (R + 1)
    · rw [indicator_of_mem ht]
      have h1 := hmod (t + s) t (by rw [add_sub_cancel_left]; exact hsρ)
      have h2 : |φ (t + s) - φ t| ^ 2 ≤ ε' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1.le 2
      have h3 : ε' ^ 2 ≤ ε' := by nlinarith [min_le_left 1 (ε / (48 * (R + 1)))]
      rw [sq_abs] at h2; linarith
    · rw [indicator_of_notMem ht]
      have h1 : R + 1 < |t| := by
        by_contra hc'; push Not at hc'; exact ht (abs_le.1 hc')
      have h2 : R < |t + s| := by
        have := abs_add_le (t + s) (-s)
        rw [add_neg_cancel_right, abs_neg] at this; linarith
      rw [hsupp t (by linarith), hsupp _ h2]; simp
  -- split `τg − g = τ(g − φ) + (τφ − φ) + (φ − g)`
  have hm1 : MemLp (fun t => g (t + s) - φ (t + s)) 2 volume :=
    (memLp_shift hg s).sub (memLp_shift hφ s)
  have hm2 : MemLp (fun t => φ (t + s) - φ t) 2 volume := (memLp_shift hφ s).sub hφ
  have hm3 : MemLp (fun t => φ t - g t) 2 volume := hφ.sub hg
  have hsplit := normSq_add3_le hm1 hm2 hm3
  have e : (fun t => (g (t + s) - φ (t + s)) + (φ (t + s) - φ t) + (φ t - g t))
      = fun t => g (t + s) - g t := by funext t; ring
  rw [e] at hsplit
  have e1 : normSq (fun t => g (t + s) - φ (t + s)) = normSq (fun t => g t - φ t) :=
    normSq_shift (fun t => g t - φ t) s
  rw [e1, normSq_neg_sub g φ] at hsplit
  have hR' : ε' * (2 * (R + 1)) ≤ ε / 24 := by
    have := min_le_right 1 (ε / (48 * (R + 1)))
    calc ε' * (2 * (R + 1)) ≤ ε / (48 * (R + 1)) * (2 * (R + 1)) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = ε / 24 := by field_simp; ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)]
  linarith

theorem abs_integral_mul_le {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    {c : ℝ} (hc : 0 < c) : |∫ t, φ t * ψ t| ≤ (c * normSq φ + normSq ψ / c) / 2 := by
  have hI : Integrable (fun t => φ t * ψ t) := hφ.integrable_mul hψ
  refine (abs_integral_le_integral_abs).trans ?_
  have hb : Integrable (fun t => (c * φ t ^ 2 + ψ t ^ 2 / c) / 2) :=
    (((hφ.integrable_sq.const_mul c).add (hψ.integrable_sq.div_const c)).div_const 2)
  have := integral_mono hI.abs hb fun t => by
    have h0 : 0 ≤ (c * |φ t| - |ψ t|) ^ 2 := sq_nonneg _
    have e : |φ t * ψ t| = |φ t| * |ψ t| := abs_mul _ _
    rw [e, ← sq_abs (φ t), ← sq_abs (ψ t)]
    have : (c * |φ t| ^ 2 + |ψ t| ^ 2 / c) / 2 - |φ t| * |ψ t| = (c * |φ t| - |ψ t|) ^ 2 / (2 * c) := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (c * |φ t| - |ψ t|)) (by positivity : (0 : ℝ) ≤ 2 * c)]
  refine this.trans (le_of_eq ?_)
  rw [integral_div, integral_add (hφ.integrable_sq.const_mul c) (hψ.integrable_sq.div_const c),
    integral_const_mul, integral_div]
  rfl
/-- **The autocorrelation of an `L²` function is continuous** (translation is continuous in `L²`). -/
theorem continuous_autocorr {g : ℝ → ℝ} (hg : MemLp g 2 volume) : Continuous (autocorr g) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  set N := normSq g
  have hN := normSq_nonneg g
  set c := ε / (N + 1)
  have hc : 0 < c := by positivity
  have h := Metric.tendsto_nhds.1 (tendsto_normSq_shift hg) (ε * c) (by positivity)
  have h' : ∀ᶠ v in 𝓝 v₀, normSq (fun t => g (t + (v - v₀)) - g t) < ε * c := by
    have hc' : Tendsto (fun v => v - v₀) (𝓝 v₀) (𝓝 0) := by
      have := (continuous_id.sub continuous_const).tendsto v₀ (f := fun v : ℝ => v - v₀)
      simpa using this
    filter_upwards [hc'.eventually h] with v hv
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)] at hv
  filter_upwards [h'] with v hv
  rw [Real.dist_eq]
  have hψ : MemLp (fun t => g (t + v) - g (t + v₀)) 2 volume :=
    (memLp_shift hg v).sub (memLp_shift hg v₀)
  have e : autocorr g v - autocorr g v₀ = ∫ t, g t * (g (t + v) - g (t + v₀)) := by
    unfold autocorr
    rw [← integral_sub (integrable_mul_shift hg v) (integrable_mul_shift hg v₀)]
    congr 1; funext t; ring
  have eD : normSq (fun t => g (t + v) - g (t + v₀)) = normSq (fun t => g (t + (v - v₀)) - g t) := by
    have := normSq_shift (fun t => g (t + (v - v₀)) - g t) v₀
    rw [← this]; congr 1; funext t; ring_nf
  have hb := abs_integral_mul_le hg hψ hc
  rw [← e, eD] at hb
  have h1 : c * N < ε / 2 * 2 := by
    have : c * N = ε * (N / (N + 1)) := by simp only [c]; field_simp
    rw [this]
    have : N / (N + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have h2 : normSq (fun t => g (t + (v - v₀)) - g t) / c < ε := by
    rw [div_lt_iff₀ hc]; linarith
  linarith

/-! ## The transform of an even real function is real on the real line -/

/-- `ĝ(z̄) = conj ĝ(z)` for a real even `g`. -/
theorem ghatC_conj {f : ℝ → ℝ} (heven : ∀ u, f (-u) = f u) {a : ℝ}
    (ha : 0 ≤ a) (z : ℂ) : ghatC f a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (ghatC f a z) := by
  have : (starRingEnd ℂ) (ghatC f a z) = ghatC f a (-((starRingEnd ℂ) z)) := by
    unfold ghatC
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
      ← integral_conj]
    congr 1; funext u
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    congr 2; ring
  rw [this, ghatC_even heven]

theorem ghatC_im_zero {f : ℝ → ℝ} (heven : ∀ u, f (-u) = f u) {a : ℝ}
    (ha : 0 ≤ a) (t : ℝ) : (ghatC f a t).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← ghatC_conj heven ha, Complex.conj_ofReal]

/-! ## Even, supported, square-integrable functions -/

/-- `g` is even, square-integrable and vanishes outside `[−a, a]`: a probe without the archimedean
hypothesis. -/
structure ESupp (a : ℝ) (g : ℝ → ℝ) : Prop where
  even : ∀ u, g (-u) = g u
  supp : ∀ u, a < |u| → g u = 0
  memL2 : MemLp g 2 volume

theorem Probe.toE {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) : ESupp a g := ⟨hp.even, hp.supp, hp.memL2⟩

theorem ESupp.integrable {a : ℝ} {g : ℝ → ℝ} (hp : ESupp a g) : Integrable g := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc (-a) a)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have h1 : IntegrableOn g (Icc (-a) a) := (hp.memL2.restrict _).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 h1
  rw [Function.mem_support] at hu
  have : |u| ≤ a := by
    by_contra h; push Not at h; exact hu (hp.supp u h)
  exact abs_le.1 this

/-! ## A1. The transform on the real line, and the convolution identity -/

variable {a : ℝ} {g : ℝ → ℝ}

/-- `ĝ(r)` for real `r`, as a real number (it is real for even `g`). -/
def gH (g : ℝ → ℝ) (a r : ℝ) : ℝ := (ghatC g a r).re

theorem ghatC_real (hp : ESupp a g) (ha : 0 ≤ a) (r : ℝ) : ghatC g a r = (gH g a r : ℂ) := by
  apply Complex.ext
  · simp [gH]
  · simp [ghatC_im_zero hp.even ha r]

theorem gH_neg (hp : ESupp a g) (r : ℝ) : gH g a (-r) = gH g a r := by
  unfold gH; rw [Complex.ofReal_neg, ghatC_even hp.even a]

theorem continuous_gH (hp : ESupp a g) : Continuous (gH g a) :=
  Complex.continuous_re.comp
    ((ghatC_differentiable (hp.integrable).intervalIntegrable).continuous.comp
      Complex.continuous_ofReal)

/-- `|ĝ(r)| ≤ ‖g‖₁` on the real line. -/
theorem abs_gH_le (hp : ESupp a g) (ha : 0 < a) (r : ℝ) : |gH g a r| ≤ ∫ u, |g u| := by
  have h1 : |gH g a r| ≤ ‖ghatC g a r‖ := Complex.abs_re_le_norm _
  refine h1.trans ?_
  rw [ghatC_eq_integral ha hp.supp]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have : (Complex.I * (r : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]

/-- For even `g`, `f(x) = ∫ g(t)g(x − t) dt`: the autocorrelation is a convolution. -/
theorem autocorr_eq_conv (heven : ∀ u, g (-u) = g u) (x : ℝ) :
    autocorr g x = ∫ t, g t * g (x - t) := by
  unfold autocorr
  rw [← integral_neg_eq_self (fun t => g t * g (t + x))]
  congr 1; funext t
  rw [heven, show -t + x = x - t by ring]

/-- **The convolution identity**: `∫ f(x) e^{irx} dx = ĝ(r)²`. -/
theorem fourier_autocorr (hp : ESupp a g) (ha : 0 < a) (r : ℝ) :
    ∫ x, (autocorr g x : ℂ) * Complex.exp (Complex.I * r * x) = ghatC g a r ^ 2 := by
  have hg := hp.integrable
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * r * x) with he
  have he1 : ∀ x, ‖e x‖ = 1 := fun x => by
    simp only [he, Complex.norm_exp]
    have : (Complex.I * (r : ℂ) * (x : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have h0 := hg.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg (μ := volume) (ν := volume)
  simp only [ContinuousLinearMap.mul_apply'] at h0
  have hF : Integrable (Function.uncurry fun x t : ℝ => ((g t * g (x - t) : ℝ) : ℂ) * e x)
      (volume.prod volume) := by
    refine Integrable.mono' h0.norm
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable h0.aestronglyMeasurable).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ => e p.1).aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun p => ?_
    show ‖((g p.2 * g (p.1 - p.2) : ℝ) : ℂ) * e p.1‖ ≤ _
    rw [norm_mul, he1, mul_one, Complex.norm_real]
  have hinner : ∀ t, ∫ x, ((g t * g (x - t) : ℝ) : ℂ) * e x = ((g t : ℂ) * e t) * ghatC g a r := by
    intro t
    have e1 : (fun x => ((g t * g (x - t) : ℝ) : ℂ) * e x)
        = fun x => ((g t : ℂ) * e t) * (fun y => ((g y : ℝ) : ℂ) * e y) (x - t) := by
      funext x
      simp only [he]
      rw [show Complex.I * (r : ℂ) * (x : ℂ) = Complex.I * r * t + Complex.I * r * ((x - t : ℝ) : ℂ) by
        push_cast; ring, Complex.exp_add]
      push_cast; ring
    rw [e1, integral_const_mul, integral_sub_right_eq_self (fun y => ((g y : ℝ) : ℂ) * e y) t,
      ghatC_eq_integral ha hp.supp]
  calc ∫ x, (autocorr g x : ℂ) * e x
      = ∫ x, ∫ t, ((g t * g (x - t) : ℝ) : ℂ) * e x := by
        congr 1; funext x
        rw [autocorr_eq_conv hp.even, ← integral_complex_ofReal, ← integral_mul_const]
    _ = ∫ t, ∫ x, ((g t * g (x - t) : ℝ) : ℂ) * e x := integral_integral_swap hF
    _ = ∫ t, ((g t : ℂ) * e t) * ghatC g a r := by congr 1; funext t; exact hinner t
    _ = ghatC g a r ^ 2 := by
        rw [integral_mul_const, ← ghatC_eq_integral ha hp.supp, sq]

/-! ## A2. The autocorrelation in Mathlib's Fourier normalisation -/

theorem integrable_autocorr (hp : ESupp a g) (ha : 0 < a) : Integrable (autocorr g) := by
  refine (continuous_autocorr hp.memL2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun u hu => ?_
  apply autocorr_eq_zero hp.supp
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

/-- `ĝ(2πξ)²`: Mathlib's Fourier transform of `f`. -/
def PhiH (g : ℝ → ℝ) (a ξ : ℝ) : ℝ := gH g a (2 * π * ξ) ^ 2

theorem fourier_autocorr_eq (hp : ESupp a g) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (autocorr g x : ℂ)) ξ = (PhiH g a ξ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • (autocorr g v : ℂ))
      = fun v => (autocorr g v : ℂ) * Complex.exp (Complex.I * ((-(2 * π * ξ) : ℝ) : ℂ) * v) := by
    funext v; rw [smul_eq_mul, mul_comm]; congr 2; push_cast; ring
  rw [e, fourier_autocorr hp ha, ghatC_real hp ha.le, gH_neg hp, PhiH]; push_cast; rfl

/-! ## A3. `∫ĝ² < ∞`, by Gaussian regularisation -/

/-- `∫ e^{−x²/c} ĝ(2πx)² dx → f(0)` as `c → ∞`. -/
theorem tendsto_gauss_PhiH (hp : ESupp a g) (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x) atTop (𝓝 (autocorr g 0)) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hT := Real.tendsto_integral_gaussian_smul' hFi (v := (0 : ℝ)) hFc.continuousAt
  have key : ∀ c : ℝ, 0 < c →
      (∫ w : ℝ, ((π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ)
          * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2)) • F w)
        = ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x : ℝ) : ℂ) := by
    intro c hc
    have hb : 0 < ((c : ℂ)⁻¹).re := by simp; positivity
    have hJ : Integrable (fun w : ℝ => cexp (-((c : ℂ))⁻¹ * ‖w‖ ^ 2)) := by
      simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℝ) hb 0 0
    have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hJ hFi
    simp only [flip_innerₗ] at hflip
    change ∫ ξ, 𝓕 (fun w : ℝ => cexp (-((c : ℂ))⁻¹ * ‖w‖ ^ 2)) ξ • F ξ
      = ∫ x, cexp (-((c : ℂ))⁻¹ * ‖x‖ ^ 2) • 𝓕 F x at hflip
    simp_rw [fourier_gaussian_innerProductSpace (V := ℝ) hb] at hflip
    have e1 : (fun w : ℝ => ((π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ)
          * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2)) • F w)
        = fun ξ : ℝ => (((π : ℂ) / ((c : ℂ))⁻¹) ^ ((Module.finrank ℝ ℝ : ℂ) / 2)
          * cexp (-(π : ℂ) ^ 2 * ‖ξ‖ ^ 2 / ((c : ℂ))⁻¹)) • F ξ := by
      funext w
      rw [div_inv_eq_mul, zero_sub, norm_neg, div_inv_eq_mul]
      congr 3; ring
    rw [e1, hflip, ← integral_complex_ofReal]
    congr 1; funext x
    have hx : 𝓕 F x = (PhiH g a x : ℂ) := fourier_autocorr_eq hp ha x
    have hx2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.norm_eq_abs, sq_abs, Complex.ofReal_pow]
    rw [hx, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, hx2]
    push_cast; ring_nf
  have hT' : Tendsto (fun c : ℝ => ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x : ℝ) : ℂ)) atTop
      (𝓝 (F 0)) :=
    hT.congr' ((eventually_gt_atTop 0).mono fun c hc => key c hc)
  have := (Complex.continuous_re.tendsto _).comp hT'
  simpa [hF, Function.comp_def] using this

theorem PhiH_nonneg (x : ℝ) : 0 ≤ PhiH g a x := sq_nonneg _

theorem continuous_PhiH (hp : ESupp a g) : Continuous (PhiH g a) :=
  ((continuous_gH hp).comp (continuous_const.mul continuous_id)).pow 2

theorem PhiH_le (hp : ESupp a g) (ha : 0 < a) (x : ℝ) : PhiH g a x ≤ (∫ u, |g u|) ^ 2 := by
  unfold PhiH
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_gH_le hp ha _) 2

/-- **`ĝ(2π·)²` is integrable**: monotone convergence along the Gaussian regularisation. -/
theorem integrable_PhiH (hp : ESupp a g) (ha : 0 < a) : Integrable (PhiH g a) := by
  set C := (∫ u, |g u|) ^ 2
  have hk : ∀ n : ℕ, Integrable (fun x => Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiH g a x) := by
    intro n
    refine (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)).mul_bdd
      (continuous_PhiH hp).aestronglyMeasurable (c := C) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (PhiH_nonneg x)]; exact PhiH_le hp ha x
  have hkn : ∀ n : ℕ, ∀ x, 0 ≤ Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiH g a x :=
    fun n x => mul_nonneg (Real.exp_pos _).le (PhiH_nonneg x)
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiH g a x)) atTop (𝓝 (∫⁻ x, ENNReal.ofReal (PhiH g a x))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul
        (continuous_PhiH hp)).measurable.ennreal_ofReal.aemeasurable
    · refine Eventually.of_forall fun x => fun m n hmn => ENNReal.ofReal_le_ofReal ?_
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (PhiH_nonneg x)
      have h1 : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      nlinarith [sq_nonneg x]
    · refine Eventually.of_forall fun x => ENNReal.tendsto_ofReal ?_
      have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
      have h1 : Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹ * x ^ 2) atTop (𝓝 0) := by
        simpa using h0.neg.mul_const (x ^ 2)
      have := ((Real.continuous_exp.tendsto 0).comp h1).mul_const (PhiH g a x)
      simpa using this
  have hval : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiH g a x)) atTop (𝓝 (ENNReal.ofReal (autocorr g 0))) := by
    have hc : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := ENNReal.tendsto_ofReal ((tendsto_gauss_PhiH hp ha).comp hc)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact ofReal_integral_eq_lintegral_ofReal (hk n) (Eventually.of_forall (hkn n))
  have heq := tendsto_nhds_unique hlim hval
  refine ⟨(continuous_PhiH hp).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall PhiH_nonneg), heq]
  exact ENNReal.ofReal_lt_top

/-! ## A4. Fourier inversion: `g_h = f` for `h = ĝ²` -/

/-- `h(r) = ĝ(r)²` on the real line. -/
def hsq (g : ℝ → ℝ) (a r : ℝ) : ℝ := gH g a r ^ 2

theorem hsq_nonneg (r : ℝ) : 0 ≤ hsq g a r := sq_nonneg _

theorem integrable_hsq (hp : ESupp a g) (ha : 0 < a) : Integrable (hsq g a) :=
  (integrable_comp_mul_left_iff (hsq g a) (by positivity : (2 * π : ℝ) ≠ 0)).1 (integrable_PhiH hp ha)

/-- **Fourier inversion for `f`**: `f(u) = ∫ ĝ(2πv)² cos(2πvu) dv`. -/
theorem autocorr_eq_inv (hp : ESupp a g) (ha : 0 < a) (u : ℝ) :
    autocorr g u = ∫ v, PhiH g a v * Real.cos (2 * π * v * u) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hFF : 𝓕 F = fun ξ => (PhiH g a ξ : ℂ) := funext (fourier_autocorr_eq hp ha)
  have hFFi : Integrable (𝓕 F) := by rw [hFF]; exact (integrable_PhiH hp ha).ofReal
  have h := congrFun (Continuous.fourierInv_fourier_eq hFc hFi hFFi) u
  rw [Real.fourierInv_eq', hFF] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  have hI : Integrable (fun v : ℝ => cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)) := by
    refine (integrable_PhiH hp ha).ofReal.bdd_mul (c := 1)
      (by fun_prop : Continuous fun v : ℝ => cexp (↑(2 * π * (u * v)) * I)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hre := congrArg Complex.re h
  have hre2 : (∫ v : ℝ, cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)).re
      = ∫ v : ℝ, (cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)).re := (integral_re hI).symm
  rw [hre2] at hre
  simp only [hF, Complex.ofReal_re] at hre
  rw [← hre]
  congr 1; funext v
  rw [smul_eq_mul, mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    show 2 * π * (u * v) = 2 * π * v * u by ring]

/-- **`g_h = f`**: `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`. -/
theorem gh_hsq (hp : ESupp a g) (ha : 0 < a) (u : ℝ) : gh (hsq g a) u = autocorr g u := by
  rw [autocorr_eq_inv hp ha u, gh]
  have e := Measure.integral_comp_mul_left (fun r => hsq g a r * Real.cos (r * u)) (2 * π)
  have e2 : (fun v => PhiH g a v * Real.cos (2 * π * v * u))
      = fun v => hsq g a (2 * π * v) * Real.cos (2 * π * v * u) := rfl
  rw [e2, e, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul, one_div]

/-- `∫ĝ² = 2πf(0) = 2π‖g‖²`. -/
theorem integral_hsq (hp : ESupp a g) (ha : 0 < a) : ∫ r, hsq g a r = 2 * π * normSq g := by
  have h := gh_hsq hp ha 0
  rw [gh, autocorr_zero] at h
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  field_simp at h ⊢
  linarith

theorem continuous_hsq (hp : ESupp a g) : Continuous (hsq g a) := (continuous_gH hp).pow 2

theorem integral_hsq_cos (hp : ESupp a g) (ha : 0 < a) (u : ℝ) :
    ∫ r, hsq g a r * Real.cos (r * u) = 2 * π * autocorr g u := by
  have h := gh_hsq hp ha u
  rw [gh, one_div, inv_mul_eq_iff_eq_mul₀ (by positivity)] at h
  exact h

theorem integrable_hsq_cos (hp : ESupp a g) (ha : 0 < a) (u : ℝ) :
    Integrable (fun r => hsq g a r * Real.cos (r * u)) :=
  (integrable_hsq hp ha).mul_bdd (c := 1) (by fun_prop : Continuous fun r : ℝ =>
    Real.cos (r * u)).aestronglyMeasurable
    (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

end Pilot1ca

#print axioms Pilot1ca.tendsto_normSq_shift
#print axioms Pilot1ca.continuous_autocorr
#print axioms Pilot1ca.ghatC_conj
#print axioms Pilot1ca.ghatC_im_zero
#print axioms Pilot1ca.fourier_autocorr
#print axioms Pilot1ca.integrable_hsq
#print axioms Pilot1ca.gh_hsq
#print axioms Pilot1ca.integral_hsq
#print axioms Pilot1ca.integral_hsq_cos
