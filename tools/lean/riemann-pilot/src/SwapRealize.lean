import Mathlib
import HurwitzCross

/-! # The swap realisation, proved

`SwapRealization` (ZeroSwap.lean) was the named Paley–Wiener input of the zero-swap lemma. It holds
for every probe, with no appeal to Paley–Wiener, because the swapped function can be written down.

Let `ĝ(w) = 0` with `σ = w²` non-real. `g` is even, so `ĝ(−w) = 0` as well. Put

  `h(x) = ∫_{−a}^{x} sin(w(x − y))/w · g(y) dy`   (the causal Green solution of `h'' + σh = g`),

written as `(e^{iwx} P_{−w}(x) − e^{−iwx} P_w(x))/(2iw)` with `P_c(x) = ∫_{−a}^{x} g(y) e^{icy} dy`.

* `h` is continuous; `P_{±w}(x) = ĝ(±w) = 0` for `x ≥ a`, so `h` vanishes right of `a`; and
  `P_{−c}(−x) = ĝ(c) − P_c(x)` makes `h` even, so it vanishes left of `−a` too (`hSw_supp`).
* A triangle Fubini swap and `∫_y^a e^{i(z+c)x} dx` give `ĥ(z) = −ĝ(z)/(z² − σ)` (`hSw_hat`).
* `f₂ = g + (σ̄ − σ)h`, `u = Re f₂`, `v = Im f₂`: then `û + iv̂ = ĝ(z)(z² − σ̄)/(z² − σ)` (**R1**,
  `swap_hat`).
* **R2** (`swap_autocorr`): on `[−6a, 6a]` the Fourier coefficients of `u, v, g` are `ĝ`-values at
  real points, where `ĝ_u, ĝ_v` are real (even real functions) and the multiplier is unimodular. So
  `|c_n(u)|² + |c_n(v)|² = |c_n(g)|²`, and Parseval for `g − g(· + s)` (`hasSum_shift'`) gives
  `A_u(s) + A_v(s) = A_g(s)` for `|s| < 3a`; beyond `2a` all three vanish.
* The archimedean integrals of `u, v` converge by domination, `0 ≤ E_u(x) ≤ E_g(x)` (`arch_dom`).

`swapRealization_of_zero` assembles this. `rh_of_eventually_simple` is the RH chain of
HurwitzCross.lean with the swap input discharged.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- **Triangle swap.** `∫_α^β e(x) ∫_α^x f(y) dy dx = ∫_α^β f(y) ∫_y^β e(x) dx dy`. -/
theorem triangle_swap {α β : ℝ} (hαβ : α ≤ β) {e f : ℝ → ℂ} (he : Continuous e)
    (hf : IntegrableOn f (Ioc α β)) :
    (∫ x in α..β, e x * ∫ y in α..x, f y) = ∫ y in α..β, f y * ∫ x in y..β, e x := by
  set μ := volume.restrict (Ioc α β)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 (by simp)
  set F : ℝ → ℝ → ℂ := fun x y => e x * (Iic x).indicator f y with hF
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn
    he.continuousOn
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hbd : Integrable (fun p : ℝ × ℝ => (fun _ : ℝ => C) p.1 * (fun y => ‖f y‖) p.2)
        (μ.prod μ) := (integrable_const C).mul_prod hf.norm
    refine hbd.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => e p.1) (μ.prod μ) :=
        (he.comp continuous_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable
          ({q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q : ℝ × ℝ => f q.2)) (μ.prod μ) :=
        (hf.aestronglyMeasurable.comp_snd).indicator (measurableSet_le measurable_snd measurable_fst)
      refine (h1.mul h2).congr (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, hF, Set.indicator, Set.mem_Iic, Pi.mul_apply, Set.mem_ofPred_eq]
    · have hmem : ∀ᵐ p ∂(μ.prod μ), p.1 ∈ Ioc α β :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      simp only [Function.uncurry, hF, norm_mul]
      refine mul_le_mul (hC p.1 (Ioc_subset_Icc_self hp)) ?_ (norm_nonneg _)
        ((norm_nonneg _).trans (hC p.1 (Ioc_subset_Icc_self hp)))
      by_cases h : p.2 ≤ p.1
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
  have hswap := integral_integral_swap hint
  rw [intervalIntegral.integral_of_le hαβ, intervalIntegral.integral_of_le hαβ]
  have hL : ∀ x ∈ Ioc α β, e x * (∫ y in α..x, f y) = ∫ y, F x y ∂μ := by
    intro x hx
    rw [integral_const_mul, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
      min_eq_right hx.2, intervalIntegral.integral_of_le hx.1.le]
  have hR : ∀ y ∈ Ioc α β, f y * (∫ x in y..β, e x) = ∫ x, F x y ∂μ := by
    intro y hy
    have hset : Ioc α β ∩ Ici y = Icc y β := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hy.1 h1, h2⟩, h1⟩
    have : ∫ x, F x y ∂μ = ∫ x in Ioc α β, f y * (Ici y).indicator e x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases h : y ≤ x
      · simp [hF, Set.indicator, h, mul_comm]
      · simp [hF, Set.indicator, h]
    rw [this, integral_const_mul, setIntegral_indicator measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hy.2]
  rw [setIntegral_congr_fun measurableSet_Ioc hL, setIntegral_congr_fun measurableSet_Ioc hR]
  exact hswap

/-! ## The primitives `P_c` and the Green solution `h` -/

theorem ii_mul_exp {g : ℝ → ℝ} (hg : MemLp g 2 volume) (c : ℂ) (α β : ℝ) :
    IntervalIntegrable (fun y : ℝ => ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * c * y)) volume α β := by
  have h := memLp_intervalIntegrable hg α β
  have h' : IntervalIntegrable (fun y : ℝ => ((g y : ℝ) : ℂ)) volume α β := ⟨h.1.ofReal, h.2.ofReal⟩
  exact h'.mul_continuousOn (by fun_prop)

/-- `P_c(x) = ∫_{−a}^{x} g(y) e^{icy} dy`; `P_c(a) = ĝ(c)`. -/
def Pc (g : ℝ → ℝ) (a : ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  ∫ y in (-a)..x, ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * c * y)

theorem Pc_continuous {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) (c : ℂ) :
    Continuous (Pc g a c) :=
  intervalIntegral.continuous_primitive (fun α β => ii_mul_exp hg c α β) (-a)

theorem Pc_neg {g : ℝ → ℝ} (hg : MemLp g 2 volume) (heven : ∀ u, g (-u) = g u) (a : ℝ) (c : ℂ)
    (x : ℝ) : Pc g a (-c) (-x) = ghatC g a c - Pc g a c x := by
  unfold Pc ghatC
  set H : ℝ → ℂ := fun y => ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * c * y) with hH
  have e : (fun y : ℝ => ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * (-c) * y)) = fun y => H (-y) := by
    funext y; simp only [hH, heven]; congr 2; push_cast; ring
  rw [e, intervalIntegral.integral_comp_neg, neg_neg, neg_neg,
    intervalIntegral.integral_interval_sub_left (ii_mul_exp hg c _ _) (ii_mul_exp hg c _ _)]

theorem ghatC_neg_of_even {g : ℝ → ℝ} (hg : MemLp g 2 volume) (heven : ∀ u, g (-u) = g u)
    (a : ℝ) (c : ℂ) : ghatC g a (-c) = ghatC g a c := by
  have h := Pc_neg hg heven a c (-a)
  rw [neg_neg] at h
  have h0 : Pc g a c (-a) = 0 := intervalIntegral.integral_same
  rw [h0, sub_zero] at h
  exact h

theorem Pc_of_ge {g : ℝ → ℝ} (hg : MemLp g 2 volume) {a : ℝ} (hsupp : ∀ u, a < |u| → g u = 0)
    (c : ℂ) {x : ℝ} (hx : a ≤ x) : Pc g a c x = ghatC g a c := by
  unfold Pc ghatC
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_mul_exp hg c (-a) a)
    (ii_mul_exp hg c a x)]
  have : (∫ y in a..x, ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * c * y)) = 0 := by
    refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun y hy => ?_)
    rw [uIoc_of_le hx] at hy
    rw [hsupp y (lt_of_lt_of_le hy.1 (le_abs_self y))]; simp
  rw [this, add_zero]

/-- The Green solution `h(x) = ∫_{−a}^{x} sin(w(x − y))/w · g(y) dy`, written through `P_{±w}`. -/
def hSw (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (Complex.I * w * x) * Pc g a (-w) x
    - Complex.exp (-(Complex.I * w * x)) * Pc g a w x) / (2 * Complex.I * w)

theorem hSw_continuous {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) (w : ℂ) :
    Continuous (hSw g a w) := by
  have h1 := Pc_continuous hg a (-w)
  have h2 := Pc_continuous hg a w
  unfold hSw
  fun_prop

theorem hSw_even {g : ℝ → ℝ} (hg : MemLp g 2 volume) (heven : ∀ u, g (-u) = g u) {a : ℝ}
    {w : ℂ} (hw : ghatC g a w = 0) (x : ℝ) : hSw g a w (-x) = hSw g a w x := by
  have hw' : ghatC g a (-w) = 0 := by rw [ghatC_neg_of_even hg heven]; exact hw
  unfold hSw
  have e1 := Pc_neg hg heven a w x
  have e2 := Pc_neg hg heven a (-w) x
  rw [neg_neg] at e2
  rw [e1, e2, hw, hw']
  have x1 : Complex.I * w * ((-x : ℝ) : ℂ) = -(Complex.I * w * x) := by push_cast; ring
  rw [x1, neg_neg]; ring

theorem hSw_supp {g : ℝ → ℝ} (hg : MemLp g 2 volume) (heven : ∀ u, g (-u) = g u) {a : ℝ}
    (hsupp : ∀ u, a < |u| → g u = 0) {w : ℂ} (hw : ghatC g a w = 0) (x : ℝ) (hx : a < |x|) :
    hSw g a w x = 0 := by
  have hw' : ghatC g a (-w) = 0 := by rw [ghatC_neg_of_even hg heven]; exact hw
  have hpos : ∀ y, a < y → hSw g a w y = 0 := by
    intro y hy
    unfold hSw
    rw [Pc_of_ge hg hsupp _ hy.le, Pc_of_ge hg hsupp _ hy.le, hw, hw']; simp
  rcases le_or_gt 0 x with h0 | h0
  · exact hpos x (by rwa [abs_of_nonneg h0] at hx)
  · rw [← hSw_even hg heven hw x]
    exact hpos (-x) (by rwa [abs_of_neg h0] at hx)

/-! ## The transform of `h`: `ĥ(z) = −ĝ(z)/(z² − w²)` -/

theorem hat_exp_Pc {g : ℝ → ℝ} (hg : MemLp g 2 volume) {a : ℝ} (ha : 0 ≤ a) (c z : ℂ)
    (hcz : z + c ≠ 0) :
    (∫ x in (-a)..a, Complex.exp (Complex.I * (z + c) * x) * Pc g a (-c) x)
      = (Complex.exp (Complex.I * (z + c) * a) * ghatC g a (-c) - ghatC g a z)
          / (Complex.I * (z + c)) := by
  have hne : Complex.I * (z + c) ≠ 0 := mul_ne_zero Complex.I_ne_zero hcz
  unfold Pc
  rw [triangle_swap (by linarith) (by fun_prop) (ii_mul_exp hg (-c) (-a) a).1]
  simp_rw [integral_exp_mul_complex hne]
  have hpt : ∀ y : ℝ, ((g y : ℝ) : ℂ) * Complex.exp (Complex.I * (-c) * y)
      * ((Complex.exp (Complex.I * (z + c) * a) - Complex.exp (Complex.I * (z + c) * y))
          / (Complex.I * (z + c)))
      = Complex.exp (Complex.I * (z + c) * a) / (Complex.I * (z + c))
          * (((g y : ℝ) : ℂ) * Complex.exp (Complex.I * (-c) * y))
        - 1 / (Complex.I * (z + c)) * (((g y : ℝ) : ℂ) * Complex.exp (Complex.I * z * y)) := by
    intro y
    have : Complex.exp (Complex.I * z * y)
        = Complex.exp (Complex.I * (-c) * y) * Complex.exp (Complex.I * (z + c) * y) := by
      rw [← Complex.exp_add]; ring_nf
    rw [this]; field_simp
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((ii_mul_exp hg _ _ _).const_mul _)
      ((ii_mul_exp hg _ _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold ghatC
  field_simp

theorem hSw_hat {g : ℝ → ℝ} (hg : MemLp g 2 volume) (heven : ∀ u, g (-u) = g u) {a : ℝ}
    (ha : 0 ≤ a) {w : ℂ} (hw : ghatC g a w = 0) (hw0 : w ≠ 0) {z : ℂ} (hz : z ^ 2 ≠ w ^ 2) :
    (∫ x in (-a)..a, hSw g a w x * Complex.exp (Complex.I * z * x))
      = -(ghatC g a z / (z ^ 2 - w ^ 2)) := by
  have hw' : ghatC g a (-w) = 0 := by rw [ghatC_neg_of_even hg heven]; exact hw
  have hp : z + w ≠ 0 := fun h => hz (by rw [eq_neg_of_add_eq_zero_left h]; ring)
  have hm : z + -w ≠ 0 := fun h => hz (by rw [← sub_eq_add_neg, sub_eq_zero] at h; rw [h])
  have hpt : ∀ x : ℝ, hSw g a w x * Complex.exp (Complex.I * z * x)
      = (Complex.exp (Complex.I * (z + w) * x) * Pc g a (-w) x
        - Complex.exp (Complex.I * (z + -w) * x) * Pc g a (-(-w)) x) / (2 * Complex.I * w) := by
    intro x
    unfold hSw
    rw [neg_neg]
    have e1 : Complex.exp (Complex.I * (z + w) * x)
        = Complex.exp (Complex.I * w * x) * Complex.exp (Complex.I * z * x) := by
      rw [← Complex.exp_add]; ring_nf
    have e2 : Complex.exp (Complex.I * (z + -w) * x)
        = Complex.exp (-(Complex.I * w * x)) * Complex.exp (Complex.I * z * x) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e1, e2]; ring
  simp_rw [hpt]
  have c1 := Pc_continuous hg a (-w)
  have c2 := Pc_continuous hg a (-(-w))
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    hat_exp_Pc hg ha w z hp, hat_exp_Pc hg ha (-w) z hm, hw', neg_neg, hw]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hq : z ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.2 hz
  have hq' : z ^ 2 - w ^ 2 = (z + w) * (z + -w) := by ring
  rw [hq']
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-! ## The swapped pair `u + iv = g + (σ̄ − σ) h` -/

/-- `f₂ = g + (σ̄ − σ)h` with `σ = w²`; its transform is `ĝ(z)(z² − σ̄)/(z² − σ)`. -/
def f2Sw (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  ((g x : ℝ) : ℂ) + ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x

def uSw (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℝ := (f2Sw g a w x).re
def vSw (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℝ := (f2Sw g a w x).im

theorem uSw_eq (g : ℝ → ℝ) (a : ℝ) (w : ℂ) :
    uSw g a w = fun x => g x + (((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x).re := by
  funext x; simp [uSw, f2Sw]

theorem vSw_eq (g : ℝ → ℝ) (a : ℝ) (w : ℂ) :
    vSw g a w = fun x => (((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x).im := by
  funext x; simp [vSw, f2Sw]

section Pair

variable {g : ℝ → ℝ} {a : ℝ} {w : ℂ}

theorem kSw_continuous (hg : MemLp g 2 volume) :
    Continuous fun x => ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x :=
  continuous_const.mul (hSw_continuous hg a w)

theorem kSw_supp (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) (hx : a < |x|) :
    ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x = 0 := by
  rw [hSw_supp hp.memL2 hp.even hp.supp hw x hx, mul_zero]

theorem hasCompactSupport_of_supp {k : ℝ → ℝ} (hk : ∀ x, a < |x| → k x = 0) :
    HasCompactSupport k := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx => hk x ?_
  by_contra h
  push Not at h
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem f2Sw_even (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) :
    f2Sw g a w (-x) = f2Sw g a w x := by
  unfold f2Sw; rw [hp.even, hSw_even hp.memL2 hp.even hw]

theorem f2Sw_supp (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) (hx : a < |x|) :
    f2Sw g a w x = 0 := by
  unfold f2Sw; rw [hp.supp x hx, kSw_supp hp hw x hx]; simp

theorem memLp_uSw (hp : Probe a g) (hw : ghatC g a w = 0) : MemLp (uSw g a w) 2 volume := by
  rw [uSw_eq]
  refine hp.memL2.add (Continuous.memLp_of_hasCompactSupport
    (Complex.continuous_re.comp (kSw_continuous hp.memL2)) (hasCompactSupport_of_supp (a := a) ?_))
  intro x hx; rw [kSw_supp hp hw x hx, Complex.zero_re]

theorem memLp_vSw (hp : Probe a g) (hw : ghatC g a w = 0) : MemLp (vSw g a w) 2 volume := by
  rw [vSw_eq]
  refine Continuous.memLp_of_hasCompactSupport
    (Complex.continuous_im.comp (kSw_continuous hp.memL2)) (hasCompactSupport_of_supp (a := a) ?_)
  intro x hx; rw [kSw_supp hp hw x hx, Complex.zero_im]

/-- **R1.** `û(z) + iv̂(z) = ĝ(z)(z² − σ̄)/(z² − σ)`. -/
theorem swap_hat (hp : Probe a g) (ha : 0 ≤ a) (hw : ghatC g a w = 0) (hw0 : w ≠ 0) (z : ℂ)
    (hz : z ^ 2 ≠ w ^ 2) :
    ghatC (uSw g a w) a z + Complex.I * ghatC (vSw g a w) a z
      = ghatC g a z * ((z ^ 2 - (starRingEnd ℂ) (w ^ 2)) / (z ^ 2 - w ^ 2)) := by
  have hu := ii_mul_exp (memLp_uSw hp hw) z (-a) a
  have hv := ii_mul_exp (memLp_vSw hp hw) z (-a) a
  have hH : IntervalIntegrable (fun x : ℝ => hSw g a w x * Complex.exp (Complex.I * z * x))
      volume (-a) a := by
    have := hSw_continuous hp.memL2 a w
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hsum : ghatC (uSw g a w) a z + Complex.I * ghatC (vSw g a w) a z
      = ∫ x in (-a)..a, f2Sw g a w x * Complex.exp (Complex.I * z * x) := by
    unfold ghatC
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hu (hv.const_mul _)]
    congr 1; funext x
    conv_rhs => rw [← Complex.re_add_im (f2Sw g a w x)]
    simp only [uSw, vSw]; ring
  have hsplit : (fun x : ℝ => f2Sw g a w x * Complex.exp (Complex.I * z * x))
      = fun x => ((g x : ℝ) : ℂ) * Complex.exp (Complex.I * z * x)
        + ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * (hSw g a w x * Complex.exp (Complex.I * z * x)) := by
    funext x; unfold f2Sw; ring
  rw [hsum, hsplit, intervalIntegral.integral_add (ii_mul_exp hp.memL2 z _ _) (hH.const_mul _),
    intervalIntegral.integral_const_mul, hSw_hat hp.memL2 hp.even ha hw hw0 hz]
  have hq : z ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.2 hz
  unfold ghatC
  field_simp
  ring

end Pair

/-! ## R2: the autocorrelations add up (Fourier coefficients on `[−6a, 6a]`) -/

theorem ghatC_im_zero {f : ℝ → ℝ} (hf : MemLp f 2 volume) (heven : ∀ u, f (-u) = f u) {a : ℝ}
    (ha : 0 ≤ a) (t : ℝ) : (ghatC f a t).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have : (starRingEnd ℂ) (ghatC f a t) = ghatC f a (-(t : ℂ)) := by
    unfold ghatC
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
      ← integral_conj]
    congr 1; funext u
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_ofReal]
    congr 2; ring
  rw [this, ghatC_neg_of_even hf heven]

theorem cf_eq_ghatC {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hsupp : ∀ u, a < |u| → f u = 0) (n : ℤ) :
    cf (3 * a) f n
      = (1 / (4 * (3 * a)) : ℂ) * ghatC f a ((-(2 * π * n / (4 * (3 * a))) : ℝ) : ℂ) := by
  have hs : ∀ u, a < |u| →
      Complex.exp (-(2 * π * I * n * u / (4 * (3 * a)))) * ((f u : ℝ) : ℂ) = 0 :=
    fun u hu => by rw [hsupp u hu]; simp
  unfold cf
  push_cast
  rw [integral_eq_of_supp hs (by linarith) (by linarith), ghatC_eq_integral ha hsupp]
  congr 1; congr 1; funext u; rw [mul_comm]; congr 2; ring

theorem norm_swapB {σ : ℂ} (hσ : σ.im ≠ 0) (t : ℝ) :
    ‖((t : ℂ) ^ 2 - (starRingEnd ℂ) σ) / ((t : ℂ) ^ 2 - σ)‖ = 1 := by
  have h : (t : ℂ) ^ 2 - (starRingEnd ℂ) σ = (starRingEnd ℂ) ((t : ℂ) ^ 2 - σ) := by
    simp [map_sub, map_pow, Complex.conj_ofReal]
  rw [h, norm_div, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.2 (sub_ne_zero.2 (sq_ne_of_im hσ t))

theorem norm_sq_add_of_im {x y : ℂ} (hx : x.im = 0) (hy : y.im = 0) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + Complex.I * y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, hx, hy]

/-- `hasSum_shift` needs only `L²` and the support. -/
theorem hasSum_shift' {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hsp : ∀ u, a < |u| → g u = 0) {s : ℝ} (hs : |s| < a) :
    HasSum (fun n : ℤ => ‖cf a g n‖ ^ 2 * (2 - 2 * Real.cos (2 * π * n * s / (4 * a))))
      ((4 * a)⁻¹ * (2 * (autocorr g 0 - autocorr g s))) := by
  have hgs : MemLp (fun t => g (t + s)) 2 volume :=
    hg.comp_measurePreserving (measurePreserving_add_right volume s)
  have hmem : MemLp (fun t => g t - g (t + s)) 2 volume := hg.sub hgs
  have hsupp : ∀ u, a + |s| < |u| → g u - g (u + s) = 0 := by
    intro u hu
    have h1 : a < |u| := by linarith [abs_nonneg s]
    have h2 : a < |u + s| := by
      have : |u| ≤ |u + s| + |s| := by
        have := abs_sub (u + s) s
        rwa [add_sub_cancel_right] at this
      linarith
    rw [hsp u h1, hsp _ h2, sub_self]
  have hP := hasSum_cf_sq ha (by linarith) hmem hsupp
  rw [normSq_sub_shift hg s] at hP
  convert hP using 1
  funext n
  have hlin : cf a (fun t => g t - g (t + s)) n
      = cf a g n * (1 - Complex.exp (((2 * π * n * s / (4 * a) : ℝ) : ℂ) * I)) := by
    rw [cf_sub (memLp_intervalIntegrable hg _ _) (memLp_intervalIntegrable hgs _ _),
      cf_shift ha hsp hs n]
    have : Complex.exp (2 * π * I * n * s / (4 * a))
        = Complex.exp (((2 * π * n * s / (4 * a) : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    rw [this]; ring
  rw [hlin, norm_mul, mul_pow, norm_one_sub_exp_sq]

theorem autocorr_eq_zero_far {a : ℝ} {f : ℝ → ℝ} (hsupp : ∀ u, a < |u| → f u = 0) {s : ℝ}
    (hs : 2 * a < |s|) : autocorr f s = 0 := by
  unfold autocorr
  have : (fun t => f t * f (t + s)) = fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : a < |t|
    · rw [hsupp t ht, zero_mul]
    · push Not at ht
      have : a < |t + s| := by
        have := abs_sub (t + s) t
        rw [add_sub_cancel_left] at this
        linarith
      rw [hsupp _ this, mul_zero]
  rw [this, integral_zero]

section Pair2

variable {g : ℝ → ℝ} {a : ℝ} {w : ℂ}

theorem uSw_even (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) :
    uSw g a w (-x) = uSw g a w x := by simp only [uSw, f2Sw_even hp hw]

theorem vSw_even (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) :
    vSw g a w (-x) = vSw g a w x := by simp only [vSw, f2Sw_even hp hw]

theorem uSw_supp (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) (hx : a < |x|) :
    uSw g a w x = 0 := by simp only [uSw, f2Sw_supp hp hw x hx, Complex.zero_re]

theorem vSw_supp (hp : Probe a g) (hw : ghatC g a w = 0) (x : ℝ) (hx : a < |x|) :
    vSw g a w x = 0 := by simp only [vSw, f2Sw_supp hp hw x hx, Complex.zero_im]

theorem swap_cf (hp : Probe a g) (ha : 0 < a) (hw : ghatC g a w = 0) (hw0 : w ≠ 0)
    (hσ : (w ^ 2).im ≠ 0) (n : ℤ) :
    ‖cf (3 * a) (uSw g a w) n‖ ^ 2 + ‖cf (3 * a) (vSw g a w) n‖ ^ 2 = ‖cf (3 * a) g n‖ ^ 2 := by
  rw [cf_eq_ghatC ha (uSw_supp hp hw), cf_eq_ghatC ha (vSw_supp hp hw), cf_eq_ghatC ha hp.supp]
  set t : ℝ := -(2 * π * n / (4 * (3 * a)))
  set K : ℂ := (1 / (4 * (3 * a)) : ℂ)
  have hx := ghatC_im_zero (memLp_uSw hp hw) (uSw_even hp hw) ha.le t
  have hy := ghatC_im_zero (memLp_vSw hp hw) (vSw_even hp hw) ha.le t
  have R1 := swap_hat hp ha.le hw hw0 t (sq_ne_of_im hσ t)
  rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, ← mul_add,
    norm_sq_add_of_im hx hy, R1, norm_mul, norm_swapB hσ t, mul_one]

/-- **R2.** `A_u + A_v = A_g` everywhere. -/
theorem swap_autocorr (hp : Probe a g) (ha : 0 < a) (hw : ghatC g a w = 0) (hw0 : w ≠ 0)
    (hσ : (w ^ 2).im ≠ 0) (s : ℝ) :
    autocorr (uSw g a w) s + autocorr (vSw g a w) s = autocorr g s := by
  have hus := uSw_supp hp hw
  have hvs := vSw_supp hp hw
  by_cases hs : |s| < 3 * a
  · have ha3 : 0 < 3 * a := by linarith
    have mono : ∀ {f : ℝ → ℝ}, (∀ u, a < |u| → f u = 0) → ∀ u, 3 * a < |u| → f u = 0 :=
      fun hf u hu => hf u (by linarith)
    have Hu := hasSum_shift' ha3 (memLp_uSw hp hw) (mono hus) hs
    have Hv := hasSum_shift' ha3 (memLp_vSw hp hw) (mono hvs) hs
    have Hg := hasSum_shift' ha3 hp.memL2 (mono hp.supp) hs
    have Nu := hasSum_cf_sq ha3 (by linarith : a < 2 * (3 * a)) (memLp_uSw hp hw) hus
    have Nv := hasSum_cf_sq ha3 (by linarith : a < 2 * (3 * a)) (memLp_vSw hp hw) hvs
    have Ng := hasSum_cf_sq ha3 (by linarith : a < 2 * (3 * a)) hp.memL2 hp.supp
    have e1 := (Hu.add Hv).unique (by
      convert Hg using 1; funext n; rw [← add_mul, swap_cf hp ha hw hw0 hσ n])
    have e2 := (Nu.add Nv).unique (by
      convert Ng using 1; funext n; rw [swap_cf hp ha hw hw0 hσ n])
    rw [normSq_eq_autocorr, normSq_eq_autocorr, normSq_eq_autocorr] at e2
    have hK : (0 : ℝ) < (4 * (3 * a))⁻¹ := by positivity
    have f1 : (4 * (3 * a))⁻¹ * (autocorr (uSw g a w) s + autocorr (vSw g a w) s
        - autocorr g s) = 0 := by linarith
    rcases mul_eq_zero.1 f1 with h | h
    · linarith
    · linarith
  · push Not at hs
    have h2 : 2 * a < |s| := by linarith
    rw [autocorr_eq_zero_far hus h2, autocorr_eq_zero_far hvs h2, autocorr_eq_zero_far hp.supp h2,
      add_zero]

theorem arch_dom {u v : ℝ → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hac : ∀ s, autocorr u s + autocorr v s = autocorr g s)
    (hg : IntegrableOn (archIntegrand g) (Ioi 0)) : IntegrableOn (archIntegrand u) (Ioi 0) := by
  refine Integrable.mono' hg (measurable_archIntegrand hu).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have h0 := archIntegrand_nonneg hu hx
  have h1 := archIntegrand_nonneg hv hx
  have hsum : archIntegrand u x + archIntegrand v x = archIntegrand g x := by
    unfold archIntegrand
    linear_combination (Real.exp (x / 2) / Real.sinh x) * (hac 0 - hac x)
  rw [Real.norm_of_nonneg h0]
  linarith

end Pair2

/-! ## The swap realisation -/

/-- **`SwapRealization` holds for every zero `w` of a probe's transform with `w²` non-real.** -/
theorem swapRealization_of_zero {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {w : ℂ}
    (hw : ghatC g a w = 0) (hσ : (w ^ 2).im ≠ 0) : SwapRealization a g (w ^ 2) := by
  have hw0 : w ≠ 0 := by rintro rfl; apply hσ; simp
  have hac := swap_autocorr hp ha hw hw0 hσ
  have hac' : ∀ s, autocorr (vSw g a w) s + autocorr (uSw g a w) s = autocorr g s :=
    fun s => by rw [add_comm]; exact hac s
  refine ⟨uSw g a w, vSw g a w, ⟨uSw_even hp hw, uSw_supp hp hw, memLp_uSw hp hw,
    arch_dom (memLp_uSw hp hw) (memLp_vSw hp hw) hac hp.arch⟩,
    ⟨vSw_even hp hw, vSw_supp hp hw, memLp_vSw hp hw,
    arch_dom (memLp_vSw hp hw) (memLp_uSw hp hw) hac' hp.arch⟩, ?_, hac⟩
  intro z hz
  exact swap_hat hp ha.le hw hw0 z hz

/-- **Zeros of a simple ground state lie on `ℝ ∪ iℝ`** — no further input. -/
theorem zeros_real_or_imag' {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGround a g) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 :=
  zeros_real_or_imag ha hs fun _ hw hσ => swapRealization_of_zero ha hs.1.1 hw hσ

/-- **RH from (a) and eventual simplicity.** The chain of HurwitzCross.lean with the swap
realisation proved: the only inputs left are eventual simplicity of the ground states and the
convergence hypothesis `HypConv`. -/
theorem rh_of_eventually_simple {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGround (a n) (g n))
    (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_simple_ground_states' ha hgs hsimple
    (Eventually.of_forall fun n _ hw hσ => swapRealization_of_zero (ha n) (hgs n).1 hw hσ) hconv

end Pilot1ca

#print axioms Pilot1ca.triangle_swap
#print axioms Pilot1ca.hSw_supp
#print axioms Pilot1ca.hSw_hat
#print axioms Pilot1ca.swap_hat
#print axioms Pilot1ca.swap_autocorr
#print axioms Pilot1ca.swapRealization_of_zero
#print axioms Pilot1ca.zeros_real_or_imag'
#print axioms Pilot1ca.rh_of_eventually_simple
