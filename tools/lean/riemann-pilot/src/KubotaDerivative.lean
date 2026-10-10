import KubotaExpansion

/-! # The derivative `∂_{z̄}` at `z = 0` of the twisted `θ̄`, in both expansions (round 373)

S5f-4b, the second part of round 360's S5f-4. The companion paper puts "`For $z=x+\mathrm i y$, use
$\partial_{\bar z}=(\partial_x+\mathrm i\partial_y)/2$ and $\partial_z=(\partial_x-\mathrm i\partial_y)/2$.`" At a
cusp: "`Thus the derivative in cusp coordinates is $-(cv)^{-2}\partial_{z'}$, with no height-derivative
term.`" This file proves the identity these give between the derivative series at `∞` and at the cusps. The
derivative is not formed: the two directions `1` and `i` enter through symmetric difference quotients,
combined as `(∂_x + i∂_y)/2`.

* **Continuity of `K_ν`** (`continuousAt_besselK`) on `(0, ∞)`, by dominated convergence.
* **The majorant** (`exists_thTerm_bound`, `summable_thDer`, with `rpow_four_thirds_exp_le`): under the
  support and size condition, `|d(m)|·v·|K_{1/3}(4π|m|v/9)|·|m| ≤ A(1 + |m|)^{−3}` for `v` in a compact
  interval of `(0, ∞)`.
* **The symmetric quotient** (**`tendsto_thSer_quot`**, with `ebr_sub_ebr_neg`, `norm_ebr_quot_le` and
  `tendsto_ebr_quot`): if `Z(x)/x → ζ` and `V(x) → V₀ > 0` as `x → 0`, then
  `(F(Z(x), V(x)) − F(−Z(x), V(x)))/(2x) → Σ_m d(m)·V₀·K_{1/3}(4π|m|V₀/9)·i·4π·Re(mζ/9)` for a theta-type
  series `F`. The constant terms cancel exactly, and the limit passes through the series by Tannery's
  theorem (Mathlib's `tendsto_tsum_of_dominated_convergence`).
* **The cusp coordinates along a line** (`cuspW_neg`, `cuspV_neg`, `tendsto_cuspW_quot`, `tendsto_cuspV`):
  `W` is odd and `V` even in `z`; for `σ(c) ≠ 0` and `v > 0`, along `z = xe`, `−W/x → −ē/(σ(c)²v²)` and
  `V → 1/(N(c)v)`.
* **The identity** (**`dbar_identity`**, with `dir_comb_inf`, `dir_comb_cusp`, `tsum_dir_comb`, `dq_sum` and
  `sum_comb`): if, at a height `v > 0`, a theta-type series with zero constant term equals for every `z` a
  finite combination of theta-type series at the cusp coordinates `(−W(z, v), V(z, v))`, all under the
  support and size condition, then
  `Σ_m a(m)·v·K_{1/3}(4π|m|v/9)·2πi·m̄/9` equals the same combination of
  `−(σ(c)v)^{−2}·Σ_m d(m)·V₀·K_{1/3}(4π|m|V₀/9)·2πi·m/9`, with `V₀ = 1/(N(c)v)`.
* **For the twisted `θ̄`** (**`twisted_theta_dbar`**, with `thetaSupp_mul_le` and `norm_twAt_le`): the
  identity for round 371's expansion. The cusp constant terms do not appear in it.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- **`K_ν` is continuous on `(0, ∞)`**, by dominated convergence: for `y > x/2` the integrand is at
most `t^{Re ν − 1}e^{−x(t + 1/t)/4}`. -/
theorem continuousAt_besselK (ν : ℂ) {x : ℝ} (hx : 0 < x) : ContinuousAt (besselK ν) x := by
  show ContinuousAt (fun y => (1 / 2 : ℂ) * mellin (fun t => (bkK y t : ℂ)) ν) x
  refine continuousAt_const.mul ?_
  unfold mellin
  have hx2 : 0 < x / 2 := half_pos hx
  refine continuousAt_of_dominated (bound := fun t => t ^ (ν.re - 1) * bkK (x / 2) t) ?_ ?_
    (integrableOn_bkR hx2 ν.re) ?_
  · filter_upwards [lt_mem_nhds hx] with y hy
    exact Integrable.aestronglyMeasurable (mellinConvergent_bkK hy ν)
  · filter_upwards [lt_mem_nhds (half_lt_self hx)] with y hy
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
      Real.norm_of_nonneg (bkK_pos y t).le]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (bkK_anti hy.le ht') (Real.rpow_nonneg ht'.le _)
  · refine Eventually.of_forall fun t => ?_
    refine Continuous.continuousAt ?_
    unfold bkK
    fun_prop

/-- `t^{4/3}e^{−ct} ≤ (120e^c/c⁵)(1 + t)^{−3}` for `t ≥ 0`, `c > 0`. -/
theorem rpow_four_thirds_exp_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    t ^ (4 / 3 : ℝ) * Real.exp (-(c * t)) ≤ (120 * Real.exp c / c ^ 5) * (1 + t) ^ (-3 : ℝ) := by
  have h1t : 0 < 1 + t := by linarith
  have hfac : (c * (1 + t)) ^ 5 / 120 ≤ Real.exp (c * (1 + t)) := by
    have := Real.pow_div_factorial_le_exp (c * (1 + t)) (by positivity) 5
    simpa [Nat.factorial] using this
  have hroot : t ^ (4 / 3 : ℝ) ≤ (1 + t) ^ 2 := by
    rcases le_or_gt t 1 with h | h
    · calc t ^ (4 / 3 : ℝ) ≤ 1 := Real.rpow_le_one ht h (by norm_num)
        _ ≤ (1 + t) ^ 2 := by nlinarith
    · calc t ^ (4 / 3 : ℝ) ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
        _ = t ^ 2 := by norm_cast
        _ ≤ (1 + t) ^ 2 := by nlinarith
  rw [Real.rpow_neg h1t.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have e3 : (1 + t) ^ (3 : ℝ) = (1 + t) ^ 3 := by norm_cast
  rw [e3]
  have hexp : Real.exp (-(c * t)) = Real.exp c / Real.exp (c * (1 + t)) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [hexp]
  have hE := Real.exp_pos (c * (1 + t))
  rw [div_eq_mul_inv]
  have hc5 : 0 < c ^ 5 := by positivity
  calc t ^ (4 / 3 : ℝ) * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3
      ≤ (1 + t) ^ 2 * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3 := by
        gcongr
    _ = Real.exp c * ((1 + t) ^ 5 / Real.exp (c * (1 + t))) := by ring
    _ ≤ Real.exp c * (120 / c ^ 5) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos c).le
        rw [div_le_div_iff₀ hE hc5]
        have : (c * (1 + t)) ^ 5 = c ^ 5 * (1 + t) ^ 5 := by ring
        nlinarith [hfac, this]
    _ = 120 * Real.exp c / c ^ 5 := by ring

/-- **The majorant of the differentiated series**: under the support and size condition, for
`0 < v₀ ≤ v ≤ v₁`, `|d(m)|·v·|K_{1/3}(4π|m|v/9)|·|m| ≤ A(1 + |m|)^{−3}`, with `A` independent of `v`
and `m`. -/
theorem exists_thTerm_bound {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (v₁ : ℝ) : ∃ A, 0 ≤ A ∧ ∀ v, v₀ ≤ v → v ≤ v₁ → ∀ m : 𝓞 K,
      ‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ * ‖σO m‖ ≤
        A * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
  set c := 2 * Real.pi * v₀ / 9 with hc_def
  have hc : 0 < c := by positivity
  have hR0 : 0 ≤ bkR (1 / 3) c := bkR_nonneg _ _
  have hKc := h.1
  have hA0 : 0 ≤ Kc * |v₁| * (1 / 2) * bkR (1 / 3) c * (120 * Real.exp c / c ^ 5) := by positivity
  refine ⟨_, hA0, fun v hv hv1 m => ?_⟩
  have hvpos : 0 < v := hv₀.trans_le hv
  by_cases hm : d m = 0
  · rw [hm, norm_zero, zero_mul, zero_mul, zero_mul]
    exact mul_nonneg hA0 (by positivity)
  obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
  have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
  have h1 := one_le_norm_σO hm0
  have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * v / 9)
  have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num
  rw [hre] at hK
  have hx₀ : 0 < 4 * Real.pi * v₀ / 9 := by positivity
  have hxx : 4 * Real.pi * v₀ / 9 ≤ 4 * Real.pi * ‖σO m‖ * v / 9 := by
    have := Real.pi_pos
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    have : v₀ ≤ ‖σO m‖ * v := by nlinarith
    nlinarith
  have hdecay := bkR_le_exp (r := 1 / 3) hx₀ hxx
  rw [show 4 * Real.pi * v₀ / 9 / 2 = c by rw [hc_def]; ring] at hdecay
  have hexp : Real.exp (-(4 * Real.pi * ‖σO m‖ * v / 9 / 2)) ≤ Real.exp (-(c * ‖σO m‖)) := by
    apply Real.exp_le_exp.2
    rw [hc_def]
    have := Real.pi_pos
    have : v₀ * ‖σO m‖ ≤ v * ‖σO m‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    nlinarith
  have hpoly := rpow_four_thirds_exp_le hc (norm_nonneg (σO m))
  have hd := norm_le_of_thetaSupp h m
  have e43 : ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ = ‖σO m‖ ^ (4 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add_one (by linarith)]
  have hKb : ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ ≤
      (1 / 2) * (Real.exp (-(c * ‖σO m‖)) * bkR (1 / 3) c) :=
    hK.trans (mul_le_mul_of_nonneg_left (hdecay.trans (mul_le_mul_of_nonneg_right hexp hR0))
      (by norm_num))
  calc ‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ * ‖σO m‖
      ≤ (Kc * ‖σO m‖ ^ (1 / 3 : ℝ)) * |v₁| * ((1 / 2) * (Real.exp (-(c * ‖σO m‖)) * bkR (1 / 3) c)) *
          ‖σO m‖ := by
        gcongr
        exact hv1.trans (le_abs_self v₁)
    _ = Kc * |v₁| * (1 / 2) * bkR (1 / 3) c * (‖σO m‖ ^ (4 / 3 : ℝ) * Real.exp (-(c * ‖σO m‖))) := by
        rw [← e43]; ring
    _ ≤ Kc * |v₁| * (1 / 2) * bkR (1 / 3) c * ((120 * Real.exp c / c ^ 5) * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by
        gcongr
    _ = Kc * |v₁| * (1 / 2) * bkR (1 / 3) c * (120 * Real.exp c / c ^ 5) * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
        ring

/-- **The differentiated series converge absolutely**: `Σ_m d(m)·v·K_{1/3}(4π|m|v/9)·φ(m)` for
`|φ(m)| ≤ C|m|`, under the support and size condition. -/
theorem summable_thDer {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) {v : ℝ} (hv : 0 < v)
    {φ : 𝓞 K → ℂ} {C : ℝ} (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) :
    Summable fun m : 𝓞 K => d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * φ m := by
  obtain ⟨A, hA0, hA⟩ := exists_thTerm_bound h hv v
  refine Summable.of_norm_bounded (summable_O_of_le (f := fun m => |C| * A * (1 + ‖σO m‖) ^ (-3 : ℝ))
    (fun m => by positivity) (fun m => le_refl _)) fun m => ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
  have h1 := hA v le_rfl le_rfl m
  have h2 : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
    (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  calc ‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ * ‖φ m‖
      ≤ ‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ * (|C| * ‖σO m‖) := by gcongr
    _ = |C| * (‖d m‖ * v * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ * ‖σO m‖) := by ring
    _ ≤ |C| * (A * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by gcongr
    _ = |C| * A * (1 + ‖σO m‖) ^ (-3 : ℝ) := by ring

/-- `ĕ(w) − ĕ(−w) = 2i·sin(4π Re w)`. -/
theorem ebr_sub_ebr_neg (w : ℂ) :
    ebr w - ebr (-w) = 2 * I * ((Real.sin (4 * Real.pi * w.re) : ℝ) : ℂ) := by
  unfold ebr
  have e1 : 2 * (Real.pi : ℂ) * I * ((2 * w.re : ℝ) : ℂ) = ((4 * Real.pi * w.re : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : 2 * (Real.pi : ℂ) * I * ((2 * (-w).re : ℝ) : ℂ) =
      (-((4 * Real.pi * w.re : ℝ) : ℂ)) * I := by
    rw [Complex.neg_re]; push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin]
  ring

/-- `|ĕ(aZ/9) − ĕ(−aZ/9)|/|2x| ≤ (4π/9)|a||Z/x|`, since `|sin y| ≤ |y|`. -/
theorem norm_ebr_quot_le (a Z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ‖(ebr (a * Z / 9) - ebr (-(a * Z / 9))) / (2 * x)‖ ≤ 4 * Real.pi / 9 * ‖a‖ * ‖Z / x‖ := by
  have hx' : 0 < |x| := abs_pos.2 hx
  have key : ‖(ebr (a * Z / 9) - ebr (-(a * Z / 9))) / (2 * x)‖ =
      |Real.sin (4 * Real.pi * (a * Z / 9).re)| / |x| := by
    rw [ebr_sub_ebr_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_I]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    field_simp
  have hs := Real.abs_sin_le_abs (x := 4 * Real.pi * (a * Z / 9).re)
  have hre : |(a * Z / 9).re| ≤ ‖a‖ * ‖Z‖ / 9 := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_div, norm_mul]
    simp
  have hθ : |4 * Real.pi * (a * Z / 9).re| ≤ 4 * Real.pi * (‖a‖ * ‖Z‖ / 9) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hre (by positivity)
  rw [key, norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hx']
  calc |Real.sin (4 * Real.pi * (a * Z / 9).re)| ≤ 4 * Real.pi * (‖a‖ * ‖Z‖ / 9) := hs.trans hθ
    _ = 4 * Real.pi / 9 * ‖a‖ * (‖Z‖ / |x|) * |x| := by field_simp

/-- **The symmetric quotient of `ĕ`**: if `Z(x)/x → ζ` as `x → 0`, then
`(ĕ(aZ(x)/9) − ĕ(−aZ(x)/9))/(2x) → i·4π·Re(aζ/9)`. -/
theorem tendsto_ebr_quot (a : ℂ) {Z : ℝ → ℂ} {ζ : ℂ}
    (hZ : Tendsto (fun x : ℝ => Z x / x) (𝓝[≠] 0) (𝓝 ζ)) :
    Tendsto (fun x : ℝ => (ebr (a * Z x / 9) - ebr (-(a * Z x / 9))) / (2 * x)) (𝓝[≠] 0)
      (𝓝 (I * ((4 * Real.pi * (a * ζ / 9).re : ℝ) : ℂ))) := by
  set θ : ℝ → ℝ := fun x => 4 * Real.pi * (a * Z x / 9).re with hθ_def
  have hq : Tendsto (fun x : ℝ => θ x / x) (𝓝[≠] 0) (𝓝 (4 * Real.pi * (a * ζ / 9).re)) := by
    have h1 : Tendsto (fun x : ℝ => 4 * Real.pi * (a * (Z x / x) / 9).re) (𝓝[≠] 0)
        (𝓝 (4 * Real.pi * (a * ζ / 9).re)) :=
      ((Complex.continuous_re.tendsto _).comp ((hZ.const_mul a).div_const 9)).const_mul _
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [hθ_def]
    rw [show a * (Z x / x) / 9 = (a * Z x / 9) / (x : ℂ) by ring, Complex.div_ofReal_re]
    ring
  have hid : Tendsto (fun x : ℝ => x) (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hθ0 : Tendsto θ (𝓝[≠] 0) (𝓝 0) := by
    have h2 := hq.mul hid
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_mul_cancel₀ (θ x) hx
  have hs := (Real.continuous_sinc.tendsto 0).comp hθ0
  rw [Real.sinc_zero] at hs
  have key : Tendsto (fun x : ℝ => I * ((Real.sinc (θ x) * (θ x / x) : ℝ) : ℂ)) (𝓝[≠] 0)
      (𝓝 (I * ((1 * (4 * Real.pi * (a * ζ / 9).re) : ℝ) : ℂ))) :=
    tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (hs.mul hq))
  rw [one_mul] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  have hsinc : Real.sinc (θ x) * θ x = Real.sin (θ x) := by
    by_cases h0 : θ x = 0
    · rw [h0, mul_zero, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero h0, div_mul_cancel₀ _ h0]
  rw [ebr_sub_ebr_neg, ← mul_div_assoc, ← hsinc]
  simp only [hθ_def]
  push_cast
  field_simp

/-- **The symmetric difference quotient of a theta-type series**: if `Z(x)/x → ζ` and `V(x) → V₀ > 0` as
`x → 0`, then `(F(Z(x), V(x)) − F(−Z(x), V(x)))/(2x) → Σ_m d(m)·V₀·K_{1/3}(4π|m|V₀/9)·i·4π·Re(mζ/9)`. For an
odd curve `Z` and an even height `V` this is the symmetric quotient along the curve. The constant terms
cancel exactly, and the limit passes through the series by Tannery's theorem. -/
theorem tendsto_thSer_quot {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (c : ℂ) {Z : ℝ → ℂ}
    {V : ℝ → ℝ} {ζ : ℂ} {V₀ : ℝ} (hV₀ : 0 < V₀)
    (hZ : Tendsto (fun x : ℝ => Z x / x) (𝓝[≠] 0) (𝓝 ζ)) (hV : Tendsto V (𝓝[≠] 0) (𝓝 V₀)) :
    Tendsto (fun x : ℝ => (thSer c d (Z x) (V x) - thSer c d (-Z x) (V x)) / (2 * x)) (𝓝[≠] 0)
      (𝓝 (∑' m : 𝓞 K, d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ / 9).re : ℝ) : ℂ)))) := by
  obtain ⟨A, hA0, hA⟩ := exists_thTerm_bound h (half_pos hV₀) (2 * V₀)
  have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ≠ 0 ∧ V₀ / 2 < V x ∧ V x < 2 * V₀ ∧ ‖Z x / x‖ < ‖ζ‖ + 1 := by
    have h2 := hV.eventually (Ioo_mem_nhds (half_lt_self hV₀) (by linarith : V₀ < 2 * V₀))
    have h3 := hZ.norm.eventually (gt_mem_nhds (lt_add_one ‖ζ‖))
    filter_upwards [self_mem_nhdsWithin, h2, h3] with x hx h2 h3
    exact ⟨hx, h2.1, h2.2, h3⟩
  have heq : (fun x : ℝ => (thSer c d (Z x) (V x) - thSer c d (-Z x) (V x)) / (2 * x)) =ᶠ[𝓝[≠] 0]
      fun x => ∑' m : 𝓞 K, d m * (V x : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V x / 9) *
        ((ebr (σO m * Z x / 9) - ebr (-(σO m * Z x / 9))) / (2 * x)) := by
    filter_upwards [hev] with x ⟨hx, hV1, hV2, _⟩
    have hVx : 0 < V x := by linarith
    unfold thSer
    rw [add_sub_add_left_eq_sub, ← (summable_thSer h (Z x) hVx).tsum_sub (summable_thSer h (-Z x) hVx),
      ← tsum_div_const]
    refine tsum_congr fun m => ?_
    rw [show σO m * -Z x / 9 = -(σO m * Z x / 9) by ring]
    ring
  refine Tendsto.congr' heq.symm (tendsto_tsum_of_dominated_convergence
    (bound := fun m => 4 * Real.pi / 9 * (‖ζ‖ + 1) * A * (1 + ‖σO m‖) ^ (-3 : ℝ))
    (summable_O_of_le (fun m => by positivity) (fun m => le_refl _)) (fun m => ?_) ?_)
  · by_cases hm : d m = 0
    · simp only [hm, zero_mul]
      exact tendsto_const_nhds
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have h1' : 0 < ‖σO m‖ := by linarith
    have hpos : 0 < 4 * Real.pi * ‖σO m‖ * V₀ / 9 := by positivity
    have hVc : Tendsto (fun x => ((V x : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 (V₀ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto V₀).comp hV
    have hK : Tendsto (fun x => besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V x / 9)) (𝓝[≠] 0)
        (𝓝 (besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9))) :=
      (continuousAt_besselK _ hpos).tendsto.comp ((hV.const_mul (4 * Real.pi * ‖σO m‖)).div_const 9)
    exact ((tendsto_const_nhds.mul hVc).mul hK).mul (tendsto_ebr_quot (σO m) hZ)
  · filter_upwards [hev] with x ⟨hx, hV1, hV2, hZx⟩ m
    have hVx : 0 < V x := by linarith
    have hq := norm_ebr_quot_le (σO m) (Z x) hx
    have hb := hA (V x) hV1.le hV2.le m
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hVx.le]
    calc ‖d m‖ * V x * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V x / 9)‖ *
          ‖(ebr (σO m * Z x / 9) - ebr (-(σO m * Z x / 9))) / (2 * x)‖
        ≤ ‖d m‖ * V x * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V x / 9)‖ *
          (4 * Real.pi / 9 * ‖σO m‖ * (‖ζ‖ + 1)) := by
          gcongr
          exact hq.trans (mul_le_mul_of_nonneg_left hZx.le (by positivity))
      _ = 4 * Real.pi / 9 * (‖ζ‖ + 1) *
          (‖d m‖ * V x * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V x / 9)‖ * ‖σO m‖) := by ring
      _ ≤ 4 * Real.pi / 9 * (‖ζ‖ + 1) * (A * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by gcongr
      _ = 4 * Real.pi / 9 * (‖ζ‖ + 1) * A * (1 + ‖σO m‖) ^ (-3 : ℝ) := by ring

theorem thetaSupp_mul_le {Kc B : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (hB : 0 ≤ B)
    (hφ : ∀ m, ‖φ m‖ ≤ B) : ThetaSupp (B * Kc) fun m => d m * φ m := by
  refine ⟨mul_nonneg hB h.1, fun m hm => ?_⟩
  have hd : d m ≠ 0 := fun h0 => hm (by simp [h0])
  obtain ⟨q, hq, h1, h2, h3, h4⟩ := h.2 m hd
  refine ⟨q, hq, h1, h2, h3, ?_⟩
  rw [norm_mul]
  have h5 : 0 ≤ Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2) := by
    have := h.1; positivity
  calc ‖d m‖ * ‖φ m‖ ≤ (Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2)) * B :=
        mul_le_mul h4 (hφ m) (norm_nonneg _) h5
    _ = B * Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2) := by ring

theorem norm_twAt_le {F : 𝓞 K → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) (m : 𝓞 K) :
    ‖twAt F m‖ ≤ B := by
  unfold twAt
  split_ifs
  · exact hF _
  · simpa using hB

theorem cuspW_neg (c : 𝓞 K) (z : ℂ) (v : ℝ) : cuspW c (-z) v = -cuspW c z v := by
  unfold cuspW
  rw [map_neg, Complex.normSq_neg, neg_div]

theorem cuspV_neg (c : 𝓞 K) (z : ℂ) (v : ℝ) : cuspV c (-z) v = cuspV c z v := by
  unfold cuspV
  rw [Complex.normSq_neg]

/-- Along `z = xe`: `−W(xe, v)/x → −ē/(σ(c)²v²)` as `x → 0`. -/
theorem tendsto_cuspW_quot {c : 𝓞 K} (hc : σO c ≠ 0) (e : ℂ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun x : ℝ => -cuspW c (x * e) v / x) (𝓝[≠] 0)
      (𝓝 (-(conj e / (σO c ^ 2 * (v : ℂ) ^ 2)))) := by
  have hNe := Complex.normSq_nonneg e
  have hden : ContinuousAt (fun x : ℝ => σO c ^ 2 * (((x ^ 2 * Complex.normSq e + v ^ 2 : ℝ)) : ℂ)) 0 :=
    Continuous.continuousAt (by fun_prop)
  have hden0 : σO c ^ 2 * ((((0 : ℝ) ^ 2 * Complex.normSq e + v ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero 2 hc) ?_
    exact_mod_cast (by positivity : (0 : ℝ) < (0 : ℝ) ^ 2 * Complex.normSq e + v ^ 2).ne'
  have h1 : Tendsto (fun x : ℝ => -(conj e / (σO c ^ 2 * (((x ^ 2 * Complex.normSq e + v ^ 2 : ℝ)) : ℂ))))
      (𝓝 0) (𝓝 (-(conj e / (σO c ^ 2 * ((((0 : ℝ) ^ 2 * Complex.normSq e + v ^ 2 : ℝ)) : ℂ))))) :=
    (tendsto_const_nhds.div hden.tendsto hden0).neg
  rw [show ((0 : ℝ) ^ 2 * Complex.normSq e + v ^ 2 : ℝ) = v ^ 2 by ring, Complex.ofReal_pow] at h1
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
  show -(conj e / (σO c ^ 2 * (((x ^ 2 * Complex.normSq e + v ^ 2 : ℝ)) : ℂ))) = -cuspW c (x * e) v / x
  unfold cuspW
  rw [map_mul, Complex.conj_ofReal, Complex.normSq_mul, Complex.normSq_ofReal,
    show x * x * Complex.normSq e + v ^ 2 = x ^ 2 * Complex.normSq e + v ^ 2 by ring,
    neg_div, mul_div_assoc, mul_div_cancel_left₀ _ hx']

/-- Along `z = xe`: `V(xe, v) → 1/(N(c)v)` as `x → 0`. -/
theorem tendsto_cuspV {c : 𝓞 K} (hc : σO c ≠ 0) (e : ℂ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun x : ℝ => cuspV c (x * e) v) (𝓝[≠] 0) (𝓝 (Complex.normSq (σO c) * v)⁻¹) := by
  have hN : 0 < Complex.normSq (σO c) := Complex.normSq_pos.2 hc
  have hN' : Complex.normSq (σO c) ≠ 0 := hN.ne'
  have hv' : v ≠ 0 := hv.ne'
  have hNe := Complex.normSq_nonneg e
  have heq : (fun x : ℝ => cuspV c (x * e) v) =
      fun x : ℝ => v / (Complex.normSq (σO c) * (x ^ 2 * Complex.normSq e + v ^ 2)) := by
    funext x
    unfold cuspV
    rw [Complex.normSq_mul, Complex.normSq_ofReal,
      show x * x * Complex.normSq e = x ^ 2 * Complex.normSq e by ring]
  have hcont : Continuous fun x : ℝ => v / (Complex.normSq (σO c) * (x ^ 2 * Complex.normSq e + v ^ 2)) :=
    continuous_const.div (by fun_prop) fun x => by positivity
  have h1 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  beta_reduce at h1
  rw [heq]
  convert h1 using 2
  field_simp
  ring

/-- `i·4π Re(a/9) + i·(i·4π Re(ai/9)) = 2·(2πi·ā/9)`: the two directions at `∞` give `∂_{z̄}`. -/
theorem dir_comb_inf (a : ℂ) :
    I * ((4 * Real.pi * (a * 1 / 9).re : ℝ) : ℂ) + I * (I * ((4 * Real.pi * (a * I / 9).re : ℝ) : ℂ)) =
      2 * (2 * Real.pi * I * conj a / 9) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The two directions at a cusp: with `ζ_e = −ē/D`, the combination is `2·(−D⁻¹·2πi·a/9)`. -/
theorem dir_comb_cusp (a D : ℂ) :
    I * ((4 * Real.pi * (a * -(conj 1 / D) / 9).re : ℝ) : ℂ) +
      I * (I * ((4 * Real.pi * (a * -(conj I / D) / 9).re : ℝ) : ℂ)) =
      2 * (-D⁻¹ * (2 * Real.pi * I * a / 9)) := by
  rw [map_one, Complex.conj_I]
  have e1 : a * -(1 / D) / 9 = -(a / D) / 9 := by ring
  have e2 : a * -(-I / D) / 9 = I * (a / D) / 9 := by ring
  rw [e1, e2, show -D⁻¹ * (2 * Real.pi * I * a / 9) = -(2 * Real.pi * I * (a / D) / 9) by ring]
  generalize a / D = u
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- **The two directional limits combine into one series**: `(L₁ + i·L₂)/2 = Σ_m d(m)V₀K_{1/3}(…)ψ(m)`
when the directional factors combine to `2ψ(m)`. -/
theorem tsum_dir_comb {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) {V₀ : ℝ} (hV₀ : 0 < V₀)
    (ζ₁ ζ₂ : ℂ) (ψ : 𝓞 K → ℂ)
    (hψ : ∀ m : 𝓞 K, I * ((4 * Real.pi * (σO m * ζ₁ / 9).re : ℝ) : ℂ) +
      I * (I * ((4 * Real.pi * (σO m * ζ₂ / 9).re : ℝ) : ℂ)) = 2 * ψ m) :
    ((∑' m : 𝓞 K, d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ₁ / 9).re : ℝ) : ℂ))) +
      I * ∑' m : 𝓞 K, d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ₂ / 9).re : ℝ) : ℂ))) / 2 =
      ∑' m : 𝓞 K, d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) * ψ m := by
  have hb : ∀ ζ : ℂ, ∀ m : 𝓞 K, ‖I * ((4 * Real.pi * (σO m * ζ / 9).re : ℝ) : ℂ)‖ ≤
      4 * Real.pi * ‖ζ‖ / 9 * ‖σO m‖ := by
    intro ζ m
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
    have h1 := Complex.abs_re_le_norm (σO m * ζ / 9)
    rw [norm_div, norm_mul] at h1
    have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
    rw [h9] at h1
    calc 4 * Real.pi * |(σO m * ζ / 9).re| ≤ 4 * Real.pi * (‖σO m‖ * ‖ζ‖ / 9) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * Real.pi * ‖ζ‖ / 9 * ‖σO m‖ := by ring
  have s1 := summable_thDer h hV₀ (hb ζ₁)
  have s2 := (summable_thDer h hV₀ (hb ζ₂)).mul_left I
  rw [← tsum_mul_left, ← s1.tsum_add s2, ← tsum_div_const]
  refine tsum_congr fun m => ?_
  have e := hψ m
  calc (d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ₁ / 9).re : ℝ) : ℂ)) +
      I * (d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ₂ / 9).re : ℝ) : ℂ)))) / 2
      = d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) *
        (I * ((4 * Real.pi * (σO m * ζ₁ / 9).re : ℝ) : ℂ) +
          I * (I * ((4 * Real.pi * (σO m * ζ₂ / 9).re : ℝ) : ℂ))) / 2 := by ring
    _ = d m * (V₀ : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * V₀ / 9) * ψ m := by
        rw [e]; ring

theorem dq_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (α : ι → ℂ) (β : κ → ℂ)
    (γ f g : ι → κ → ℂ) (w : ℂ) :
    ((∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * f i k)) -
        ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * g i k)) / w =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * ((f i k - g i k) / w)) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sum_comb {ι κ : Type*} (s : Finset ι) (t : Finset κ) (α : ι → ℂ) (β : κ → ℂ)
    (γ P Q : ι → κ → ℂ) :
    ((∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * P i k)) +
        I * ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * Q i k)) / 2 =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * ((P i k + I * Q i k) / 2)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **`∂_{z̄}` at `z = 0` through an expansion in cusp coordinates**: if, at a height `v > 0`, a theta-type
series with zero constant term equals for every `z` a finite combination of theta-type series at the cusp
coordinates `(−W(z, v), V(z, v))`, all under the support and size condition, then the series of `∂_{z̄}` at
`z = 0` at `∞`, `Σ_m a(m)·v·K_{1/3}(4π|m|v/9)·2πi·m̄/9`, equals the combination of
`−(σ(c)v)^{−2}·Σ_m d(m)·V₀·K_{1/3}(4π|m|V₀/9)·2πi·m/9`, with `V₀ = 1/(N(c)v)`. The constant terms drop out. -/
theorem dbar_identity {ι κ : Type*} (s : Finset ι) (t : Finset κ) {Ka : ℝ} {a : 𝓞 K → ℂ}
    (ha : ThetaSupp Ka a) (α : ι → ℂ) (β : κ → ℂ) (γ c₁ : ι → κ → ℂ) (dd : ι → κ → 𝓞 K → ℂ)
    (cc : ι → κ → 𝓞 K) (Kd : ι → κ → ℝ)
    (hdd : ∀ i ∈ s, ∀ k ∈ t, ThetaSupp (Kd i k) (dd i k) ∧ σO (cc i k) ≠ 0) {v : ℝ} (hv : 0 < v)
    (hexp : ∀ z, thSer 0 a z v = ∑ i ∈ s, α i * ∑ k ∈ t, β k *
      (γ i k * thSer (c₁ i k) (dd i k) (-cuspW (cc i k) z v) (cuspV (cc i k) z v))) :
    ∑' m : 𝓞 K, a m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
        (2 * Real.pi * I * conj (σO m) / 9) =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * (-(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
        ∑' m : 𝓞 K, dd i k m * (((Complex.normSq (σO (cc i k)) * v)⁻¹ : ℝ) : ℂ) *
          besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * (Complex.normSq (σO (cc i k)) * v)⁻¹ / 9) *
          (2 * Real.pi * I * σO m / 9))) := by
  have hV₀ : ∀ i ∈ s, ∀ k ∈ t, 0 < (Complex.normSq (σO (cc i k)) * v)⁻¹ := fun i hi k hk =>
    inv_pos.2 (mul_pos (Complex.normSq_pos.2 (hdd i hi k hk).2) hv)
  have hinf : ∀ e : ℂ, Tendsto (fun x : ℝ => (thSer 0 a (x * e) v - thSer 0 a (-(x * e)) v) / (2 * x))
      (𝓝[≠] 0) (𝓝 (∑' m : 𝓞 K, a m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
        (I * ((4 * Real.pi * (σO m * e / 9).re : ℝ) : ℂ)))) := by
    intro e
    have hZ : Tendsto (fun x : ℝ => (x : ℂ) * e / x) (𝓝[≠] 0) (𝓝 e) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (mul_div_cancel_left₀ e (Complex.ofReal_ne_zero.2 hx)).symm
    exact tendsto_thSer_quot ha 0 (Z := fun x : ℝ => (x : ℂ) * e) (V := fun _ => v) hv hZ
      tendsto_const_nhds
  have hcusp : ∀ e : ℂ, ∀ i ∈ s, ∀ k ∈ t, Tendsto (fun x : ℝ =>
      (thSer (c₁ i k) (dd i k) (-cuspW (cc i k) (x * e) v) (cuspV (cc i k) (x * e) v) -
        thSer (c₁ i k) (dd i k) (-cuspW (cc i k) (-(x * e)) v) (cuspV (cc i k) (-(x * e)) v)) / (2 * x))
      (𝓝[≠] 0) (𝓝 (∑' m : 𝓞 K, dd i k m * (((Complex.normSq (σO (cc i k)) * v)⁻¹ : ℝ) : ℂ) *
          besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * (Complex.normSq (σO (cc i k)) * v)⁻¹ / 9) *
          (I * ((4 * Real.pi * (σO m * -(conj e / (σO (cc i k) ^ 2 * (v : ℂ) ^ 2)) / 9).re : ℝ) : ℂ)))) := by
    intro e i hi k hk
    obtain ⟨hd, hc⟩ := hdd i hi k hk
    have key := tendsto_thSer_quot hd (c₁ i k) (hV₀ i hi k hk) (tendsto_cuspW_quot hc e hv)
      (tendsto_cuspV hc e hv)
    refine key.congr fun x => ?_
    simp only [cuspW_neg, cuspV_neg, neg_neg]
  have hq : ∀ e : ℂ, ∀ x : ℝ, (thSer 0 a (x * e) v - thSer 0 a (-(x * e)) v) / (2 * x) =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k *
        ((thSer (c₁ i k) (dd i k) (-cuspW (cc i k) (x * e) v) (cuspV (cc i k) (x * e) v) -
          thSer (c₁ i k) (dd i k) (-cuspW (cc i k) (-(x * e)) v) (cuspV (cc i k) (-(x * e)) v)) /
            (2 * x))) := by
    intro e x
    rw [hexp, hexp]
    exact dq_sum _ _ _ _ _ _ _ _
  have hlim : ∀ e : ℂ, ∑' m : 𝓞 K, a m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
        (I * ((4 * Real.pi * (σO m * e / 9).re : ℝ) : ℂ)) =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k *
        ∑' m : 𝓞 K, dd i k m * (((Complex.normSq (σO (cc i k)) * v)⁻¹ : ℝ) : ℂ) *
          besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * (Complex.normSq (σO (cc i k)) * v)⁻¹ / 9) *
          (I * ((4 * Real.pi * (σO m * -(conj e / (σO (cc i k) ^ 2 * (v : ℂ) ^ 2)) / 9).re : ℝ) : ℂ))) := by
    intro e
    refine tendsto_nhds_unique (hinf e) ?_
    simp only [hq e]
    exact tendsto_finsetSum _ fun i hi => (tendsto_finsetSum _ fun k hk =>
      ((hcusp e i hi k hk).const_mul (γ i k)).const_mul (β k)).const_mul (α i)
  rw [← tsum_dir_comb ha hv 1 I _ fun m => dir_comb_inf (σO m), hlim 1, hlim I, sum_comb]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 2
  rw [tsum_dir_comb (hdd i hi k hk).1 (hV₀ i hi k hk) _ _ _ fun m => dir_comb_cusp (σO m) _,
    ← tsum_mul_left]
  exact tsum_congr fun m => by ring

open Classical in
/-- **`∂_{z̄}` at `z = 0` of the twisted `θ̄`, in both expansions** (S5f-4b): for data `(D, C₀, d_H, y)` as in
`twisted_theta_expansion` and `v > 0`, the series `Σ_m a(m)·v·K_{1/3}(4π|m|v/9)·2πi·m̄/9` of the
twisted coefficients `a(m) = φ(m/λ)·conj τ(−m)` equals the sum over `h₀` and the active sets `A` of
`φ̂₀(h₀)∏_{P∉A}C_{P,j_P}(0)C₀(h₀, A)` times `−(σ(c)v)^{−2}·Σ_m d′(m)·V₀·K_{1/3}(4π|m|V₀/9)·2πi·m/9`, with
`c = D(h₀, A)∏_{P∈A}π_P`, `V₀ = 1/(N(c)v)` and the cusp coefficients `d′` of the group. -/
theorem twisted_theta_dbar {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ (D : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K) (C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K → ℂ) (y : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K),
      (∀ h₀, ∀ A ∈ Ps.powerset, D h₀ A ≠ 0 ∧ D h₀ A ∣ L ∧ ‖C₀ h₀ A‖ = 1 ∧ ThetaSupp Kc (dH h₀ A)) ∧
      ∀ v : ℝ, 0 < v →
        ∑' m : 𝓞 K, twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) * (v : ℂ) *
            besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * (2 * Real.pi * I * conj (σO m) / 9) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ A * ∏ P ∈ A, πP P) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
                    (∏ P : A, Bloc P.1.1 (j P.1) m) *
                  (((Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) * v)⁻¹ : ℝ) : ℂ) *
                  besselK (1 / 3)
                    (4 * Real.pi * ‖σO m‖ * (Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) * v)⁻¹ / 9) *
                  (2 * Real.pi * I * σO m / 9))) := by
  obtain ⟨D, C₀, cH, dH, y, hDATA, hexp⟩ := twisted_theta_expansion hd hL φ₀ hφ hφ0 Ps hPs j
  refine ⟨D, C₀, dH, y, hDATA, fun v hv => ?_⟩
  obtain ⟨B₀, hB₀⟩ := exists_bound_of_periodic L hL φ₀ hφ
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hF : ∀ x, ‖φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x‖ ≤ B₀ := by
    intro x
    rw [norm_mul, norm_prod]
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun P _ => norm_chiPow_le _ _ _))).trans (hB₀ x)
  have ha : ThetaSupp (B₀ * Kc)
      fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) := by
    have h1 := thetaSupp_mul_le (thetaSupp_conj hd.1) hB₀0 (norm_twAt_le hB₀0 hF)
    have e : (fun m => conj (τ (-m)) * twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m) =
        fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) :=
      funext fun m => mul_comm _ _
    rwa [e] at h1
  have := finite_quot L hL
  let _ : Fintype (𝓞 K ⧸ span {L}) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  refine dbar_identity Finset.univ Ps.powerset ha (fun h₀ => fCoef L φ₀ (repQ L h₀))
    (fun A => ∏ P ∈ Ps \ A, locCoef P (j P) 0) C₀
    (fun h₀ A => conj (cH h₀ A) * ∏ P : A, Bloc P.1.1 (j P.1) 0)
    (fun h₀ A m => conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
      ∏ P : A, Bloc P.1.1 (j P.1) m)
    (fun h₀ A => D h₀ A * ∏ P ∈ A, πP P) (fun _ A => (∏ P : A, Real.sqrt (absNorm P.1.1)) * Kc)
    (fun h₀ _ A hA => ⟨?_, ?_⟩) hv (fun z => ?_)
  · have h1 := thetaSupp_mul (thetaSupp_conj (hDATA h₀ A hA).2.2.2)
      (fun m => (norm_ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A))).le)
    exact thetaSupp_mul_le h1 (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) fun m => by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => norm_Bloc_le_sqrt P.1 (j P.1) m
  · have hD := (hDATA h₀ A hA).1
    have hprod : (∏ P ∈ A, πP P) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ => ne_zero_of_maximal (πP P)
    have hc : D h₀ A * ∏ P ∈ A, πP P ≠ 0 := mul_ne_zero hD hprod
    exact fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  · rw [← finsum_eq_sum_of_fintype, ← hexp z v hv]
    unfold thSer
    rw [zero_mul, zero_add]

end Eis

end

#print axioms Eis.continuousAt_besselK
#print axioms Eis.rpow_four_thirds_exp_le
#print axioms Eis.exists_thTerm_bound
#print axioms Eis.summable_thDer
#print axioms Eis.ebr_sub_ebr_neg
#print axioms Eis.norm_ebr_quot_le
#print axioms Eis.tendsto_ebr_quot
#print axioms Eis.tendsto_thSer_quot
#print axioms Eis.thetaSupp_mul_le
#print axioms Eis.norm_twAt_le
#print axioms Eis.cuspW_neg
#print axioms Eis.cuspV_neg
#print axioms Eis.tendsto_cuspW_quot
#print axioms Eis.tendsto_cuspV
#print axioms Eis.dir_comb_inf
#print axioms Eis.dir_comb_cusp
#print axioms Eis.tsum_dir_comb
#print axioms Eis.dq_sum
#print axioms Eis.sum_comb
#print axioms Eis.dbar_identity
#print axioms Eis.twisted_theta_dbar
