import KubotaConstTerm
import KubotaTranslates

/-! # The Fourier coefficients of the Eisenstein series (round 428)

S5f-10 of round 360's plan, part 11 (S5f-10f, first part). Round 427's next step planned the Fourier modes of
θ through the `m`-th Fourier coefficient of `E_s` for `Re s > 2`. This round computes that coefficient, with
round 361's `ĕ(w) = e^{4πi·Re w}` and the frequencies `m = δ₃x`:

* **The planar Fourier transform** (**`integral_ebr_inv_cpow`**, with `measurable_ebr`, `ebr_neg_mul_exp`,
  `integral_ebr_gauss`, `cpow_neg_eq_integral`, `ftInt`, `ftInt_eq`, `measurable_ftInt`, `norm_ftInt` and
  `integrable_ftInt`): for `ξ ≠ 0` and `Re s > 1`,
  `∫_ℂ ĕ(−ξz)(1 + |z|²)^{−s} dz = (2π/Γ(s))·(2π|ξ|)^{s−1}·K_{s−1}(4π|ξ|)`, from the Gamma integral
  `r^{−s} = Γ(s)⁻¹∫_0^∞ t^{s−1}e^{−rt} dt`, Fubini, Mathlib's Gaussian integral
  `integral_cexp_neg_mul_sq_norm_add`, and round 361's `besselK` as a Mellin transform, rescaled by `2π|ξ|`
  (Mathlib's `mellin_comp_mul_left`).
* **`K_ν` is entire in `ν`** (**`differentiable_besselK`**), with the bounds of round 361's
  `mellinConvergent_bkK`.
* **One term** (**`integral_ebr_height_cpow`**): for `c ≠ 0`,
  `∫_ℂ ĕ(−ξz)(v/Q_z(c, d))^s dz = ĕ(ξd/c)·|c|^{−2s}·(2π/Γ(s))(2π|ξ|)^{s−1}·v·K_{s−1}(4π|ξ|v)`, by round 389's
  `height_cpow_eq`, the shift `z ↦ z − d/c` and the scaling `z ↦ vz`.
* **The Fourier coefficient** (`cuspSm`, a definition; **`hasSum_integral_ebr_eisTerm_c`** and
  **`integral_ebr_eis1_fundP3`**, with `ebr_period` and `ebr_neg_mul_add_period`): `ĕ(−mz/9)` is periodic
  under `3ℤ[ω]` (round 363's `ebr_shift` with `q = 1`), so round 389's tiling applies with the character. For
  `m = δ₃x ≠ 0`, `Re s > 2` and `v > 0`,
  `∫_{3P} ĕ(−mz/9)E(z, v; s) dz = v^s·∫_{3P} ĕ(−mz/9) dz + (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·D_m(s)`,
  with `D_m(s) = Σ_c S_m(c)N(c)^{−s}` and `S_m(c) = Σ_{d mod 3c} (c/d)₃·ĕ((m/9)(d/c))`.
-/

open MeasureTheory Set Filter Asymptotics Complex NumberField Ideal
open scoped Topology ComplexConjugate RealInnerProductSpace

noncomputable section

namespace Eis

theorem measurable_ebr : Measurable ebr := by
  unfold ebr
  fun_prop

/-- `ĕ(−ξz)·e^{−t|z|²}` as a Gaussian with a linear term in `⟨2ξ̄, z⟩`. -/
theorem ebr_neg_mul_exp (ξ z : ℂ) (t : ℝ) :
    ebr (-(ξ * z)) * cexp (-((t : ℂ) * (Complex.normSq z : ℂ))) =
      cexp (-(t : ℂ) * (‖z‖ : ℂ) ^ 2 + (-2 * Real.pi * I) * ((⟪2 * conj ξ, z⟫ : ℝ) : ℂ)) := by
  unfold ebr
  rw [← Complex.exp_add]
  congr 1
  have h1 : ((Complex.normSq z : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  have h2 : (⟪2 * conj ξ, z⟫ : ℝ) = 2 * (ξ * z).re := by
    rw [Complex.inner]
    simp [Complex.mul_re, map_mul]
    ring
  rw [h1, h2, Complex.neg_re]
  push_cast
  ring

/-- **The Gaussian on `ℂ` against a character**: `∫_ℂ ĕ(−ξz)e^{−t|z|²} dz = (π/t)e^{−4π²|ξ|²/t}` for `t > 0`
(Mathlib's `integral_cexp_neg_mul_sq_norm_add`). -/
theorem integral_ebr_gauss (ξ : ℂ) {t : ℝ} (ht : 0 < t) :
    ∫ z : ℂ, ebr (-(ξ * z)) * cexp (-((t : ℂ) * (Complex.normSq z : ℂ))) =
      (Real.pi / t : ℂ) * cexp (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / t : ℝ)) := by
  simp_rw [ebr_neg_mul_exp]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using ht), Complex.finrank_real_complex]
  have hn : ‖(2 : ℂ) * conj ξ‖ = 2 * ‖ξ‖ := by rw [norm_mul, Complex.norm_conj]; norm_num
  rw [hn]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  congr 1
  · norm_num
  · congr 1
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- `r^{−s} = Γ(s)⁻¹∫_0^∞ t^{s−1}e^{−rt} dt` for `r > 0` and `Re s > 0` (Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`). -/
theorem cpow_neg_eq_integral {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    ((r : ℝ) : ℂ) ^ (-s) =
      (Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * t)) := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr]
  have hG := Complex.Gamma_ne_zero_of_re_pos hs
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  field_simp

/-- The integrand of the Fubini step: `ĕ(−ξz)·t^{s−1}e^{−(1 + |z|²)t}`. -/
def ftInt (ξ s : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  ebr (-(ξ * z)) * ((t : ℂ) ^ (s - 1) * cexp (-(((1 + Complex.normSq z : ℝ) : ℂ) * t)))

theorem ftInt_eq (ξ s : ℂ) (t : ℝ) (z : ℂ) :
    ftInt ξ s t z = (t : ℂ) ^ (s - 1) * cexp (-(t : ℂ)) *
      (ebr (-(ξ * z)) * cexp (-((t : ℂ) * (Complex.normSq z : ℂ)))) := by
  unfold ftInt
  have : cexp (-(((1 + Complex.normSq z : ℝ) : ℂ) * t)) =
      cexp (-(t : ℂ)) * cexp (-((t : ℂ) * (Complex.normSq z : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  ring

theorem measurable_ftInt (ξ s : ℂ) : Measurable (Function.uncurry (ftInt ξ s)) := by
  have h1 : Measurable fun p : ℝ × ℂ => ebr (-(ξ * p.2)) := measurable_ebr.comp (by fun_prop)
  have h2 : Measurable fun p : ℝ × ℂ => (p.1 : ℂ) ^ (s - 1) :=
    (Complex.measurable_ofReal.comp measurable_fst).pow_const _
  have h3 : Measurable fun p : ℝ × ℂ => cexp (-(((1 + Complex.normSq p.2 : ℝ) : ℂ) * p.1)) := by
    fun_prop
  exact h1.mul (h2.mul h3)

theorem norm_ftInt (ξ s : ℂ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖ftInt ξ s t z‖ = t ^ (s.re - 1) * Real.exp (-t) * Real.exp (-t * ‖z‖ ^ 2) := by
  rw [ftInt_eq, norm_mul, norm_mul, norm_mul, norm_ebr, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.normSq_eq_norm_sq]
  ring_nf

/-- **The Fubini step is justified** for `Re s > 1`. -/
theorem integrable_ftInt (ξ : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (Function.uncurry (ftInt ξ s))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℂ)) := by
  rw [integrable_prod_iff (measurable_ftInt ξ s).aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 0 < t) => ?_
    have e : (fun z => Function.uncurry (ftInt ξ s) (t, z)) = fun z => (t : ℂ) ^ (s - 1) * cexp (-(t : ℂ)) *
        cexp (-(t : ℂ) * (‖z‖ : ℂ) ^ 2 + (-2 * Real.pi * I) * ((⟪2 * conj ξ, z⟫ : ℝ) : ℂ)) := by
      funext z
      rw [Function.uncurry_apply_pair, ftInt_eq, ebr_neg_mul_exp]
    rw [e]
    exact (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) _ _).const_mul _
  · have e : ∀ t ∈ Ioi (0 : ℝ), ∫ z, ‖Function.uncurry (ftInt ξ s) (t, z)‖ =
        Real.pi * (Real.exp (-t) * t ^ (s.re - 1 - 1)) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      simp_rw [Function.uncurry_apply_pair, norm_ftInt ξ s ht']
      rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht',
        Complex.finrank_real_complex, Real.rpow_sub_one ht'.ne' (s.re - 1)]
      norm_num
      field_simp
    exact IntegrableOn.congr_fun
      ((Real.GammaIntegral_convergent (s := s.re - 1) (by linarith)).const_mul Real.pi)
      (fun t ht => (e t ht).symm) measurableSet_Ioi

/-- **The planar Fourier transform of `(1 + |z|²)^{−s}`**: for `ξ ≠ 0` and `Re s > 1`,
`∫_ℂ ĕ(−ξz)(1 + |z|²)^{−s} dz = (2π/Γ(s))·(2π|ξ|)^{s−1}·K_{s−1}(4π|ξ|)`. -/
theorem integral_ebr_inv_cpow {ξ : ℂ} (hξ : ξ ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    ∫ z : ℂ, ebr (-(ξ * z)) * ((1 + Complex.normSq z : ℝ) : ℂ) ^ (-s) =
      2 * Real.pi / Gamma s * ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1) *
        besselK (s - 1) (4 * Real.pi * ‖ξ‖) := by
  have hs0 : 0 < s.re := by linarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hs0
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * Real.pi * ‖ξ‖ := ⟨_, rfl⟩
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have ha0 : 0 < a := by rw [ha]; positivity
  -- the Gamma integral
  have h1 : ∀ z : ℂ, ebr (-(ξ * z)) * ((1 + Complex.normSq z : ℝ) : ℂ) ^ (-s) =
      (Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), ftInt ξ s t z := by
    intro z
    have hr : (0 : ℝ) < 1 + Complex.normSq z := by
      have := Complex.normSq_nonneg z
      linarith
    rw [cpow_neg_eq_integral hr hs0, mul_left_comm, ← integral_const_mul]
    rfl
  simp_rw [h1]
  rw [integral_const_mul, ← integral_integral_swap (integrable_ftInt ξ hs)]
  -- the inner integrals
  have h3 : ∀ t ∈ Ioi (0 : ℝ), ∫ z, ftInt ξ s t z =
      Real.pi * ((t : ℂ) ^ (s - 1 - 1) * ((bkK (2 * a) (a⁻¹ * t) : ℝ) : ℂ)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    simp_rw [ftInt_eq]
    rw [integral_const_mul, integral_ebr_gauss ξ ht']
    have hb : ((bkK (2 * a) (a⁻¹ * t) : ℝ) : ℂ) =
        cexp (-(t : ℂ)) * cexp (-((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / t : ℝ) : ℂ)) := by
      have hξc : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hξ0.ne'
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      unfold bkK
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      rw [ha]
      push_cast
      field_simp
      ring
    have hc : (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 1) / t := by
      rw [Complex.cpow_sub _ _ htc, Complex.cpow_one]
    rw [hb, hc]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  -- the Mellin transform of the kernel
  have h4 : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) * ((bkK (2 * a) (a⁻¹ * t) : ℝ) : ℂ) =
      (a : ℂ) ^ (s - 1) * (2 * besselK (s - 1) (2 * a)) := by
    have h := mellin_comp_mul_left (fun t => ((bkK (2 * a) t : ℝ) : ℂ)) (s - 1) (inv_pos.2 ha0)
    unfold mellin at h
    simp only [smul_eq_mul] at h
    rw [h]
    have harg : (a : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ha0.le]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
    unfold besselK mellin
    simp only [smul_eq_mul]
    ring
  rw [h4, show 2 * a = 4 * Real.pi * ‖ξ‖ by rw [ha]; ring, ha]
  field_simp

/-- **`K_ν(x)` is entire in `ν`** for `x > 0` (Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp`, with
the bounds of round 361's `mellinConvergent_bkK`). -/
theorem differentiable_besselK {x : ℝ} (hx : 0 < x) : Differentiable ℂ fun ν => besselK ν x := by
  intro ν
  have hx2 : 0 < x / 2 := by positivity
  unfold besselK
  refine DifferentiableAt.const_mul ?_ _
  refine mellin_differentiableAt_of_isBigO_rpow_exp hx2 (locInt_bkK x) ?_ ?_ (b := ν.re - 1)
    (by linarith)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (bkK_pos x t).le, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact bkK_le_top hx ht
  · have h1 := (isLittleO_exp_neg_mul_rpow_atTop hx2 (ν.re - 1)).comp_tendsto tendsto_inv_nhdsGT_zero
    have h2 : ((fun x : ℝ => x ^ (ν.re - 1)) ∘ fun t : ℝ => t⁻¹) =ᶠ[𝓝[>] 0]
        fun t => t ^ (-(ν.re - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_apply]
      rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]
    refine IsBigO.trans ?_ (h1.isBigO.congr' EventuallyEq.rfl h2)
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (bkK_pos x t).le, one_mul, Function.comp_apply,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact bkK_le_bot hx ht

/-- **The Fourier integral of one term**: for `c ≠ 0`, `v > 0`, `ξ ≠ 0` and `Re s > 1`,
`∫_ℂ ĕ(−ξz)(v/Q_z(c, d))^s dz = ĕ(ξd/c)·|c|^{−2s}·(2π/Γ(s))·(2π|ξ|)^{s−1}·v·K_{s−1}(4π|ξ|v)`. -/
theorem integral_ebr_height_cpow {c : ℂ} (hc : c ≠ 0) (d : ℂ) {v : ℝ} (hv : 0 < v) {ξ : ℂ}
    (hξ : ξ ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    ∫ z : ℂ, ebr (-(ξ * z)) * ((v / uhsDen c d z v : ℝ) : ℂ) ^ s =
      ebr (ξ * (d / c)) * ((Complex.normSq c : ℝ) : ℂ) ^ (-s) *
        (2 * Real.pi / Gamma s * ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1)) * (v : ℂ) *
          besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v) := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  simp_rw [height_cpow_eq hc d _ hv s]
  -- the shift `w = z + d/c`
  have hshift : ∫ z : ℂ, ebr (-(ξ * z)) * (((v / Complex.normSq c : ℝ) : ℂ) ^ s *
      ((Complex.normSq (z + d / c) + v ^ 2 : ℝ) : ℂ) ^ (-s)) =
      ((v / Complex.normSq c : ℝ) : ℂ) ^ s * ebr (ξ * (d / c)) *
        ∫ w : ℂ, ebr (-(ξ * w)) * ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun w : ℂ => ebr (-(ξ * (w - d / c))) * (((v / Complex.normSq c : ℝ) : ℂ) ^ s *
        ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s))) (d / c)
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [show -(ξ * (w - d / c)) = -(ξ * w) + ξ * (d / c) by ring, ebr_add]
    ring
  rw [hshift]
  -- the scaling `w = v·y`
  have hscale : ∫ w : ℂ, ebr (-(ξ * w)) * ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s) =
      ((v ^ 2 : ℝ) : ℂ) * ((v ^ 2 : ℝ) : ℂ) ^ (-s) *
        ∫ y : ℂ, ebr (-((ξ * v) * y)) * ((1 + Complex.normSq y : ℝ) : ℂ) ^ (-s) := by
    have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure ℂ))
      (fun w : ℂ => ebr (-(ξ * w)) * ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s)) v (hR := hv.le)
    rw [Complex.finrank_real_complex] at h
    have e : ∀ y : ℂ, ebr (-(ξ * (v • y))) * ((Complex.normSq (v • y) + v ^ 2 : ℝ) : ℂ) ^ (-s) =
        ((v ^ 2 : ℝ) : ℂ) ^ (-s) * (ebr (-((ξ * v) * y)) * ((1 + Complex.normSq y : ℝ) : ℂ) ^ (-s)) := by
      intro y
      rw [Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal,
        show v * v * Complex.normSq y + v ^ 2 = v ^ 2 * (1 + Complex.normSq y) by ring,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity)
          (by have := Complex.normSq_nonneg y; linarith),
        show ξ * ((v : ℂ) * y) = (ξ * v) * y by ring]
      ring
    simp_rw [e] at h
    rw [integral_const_mul] at h
    have hv2 : ((v ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (v ^ 2 : ℝ) ≠ 0)
    calc ∫ w : ℂ, ebr (-(ξ * w)) * ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s)
        = ((v ^ 2 : ℝ) : ℂ) * (((v ^ 2)⁻¹ : ℝ) • ∫ w : ℂ, ebr (-(ξ * w)) *
            ((Complex.normSq w + v ^ 2 : ℝ) : ℂ) ^ (-s)) := by
          rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hv2, one_mul]
      _ = _ := by rw [← h]; ring
  rw [hscale, integral_ebr_inv_cpow (mul_ne_zero hξ (by exact_mod_cast hv.ne')) hs]
  have hn : ‖ξ * (v : ℂ)‖ = ‖ξ‖ * v := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
  rw [hn]
  -- the powers
  have key : ((v / Complex.normSq c : ℝ) : ℂ) ^ s * (((v ^ 2 : ℝ) : ℂ) * ((v ^ 2 : ℝ) : ℂ) ^ (-s)) *
      ((2 * Real.pi * (‖ξ‖ * v) : ℝ) : ℂ) ^ (s - 1) =
      ((Complex.normSq c : ℝ) : ℂ) ^ (-s) * ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) := by
    have hp : (0 : ℝ) < 2 * Real.pi * ‖ξ‖ := by positivity
    rw [cpow_ofReal_eq_exp (div_pos hv hN), cpow_ofReal_eq_exp (pow_pos hv 2),
      cpow_ofReal_eq_exp (by positivity : (0 : ℝ) < 2 * Real.pi * (‖ξ‖ * v)), cpow_ofReal_eq_exp hN,
      cpow_ofReal_eq_exp hp, Real.log_div hv.ne' hN.ne', Real.log_pow,
      show 2 * Real.pi * (‖ξ‖ * v) = (2 * Real.pi * ‖ξ‖) * v by ring, Real.log_mul hp.ne' hv.ne']
    have hv' : (v : ℂ) = Complex.exp (Real.log v) := by
      rw [← Complex.ofReal_exp, Real.exp_log hv]
    have hv2 : ((v ^ 2 : ℝ) : ℂ) = Complex.exp (Real.log v * 2) := by
      rw [Complex.ofReal_pow, hv', ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hv2, hv', ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show 4 * Real.pi * (‖ξ‖ * v) = 4 * Real.pi * ‖ξ‖ * v by ring]
  linear_combination (ebr (ξ * (d / c)) * (2 * Real.pi / Gamma s) *
    besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v)) * key

/-! ### The Fourier coefficients of `E_s` -/

/-- **The character is periodic under `3ℤ[ω]`** at frequencies in `δ₃ℤ[ω]`:
`ĕ(σ(δ₃x)·σ(3u)/9) = 1` (round 363's `ebr_shift` with `q = 1`). -/
theorem ebr_period (x u : 𝓞 K) : ebr (σO (δ3 * x) * σO (3 * u) / 9) = 1 := by
  have h := ebr_shift 1 (-u) x
  rw [ψc_one] at h
  have e : σO (δ3 ^ 2 * -u) / σO 1 = σO (3 * u) := by
    rw [map_one, div_one, δ3_sq]
    congr 1
    ring
  rw [e] at h
  exact h

theorem ebr_neg_mul_add_period (x u : 𝓞 K) (z : ℂ) :
    ebr (-(σO (δ3 * x) / 9 * (z + σO (3 * u)))) = ebr (-(σO (δ3 * x) / 9 * z)) := by
  have h := ebr_period x (-u)
  rw [show -(σO (δ3 * x) / 9 * (z + σO (3 * u))) =
      -(σO (δ3 * x) / 9 * z) + σO (δ3 * x) * σO (3 * -u) / 9 by
    rw [mul_neg, map_neg]; ring, ebr_add, h, mul_one]

open Classical in
/-- **The twisted sums of the character over the classes modulo `3c`**:
`S_m(c) = Σ_{d mod 3c} (c/d)₃·ĕ((m/9)·(d/c))` over the classes of the `d` with `(c, d)` a bottom row. -/
def cuspSm (m c : 𝓞 K) : ℂ :=
  ∑' r : 𝓞 K ⧸ span {3 * c},
    if BRow (c, repQ (3 * c) r) then
      σO (cub c (span {repQ (3 * c) r})) * ebr (σO m / 9 * (σO (repQ (3 * c) r) / σO c))
    else 0

open Classical in
/-- **The sum over `d` of the twisted integrals over `3P`**: for `m = δ₃x ≠ 0`, `c ≠ 0`, `v > 0` and
`Re s > 1`,
`Σ_d ∫_{3P} ĕ(−mz/9)·(term at (c, d)) dz = S_m(c)·N(c)^{−s}·(2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)`. -/
theorem hasSum_integral_ebr_eisTerm_c {x : 𝓞 K} (hx : x ≠ 0) {c : 𝓞 K} (hc : c ≠ 0) {v : ℝ} (hv : 0 < v)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun d : 𝓞 K => ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * eisTerm s (z, v) (c, d))
      (cuspSm (δ3 * x) c * (((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) *
        (2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1)) * (v : ℂ) *
          besselK (s - 1) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v))) := by
  have := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  set ξ : ℂ := σO (δ3 * x) / 9 with hξdef
  have hξ : ξ ≠ 0 := by
    rw [hξdef]
    exact div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
  set F := fun d : 𝓞 K => ∫ z in fundP3, ebr (-(ξ * z)) * eisTerm s (z, v) (c, d) with hF
  set G := fun d : 𝓞 K =>
    ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO c) (σO d) z v) ^ s.re) with hG
  have hGtop : ∑' d, G d ≠ ⊤ := by
    rw [hG, tsum_lintegral_height_c hc hv hs]
    exact ENNReal.ofReal_ne_top
  have hB : ∀ d, ‖F d‖ ≤ (G d).toReal := by
    intro d
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.ne_top_of_tsum_ne_top hGtop d) (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_))
    rw [norm_mul, norm_ebr, one_mul]
    exact norm_eisTerm_le_height s (p := (z, v)) hv (c, d)
  have hsum : Summable F := Summable.of_norm_bounded (ENNReal.summable_toReal hGtop) hB
  have hsum' : Summable fun p => F (resClassEquiv hc p) := (resClassEquiv hc).summable_iff.2 hsum
  rw [hsum.hasSum_iff, ← (resClassEquiv hc).tsum_eq, hsum'.tsum_prod' hsum'.prod_factor, tsum_fintype]
  unfold cuspSm
  rw [tsum_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  set f : ℂ → ℂ := fun z => ebr (-(ξ * z)) * eisTerm s (z, v) (c, repQ (3 * c) r) with hf_def
  have hf : Integrable f := by
    have hm : Measurable fun z : ℂ => ebr (-(ξ * z)) := measurable_ebr.comp (by fun_prop)
    have hi : Integrable fun z : ℂ => eisTerm s (z, v) (c, repQ (3 * c) r) := by
      unfold eisTerm
      split_ifs
      · exact (integrable_height_cpow (σO_ne_zero hc) _ hv hs).const_mul _
      · exact integrable_zero _ _ _
    refine hi.bdd_mul (c := 1) hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [norm_ebr]
  have h1 : ∀ u : 𝓞 K, F (resClassEquiv hc (r, u)) = ∫ y in fundP3, f (y - σO (3 * -u)) := by
    intro u
    simp only [hF, resClassEquiv_apply, hf_def]
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [eisTerm_add, mul_neg, map_neg, sub_neg_eq_add, hξdef, ebr_neg_mul_add_period]
  have h2 := (Equiv.neg (𝓞 K)).tsum_eq (fun t => ∫ y in fundP3, f (y - σO (3 * t)))
  simp only [Equiv.neg_apply] at h2
  rw [tsum_congr h1, h2, ← integral_tile3 hf]
  simp only [hf_def]
  unfold eisTerm
  split_ifs with hb
  · simp_rw [mul_left_comm (ebr _)]
    rw [integral_const_mul, integral_ebr_height_cpow (σO_ne_zero hc) _ hv hξ hs]
    ring
  · simp

open Classical in
/-- **The `m`-th Fourier coefficient of `E_s`**, for `m = δ₃x ≠ 0`, `Re s > 2` and `v > 0`:
`∫_{3P} ĕ(−mz/9)E(z, v; s) dz = v^s·∫_{3P} ĕ(−mz/9) dz + (2π/Γ(s))(2π|m|/9)^{s−1}·v·K_{s−1}(4π|m|v/9)·D_m(s)`,
with `D_m(s) = Σ_c S_m(c)N(c)^{−s}`. -/
theorem integral_ebr_eis1_fundP3 {x : 𝓞 K} (hx : x ≠ 0) {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * eis1 s (z, v) =
      ((v : ℝ) : ℂ) ^ s * (∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z))) +
        2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) *
          besselK (s - 1) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v) *
            ∑' c : 𝓞 K, cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  set ξ : ℂ := σO (δ3 * x) / 9 with hξdef
  have hfin := tsum_lintegral_eisTerm_ne_top hs hv
  have hm : Measurable fun z : ℂ => ebr (-(ξ * z)) := measurable_ebr.comp (by fun_prop)
  set I := fun cd : 𝓞 K × 𝓞 K => ∫ z in fundP3, ebr (-(ξ * z)) * eisTerm s (z, v) cd with hI
  have hfin' : ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3, ‖ebr (-(ξ * z)) * eisTerm s (z, v) cd‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun cd => lintegral_mono fun z => ?_)
    rw [enorm_mul, ← ofReal_norm (ebr _), norm_ebr, ENNReal.ofReal_one, one_mul]
  have hI_le : ∀ cd, ‖I cd‖ ≤
      (∫⁻ z in fundP3, ‖ebr (-(ξ * z)) * eisTerm s (z, v) cd‖ₑ).toReal := by
    intro cd
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp_rw [ofReal_norm]
  have hIsum : Summable I := Summable.of_norm_bounded (ENNReal.summable_toReal hfin') hI_le
  have h1 : ∫ z in fundP3, ebr (-(ξ * z)) * eis1 s (z, v) = ∑' cd, I cd := by
    have e : ∀ z, ebr (-(ξ * z)) * eis1 s (z, v) = ∑' cd, ebr (-(ξ * z)) * eisTerm s (z, v) cd := by
      intro z
      unfold eis1
      rw [tsum_mul_left]
    simp_rw [e]
    exact integral_tsum (fun cd => (hm.mul (measurable_eisTerm s v cd)).aestronglyMeasurable) hfin'
  set J := fun c : 𝓞 K => ∑' d : 𝓞 K, I (c, d) with hJ
  have hJsum : Summable J := hIsum.prod
  have hJ0 : J 0 = ((v : ℝ) : ℂ) ^ s * (∫ z in fundP3, ebr (-(ξ * z))) := by
    have e : ∀ d : 𝓞 K, I (0, d) = if d = 1 then ∫ z in fundP3, ebr (-(ξ * z)) * ((v : ℝ) : ℂ) ^ s
        else 0 := by
      intro d
      simp only [hI, eisTerm_zero_fst]
      split_ifs <;> simp
    simp only [hJ, e, tsum_ite_eq]
    rw [integral_mul_const]
    ring
  have hJc : ∀ c : 𝓞 K, c ≠ 0 → J c = 2 * Real.pi / Gamma s *
      ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ξ‖ * v) *
        (cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) := by
    intro c hc
    show ∑' d : 𝓞 K, ∫ z in fundP3, ebr (-(ξ * z)) * eisTerm s (z, v) (c, d) = _
    rw [(hasSum_integral_ebr_eisTerm_c hx hc hv (by linarith)).tsum_eq]
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

end Eis

end

#print axioms Eis.ebr_neg_mul_exp
#print axioms Eis.integral_ebr_gauss
#print axioms Eis.cpow_neg_eq_integral
#print axioms Eis.ftInt_eq
#print axioms Eis.measurable_ftInt
#print axioms Eis.norm_ftInt
#print axioms Eis.integrable_ftInt
#print axioms Eis.integral_ebr_inv_cpow
#print axioms Eis.differentiable_besselK
#print axioms Eis.integral_ebr_height_cpow
#print axioms Eis.measurable_ebr
#print axioms Eis.ebr_period
#print axioms Eis.ebr_neg_mul_add_period
#print axioms Eis.hasSum_integral_ebr_eisTerm_c
#print axioms Eis.integral_ebr_eis1_fundP3
