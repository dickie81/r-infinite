import Mathlib

/-! # Separating variables with one-dimensional Mellin transforms (round 302)

S4 of round 291's plan, part 2: the analysis that the companion paper's proof of its Proposition 4.5
takes from its Appendix B (Lemma B.2, which rests on Lemma B.1). There a two-variable kernel depending
on the row is separated by a two-dimensional Mellin transform. In Proposition 4.5 the kernel has the product form
`W₀(ρx₁)·conj W₀(ρx₂)·𝓕Φ(A/(x₁x₂))`. This file separates each factor with a one-dimensional
Mellin transform instead and records the resulting bounds.

* **Fourier inversion in logarithmic coordinates** (`log_fourier_inversion`): `h(log y) =
  ∫ 𝓕h(t)·y^{2πit} dt` for Schwartz `h`. Hence a smooth `W` vanishing outside `[α, β]`, `α > 0`, is
  `W(y) = ∫ c(t)·y^{2πit} dt` on `y > 0` with `c` Schwartz (`mellin_of_compact`).
* **The dual weight** (`mellin_of_dual`): if `G` is smooth with bounded derivatives and vanishes on
  `[R, ∞)`, then for `σ > 0`, `G(√y) = ∫ c(t)·y^{−σ+2πit} dt` on `y > 0` with `c` Schwartz. The
  factor `e^{σv}` makes `v ↦ e^{σv}·G(e^{v/2})` Schwartz although `G` need not vanish at `0`
  (`schwartz_exp_comp`, by Mathlib's Faà di Bruno and Leibniz bounds); `y^{−σ}` undoes it.
* **Test functions** `U_s(x) = V(x)·x^s` for a fixed smooth `V` with compact support in `(0, ∞)`:
  smooth (`testFun_contDiff`), with `‖U_s^{(j)}‖ ≤ C·(1+|s|)^J` for `j ≤ J` uniformly in `|Re s| ≤ A`
  (`testFun_bound`), from `(x^s)^{(m)} = (∏_{i<m}(s − i))·x^{s−m}` (`iteratedDeriv_ofReal_cpow`).
* **Cauchy–Schwarz** (`sq_integral_mul_le`, `sum_norm_integral_sq_le`):
  `Σ_r ‖∫ c(t)·g_r(t) dt‖² ≤ (∫‖c‖)·M·∫‖c(t)‖(1+|t|)^k dt` when `Σ_r ‖g_r(t)‖² ≤ M(1+|t|)^k`.
* **Dilated weights** (`dilated_meanSquare`): if the row sums `S_r(U) = Σ_n a_r(n)·U(x_n)` satisfy
  `Σ_r ‖S_r(U)‖² ≤ M·N²` for every smooth `U` supported in `tsupport V` with its first `J`
  derivatives bounded by `N`, then the weights `W₀(ρ_r x)·x^s` with row-dependent `ρ_r ∈ [ρ₀, ρ₁]`
  satisfy `Σ_r ‖S_r(W₀(ρ_r ·)·(·)^s)‖² ≤ K·M·(1+|s|)^{2J}`, with `K` independent of the rows, the
  columns, the coefficients, the points, `M`, the dilations and `s`.
* **The bilinear form with the dual kernel** (`bilinear_dual_bound`): under the same hypothesis,
  `|Σ_r w_r Σ_{n₁,n₂} a_r(n₁)·conj a_r(n₂)·W₀(ρ_r x_{n₁})·conj W₀(ρ_r x_{n₂})·G(√(A_r/(x_{n₁}x_{n₂})))|
  ≤ K·A_min^{−σ}·M` for `|w_r| ≤ 1` and `A_r ≥ A_min > 0`, with `K` independent of the same data
  and of `w`, `A`. The cost of the dual weight's `y^{−σ}` is the factor `A_min^{−σ}`.

The paper bounds the contribution of its kernels through their `C^{2m+4}` norms, which tracks the
dependence on the weight `W`. Here the constants depend on `W₀`, `V`, `G`, `σ`, `J` and `[ρ₀, ρ₁]`
through the Mellin coefficients. That suffices for round 288's `MeanSquare`, whose constant may
depend on the weight.
-/

open Complex MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace ContDiff SchwartzMap Nat ComplexConjugate

noncomputable section

namespace MellinSep

/-! ### Fourier inversion in logarithmic coordinates -/

/-- `y^{2πit} = e(t·log y)` for `y > 0`. -/
theorem cpow_eq_fourierChar (y t : ℝ) (hy : 0 < y) :
    ((y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) = (𝐞 (t * Real.log y) : ℂ) := by
  rw [Real.fourierChar_apply, Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    ← Complex.ofReal_log hy.le]
  congr 1
  push_cast; ring

/-- **Fourier inversion in logarithmic coordinates**: for a Schwartz `h` on `ℝ` and `y > 0`,
`h(log y) = ∫ 𝓕h(t)·y^{2πit} dt`. -/
theorem log_fourier_inversion (h : 𝓢(ℝ, ℂ)) (y : ℝ) (hy : 0 < y) :
    h (Real.log y) = ∫ t : ℝ, 𝓕 (h : ℝ → ℂ) t * ((y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
  have h1 : 𝓕⁻ (𝓕 h) = h := FourierPair.fourierInv_fourier_eq h
  have h2 := congrArg (fun g : 𝓢(ℝ, ℂ) => g (Real.log y)) h1
  rw [← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [cpow_eq_fourierChar y t hy, Circle.smul_def, smul_eq_mul, mul_comm, SchwartzMap.fourier_coe]
  congr 2
  rw [RCLike.inner_apply', conj_trivial]

/-- **Mellin separation of a compactly supported weight**: for `W` smooth, vanishing outside `[α, β]`
with `0 < α`, there is a Schwartz `c` with `W(y) = ∫ c(t)·y^{2πit} dt` for `y > 0`. -/
theorem mellin_of_compact (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hs : ∀ x, x < α ∨ β < x → W x = 0) :
    ∃ c : 𝓢(ℝ, ℂ), ∀ y : ℝ, 0 < y →
      W y = ∫ t : ℝ, c t * ((y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
  set w : ℝ → ℂ := fun v => W (Real.exp v) with hw
  have hwc : ContDiff ℝ ∞ w := hW.comp Real.contDiff_exp
  have hws : HasCompactSupport w := by
    refine HasCompactSupport.intro (isCompact_Icc (a := Real.log α) (b := max (Real.log β)
      (Real.log α))) fun v hv => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hv
    apply hs
    rcases hv with hv | hv
    · left
      have := Real.exp_lt_exp.2 hv
      rwa [Real.exp_log hα] at this
    · right
      have h1 : Real.log β < v := lt_of_le_of_lt (le_max_left _ _) hv
      by_cases hβ : 0 < β
      · have := Real.exp_lt_exp.2 h1
        rwa [Real.exp_log hβ] at this
      · exact lt_of_le_of_lt (not_lt.1 hβ) (Real.exp_pos v)
  set h : 𝓢(ℝ, ℂ) := hws.toSchwartzMap hwc
  refine ⟨𝓕 h, fun y hy => ?_⟩
  have e := log_fourier_inversion h y hy
  have e2 : h (Real.log y) = W y := by
    show W (Real.exp (Real.log y)) = W y
    rw [Real.exp_log hy]
  rw [← e2, e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  rw [SchwartzMap.fourier_coe]


/-! ### The dual weight -/

/-- `|v|^k e^{σv}` is bounded on `(-∞, v₁]` when `σ > 0`. -/
theorem abs_pow_mul_exp_le {σ : ℝ} (hσ : 0 < σ) (v1 : ℝ) (k : ℕ) :
    ∃ B, ∀ v, v ≤ v1 → |v| ^ k * Real.exp (σ * v) ≤ B := by
  refine ⟨k ! / σ ^ k + |v1| ^ k * Real.exp (σ * v1), fun v hv => ?_⟩
  rcases le_or_gt v 0 with h0 | h0
  · have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg hσ.le (abs_nonneg v)) k
    have h2 : Real.exp (σ * v) * Real.exp (σ * |v|) = 1 := by
      rw [← Real.exp_add, abs_of_nonpos h0, mul_neg, add_neg_cancel, Real.exp_zero]
    have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    have h3 : |v| ^ k * Real.exp (σ * v) ≤ k ! / σ ^ k := by
      rw [mul_pow, div_le_iff₀ hk] at h1
      rw [le_div_iff₀ (pow_pos hσ k)]
      calc |v| ^ k * Real.exp (σ * v) * σ ^ k = (σ ^ k * |v| ^ k) * Real.exp (σ * v) := by ring
        _ ≤ (Real.exp (σ * |v|) * k !) * Real.exp (σ * v) := by gcongr
        _ = k ! := by
          rw [mul_comm (Real.exp _) _, mul_assoc, mul_comm (Real.exp (σ * |v|)), h2, mul_one]
    have h4 : 0 ≤ |v1| ^ k * Real.exp (σ * v1) := by positivity
    linarith
  · have h1 : |v| ≤ |v1| := by rw [abs_of_pos h0]; exact hv.trans (le_abs_self v1)
    have h2 : |v| ^ k * Real.exp (σ * v) ≤ |v1| ^ k * Real.exp (σ * v1) := by
      gcongr
    have h3 : 0 ≤ (k ! : ℝ) / σ ^ k := by positivity
    linarith

theorem nat_le_infty (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top

/-- **Schwartz in logarithmic coordinates.** If `G` has bounded derivatives and vanishes on
`[R, ∞)`, then `v ↦ e^{σv}·G(e^{av})` is a Schwartz function for `σ, a > 0`. -/
theorem schwartz_exp_comp (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ n : ℕ, ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n G ρ‖ ≤ C) {R : ℝ}
    (hR : ∀ ρ, R ≤ ρ → G ρ = 0) {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    ∃ h : 𝓢(ℝ, ℂ), ∀ v, h v = Real.exp (σ * v) • G (Real.exp (a * v)) := by
  set f : ℝ → ℂ := fun v => Real.exp (σ * v) • G (Real.exp (a * v)) with hf
  have he1 : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (σ * v)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have he2 : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (a * v)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hGe : ContDiff ℝ ∞ (fun v : ℝ => G (Real.exp (a * v))) := hG.comp he2
  have hfs : ContDiff ℝ ∞ f := he1.smul hGe
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right R 1
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos hR'1
  set v1 := Real.log R' / a with hv1
  have hvan : ∀ v, v1 < v → f v = 0 := by
    intro v hv
    have h1 : Real.log R' < a * v := by
      have := (div_lt_iff₀ ha).1 hv; linarith
    have : R' < Real.exp (a * v) := by
      calc R' = Real.exp (Real.log R') := (Real.exp_log hR'0).symm
        _ < Real.exp (a * v) := Real.exp_lt_exp.2 h1
    simp only [hf, hR _ ((le_max_left R 1).trans this.le), smul_zero]
  choose C hC using hGb
  set K : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), |C i| with hKdef
  have hK : ∀ m i, i ≤ m → ∀ ρ, ‖iteratedFDeriv ℝ i G ρ‖ ≤ K m := by
    intro m i hi ρ
    calc ‖iteratedFDeriv ℝ i G ρ‖ ≤ C i := hC i ρ
      _ ≤ |C i| := le_abs_self _
      _ ≤ K m := Finset.single_le_sum (f := fun i => |C i|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hder : ∀ n, ∃ M, ∀ v, v ≤ v1 → ‖iteratedFDeriv ℝ n f v‖ ≤ M * Real.exp (σ * v) := by
    intro n
    refine ⟨∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * σ ^ i * ((n - i) ! * K (n - i) * (a * R') ^ (n - i)), fun v hv => ?_⟩
    have hexp : Real.exp (a * v) ≤ R' := by
      have : a * v ≤ Real.log R' := by
        have := (le_div_iff₀ ha).1 hv; linarith
      calc Real.exp (a * v) ≤ Real.exp (Real.log R') := Real.exp_le_exp.2 this
        _ = R' := Real.exp_log hR'0
    have hL := norm_iteratedFDeriv_smul_le he1 hGe v (nat_le_infty n)
    refine hL.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : ‖iteratedFDeriv ℝ i (fun v : ℝ => Real.exp (σ * v)) v‖ =
        σ ^ i * Real.exp (σ * v) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have h2 : ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖ ≤
        (n - i) ! * K (n - i) * (a * R') ^ (n - i) := by
      refine norm_iteratedFDeriv_comp_le (g := G) (f := fun v : ℝ => Real.exp (a * v)) hG he2
        (nat_le_infty (n - i)) v (fun j hj => hK _ _ hj _) (fun j hj1 hj2 => ?_)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), mul_pow]
      show a ^ j * Real.exp (a * v) ≤ a ^ j * R' ^ j
      gcongr
      calc Real.exp (a * v) ≤ R' := hexp
        _ = R' ^ 1 := (pow_one _).symm
        _ ≤ R' ^ j := pow_le_pow_right₀ hR'1 hj1
    rw [h1]
    calc (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ‖iteratedFDeriv ℝ (n - i) (fun v : ℝ => G (Real.exp (a * v))) v‖
        ≤ (n.choose i : ℝ) * (σ ^ i * Real.exp (σ * v)) *
          ((n - i) ! * K (n - i) * (a * R') ^ (n - i)) := by gcongr
      _ = _ := by ring
  refine ⟨⟨f, hfs, fun k n => ?_⟩, fun v => rfl⟩
  obtain ⟨M, hM⟩ := hder n
  obtain ⟨B, hB⟩ := abs_pow_mul_exp_le hσ v1 k
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB v1 le_rfl)
  refine ⟨|M| * B, fun v => ?_⟩
  rcases le_or_gt v v1 with hv | hv
  · have h1 := hM v hv
    have h2 := hB v hv
    rw [Real.norm_eq_abs]
    calc |v| ^ k * ‖iteratedFDeriv ℝ n f v‖ ≤ |v| ^ k * (|M| * Real.exp (σ * v)) := by
          gcongr; exact h1.trans (by gcongr; exact le_abs_self M)
      _ = |M| * (|v| ^ k * Real.exp (σ * v)) := by ring
      _ ≤ |M| * B := by gcongr
  · have hev : f =ᶠ[nhds v] fun _ => (0 : ℂ) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hv) fun w hw => hvan w hw
    have : iteratedFDeriv ℝ n f v = 0 := by
      rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]; rfl
    rw [this, norm_zero, mul_zero]
    positivity


/-- **Mellin separation of the dual weight.** If `G` has bounded derivatives and vanishes on
`[R, ∞)`, then for `σ > 0` there is a Schwartz `c` with `G(√y) = ∫ c(t)·y^{−σ+2πit} dt` for
`y > 0`. -/
theorem mellin_of_dual (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ n : ℕ, ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n G ρ‖ ≤ C) {R : ℝ}
    (hR : ∀ ρ, R ≤ ρ → G ρ = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c : 𝓢(ℝ, ℂ), ∀ y : ℝ, 0 < y →
      G (Real.sqrt y) =
        ∫ t : ℝ, c t * ((y : ℂ) ^ ((-σ : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
  obtain ⟨h, hh⟩ := schwartz_exp_comp G hG hGb hR hσ (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨𝓕 h, fun y hy => ?_⟩
  have e := log_fourier_inversion h y hy
  rw [hh] at e
  have hsq : Real.exp (1 / 2 * Real.log y) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; congr 1; ring
  have hpow : Real.exp (σ * Real.log y) = y ^ σ := by
    rw [Real.rpow_def_of_pos hy]; congr 1; ring
  rw [hsq, hpow] at e
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hone : (y : ℂ) ^ (-σ : ℂ) * ((y ^ σ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_add _ _ hy']; simp
  calc G (Real.sqrt y) = (y : ℂ) ^ (-σ : ℂ) * ((y ^ σ : ℝ) • G (Real.sqrt y)) := by
        rw [Complex.real_smul, ← mul_assoc, hone, one_mul]
    _ = ∫ t : ℝ, (y : ℂ) ^ (-σ : ℂ) *
          (𝓕 (h : ℝ → ℂ) t * (y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
        rw [e, integral_const_mul]
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [SchwartzMap.fourier_coe]
        rw [Complex.cpow_add _ _ hy']; ring


/-! ### Test functions `V(x)·x^s` -/

/-- Smoothness of `y ↦ y^s` at `x > 0`. -/
theorem contDiffAt_ofReal_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ s) x := by
  have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.2 hx.ne')
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * s)) x :=
    Complex.contDiff_exp.contDiffAt.comp x (hl.mul contDiffAt_const)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hy)), ← Complex.ofReal_log hy.le]

/-- **Iterated derivatives of `x ↦ x^s`** on `x > 0`: `(∏_{i<m} (s − i))·x^{s−m}`. -/
theorem iteratedDeriv_ofReal_cpow (s : ℂ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (fun y : ℝ => (y : ℂ) ^ s) x =
      (∏ i ∈ Finset.range m, (s - i)) * (x : ℂ) ^ (s - m) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hev : iteratedDeriv m (fun y : ℝ => (y : ℂ) ^ s) =ᶠ[nhds x]
        fun y : ℝ => (∏ i ∈ Finset.range m, (s - i)) * (y : ℂ) ^ (s - m) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq, Finset.prod_range_succ]
    by_cases hsm : s - m = 0
    · simp only [hsm, Complex.cpow_zero, mul_one, deriv_const, mul_zero, zero_mul]
    · rw [((hasDerivAt_ofReal_cpow_const hx.ne' hsm).const_mul _).deriv]
      push_cast
      rw [show s - ((m : ℂ) + 1) = s - m - 1 by ring]
      ring

theorem norm_prod_sub_le (s : ℂ) (m : ℕ) :
    ‖∏ i ∈ Finset.range m, (s - i)‖ ≤ ((1 + ‖s‖) * (1 + m)) ^ m := by
  rw [norm_prod]
  calc ∏ i ∈ Finset.range m, ‖s - i‖ ≤ ∏ _i ∈ Finset.range m, ((1 + ‖s‖) * (1 + m)) := by
        refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi => ?_
        have hi' : (i : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hi).le
        calc ‖s - i‖ ≤ ‖s‖ + ‖(i : ℂ)‖ := norm_sub_le _ _
          _ = ‖s‖ + i := by rw [Complex.norm_natCast]
          _ ≤ (1 + ‖s‖) * (1 + m) := by
            nlinarith [norm_nonneg s, mul_nonneg (norm_nonneg s) (Nat.cast_nonneg m)]
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

theorem rpow_le_exp_of_abs_log_le {x e L B : ℝ} (hx : 0 < x) (hL : |Real.log x| ≤ L)
    (hB : |e| ≤ B) (hL0 : 0 ≤ L) : x ^ e ≤ Real.exp (L * B) := by
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.2
  calc Real.log x * e ≤ |Real.log x * e| := le_abs_self _
    _ = |Real.log x| * |e| := abs_mul _ _
    _ ≤ L * B := mul_le_mul hL hB (abs_nonneg _) hL0

/-- The test functions `V(x)·x^s` are smooth. -/
theorem testFun_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hVp : tsupport V ⊆ Ioi 0) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : ℝ => V x * (x : ℂ) ^ s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport V
  · exact hV.contDiffAt.mul (contDiffAt_ofReal_cpow s (hVp hx))
  · have hev : (fun x : ℝ => V x * (x : ℂ) ^ s) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **Derivative bounds for the test functions `V(x)·x^s`**: for `|Re s| ≤ A` and `j ≤ J`, the
`j`-th derivative is `O((1 + |s|)^J)` uniformly in `s` and `x`. -/
theorem testFun_bound (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVp : tsupport V ⊆ Ioi 0) (A : ℝ) (J : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ A → ∀ j ≤ J, ∀ x : ℝ,
      ‖iteratedDeriv j (fun x : ℝ => V x * (x : ℂ) ^ s) x‖ ≤ C * (1 + ‖s‖) ^ J := by
  obtain ⟨KV, hKV0, hKV⟩ := hVc.exists_bound_iteratedFDeriv hV J
  obtain ⟨Lg, hLg⟩ := hVc.isCompact.exists_bound_of_continuousOn
    (Real.continuousOn_log.mono fun x hx => (ne_of_gt (hVp hx)))
  set L := max Lg 0 with hLdef
  set E := Real.exp (L * (A + J)) with hEdef
  refine ⟨2 ^ J * KV * (1 + J) ^ J * E, by positivity, fun s hs j hj x => ?_⟩
  by_cases hx : x ∈ tsupport V
  · have hx0 : (0 : ℝ) < x := hVp hx
    have hP : ContDiffOn ℝ ∞ (fun y : ℝ => (y : ℂ) ^ s) (Ioi 0) :=
      fun y hy => (contDiffAt_ofReal_cpow s hy).contDiffWithinAt
    have hlog : |Real.log x| ≤ L := by
      have := hLg x hx
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hPb : ∀ m ≤ J, ‖iteratedDeriv m (fun y : ℝ => (y : ℂ) ^ s) x‖ ≤
        (1 + ‖s‖) ^ J * ((1 + J) ^ J * E) := by
      intro m hm
      rw [iteratedDeriv_ofReal_cpow s m hx0, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have h1 := norm_prod_sub_le s m
      have h2 : x ^ (s - m).re ≤ E := by
        apply rpow_le_exp_of_abs_log_le hx0 hlog _ (le_max_right _ _)
        rw [Complex.sub_re, Complex.natCast_re]
        calc |s.re - m| ≤ |s.re| + |(m : ℝ)| := abs_sub _ _
          _ ≤ A + J := by
            rw [Nat.abs_cast]; gcongr
      have h3 : ((1 + ‖s‖) * (1 + m)) ^ m ≤ (1 + ‖s‖) ^ J * (1 + J) ^ J := by
        have ha : 1 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
        have hb : (1 : ℝ) + m ≤ 1 + J := by
          have : (m : ℝ) ≤ J := by exact_mod_cast hm
          linarith
        have hc : (1 : ℝ) ≤ 1 + J := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
        rw [mul_pow]
        exact mul_le_mul (pow_le_pow_right₀ ha hm)
          ((pow_le_pow_left₀ (by positivity) hb m).trans (pow_le_pow_right₀ hc hm))
          (by positivity) (by positivity)
      calc ‖∏ i ∈ Finset.range m, (s - i)‖ * x ^ (s - m).re
          ≤ ((1 + ‖s‖) * (1 + m)) ^ m * E := by gcongr
        _ ≤ (1 + ‖s‖) ^ J * (1 + J) ^ J * E := by gcongr
        _ = _ := by ring
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      ← iteratedFDerivWithin_of_isOpen j isOpen_Ioi hx0]
    refine (norm_iteratedFDerivWithin_mul_le hV.contDiffOn hP isOpen_Ioi.uniqueDiffOn hx0
      (nat_le_infty j)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i V (Ioi 0) x‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (fun y : ℝ => (y : ℂ) ^ s) (Ioi 0) x‖
        ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * KV * ((1 + ‖s‖) ^ J * ((1 + J) ^ J * E)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hx0,
            iteratedFDerivWithin_of_isOpen (j - i) isOpen_Ioi hx0,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := fun y : ℝ => (y : ℂ) ^ s)]
          have hi' : i ≤ J := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
          gcongr
          · exact hKV i hi' x
          · exact hPb _ ((Nat.sub_le j i).trans hj)
      _ = 2 ^ j * KV * ((1 + ‖s‖) ^ J * ((1 + J) ^ J * E)) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ J * KV * ((1 + ‖s‖) ^ J * ((1 + J) ^ J * E)) := by
          have h2J : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
          have hY : 0 ≤ (1 + ‖s‖) ^ J * ((1 + (J : ℝ)) ^ J * E) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2J hKV0) hY
      _ = _ := by ring
  · have hev : (fun x : ℝ => V x * (x : ℂ) ^ s) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity



/-! ### Cauchy–Schwarz for Mellin integrals -/

theorem one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (1 + a) ^ k ≤ 2 ^ k * (1 + a ^ k) := by
  rcases le_or_gt a 1 with h | h
  · calc (1 + a) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + a ^ k) := by
        have : 0 ≤ a ^ k := pow_nonneg ha k
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  · calc (1 + a) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + a ^ k) := by
        have : (0 : ℝ) ≤ 2 ^ k := by positivity
        nlinarith

/-- A Schwartz function against a polynomial weight is integrable. -/
theorem integrable_norm_mul_one_add_pow (c : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Integrable fun t : ℝ => ‖c t‖ * (1 + |t|) ^ k := by
  have h0 := c.integrable_pow_mul volume 0
  have hk := c.integrable_pow_mul volume k
  refine ((h0.add hk).const_mul (2 ^ k)).mono'
    (c.continuous.norm.mul ((continuous_const.add continuous_abs).pow k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply, pow_zero, one_mul, Real.norm_eq_abs]
  have h := one_add_pow_le |t| (abs_nonneg t) k
  have hc : 0 ≤ ‖c t‖ := norm_nonneg _
  calc ‖c t‖ * (1 + |t|) ^ k ≤ ‖c t‖ * (2 ^ k * (1 + |t| ^ k)) := by gcongr
    _ = 2 ^ k * (‖c t‖ + |t| ^ k * ‖c t‖) := by ring

/-- **Weighted Cauchy–Schwarz for integrals**: `(∫ w f)² ≤ (∫ w)·∫ w f²` for `w ≥ 0`. -/
theorem sq_integral_mul_le {w f : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t) (h1 : Integrable w)
    (h2 : Integrable fun t => w t * f t) (h3 : Integrable fun t => w t * f t ^ 2) :
    (∫ t, w t * f t) ^ 2 ≤ (∫ t, w t) * ∫ t, w t * f t ^ 2 := by
  have key : ∀ x : ℝ, 0 ≤ (∫ t, w t) * (x * x) + (-2 * ∫ t, w t * f t) * x +
      ∫ t, w t * f t ^ 2 := by
    intro x
    have e : (∫ t, w t) * (x * x) + (-2 * ∫ t, w t * f t) * x + ∫ t, w t * f t ^ 2 =
        ∫ t, w t * (f t - x) ^ 2 := by
      have hfun : (fun t => w t * (f t - x) ^ 2) =
          fun t => (w t * f t ^ 2 + (-2 * x) * (w t * f t)) + (x * x) * w t := by
        ext t; ring
      have i1 : ∫ t, (w t * f t ^ 2 + (-2 * x) * (w t * f t) + (x * x) * w t) =
          (∫ t, (w t * f t ^ 2 + (-2 * x) * (w t * f t))) + ∫ t, (x * x) * w t :=
        integral_add (h3.add (h2.const_mul _)) (h1.const_mul _)
      have i2 : ∫ t, (w t * f t ^ 2 + (-2 * x) * (w t * f t)) =
          (∫ t, w t * f t ^ 2) + ∫ t, (-2 * x) * (w t * f t) :=
        integral_add h3 (h2.const_mul _)
      rw [hfun, i1, i2, integral_const_mul, integral_const_mul]
      ring
    rw [e]
    exact integral_nonneg fun t => mul_nonneg (hw t) (sq_nonneg _)
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- **Cauchy–Schwarz over rows for Mellin integrals.** If `Σ_r ‖g_r(t)‖² ≤ M·(1+|t|)^k` for every
`t`, then `Σ_r ‖∫ c(t)·g_r(t) dt‖² ≤ (∫ ‖c‖)·M·∫ ‖c(t)‖·(1+|t|)^k dt` for Schwartz `c` and
continuous `g_r`. -/
theorem sum_norm_integral_sq_le {ι : Type*} (T : Finset ι) (c : 𝓢(ℝ, ℂ)) (g : ι → ℝ → ℂ)
    (hg : ∀ r ∈ T, Continuous (g r)) {M : ℝ} {k : ℕ}
    (hb : ∀ t, ∑ r ∈ T, ‖g r t‖ ^ 2 ≤ M * (1 + |t|) ^ k) :
    ∑ r ∈ T, ‖∫ t, c t * g r t‖ ^ 2 ≤ (∫ t, ‖c t‖) * (M * ∫ t, ‖c t‖ * (1 + |t|) ^ k) := by
  have hck := integrable_norm_mul_one_add_pow c k
  have hc0 : Integrable fun t => ‖c t‖ := c.integrable.norm
  have hgr : ∀ r ∈ T, ∀ t, ‖g r t‖ ^ 2 ≤ M * (1 + |t|) ^ k := fun r hr t =>
    le_trans (Finset.single_le_sum (f := fun r => ‖g r t‖ ^ 2) (fun _ _ => by positivity) hr)
      (hb t)
  have hI2 : ∀ r ∈ T, Integrable fun t => ‖c t‖ * ‖g r t‖ ^ 2 := by
    intro r hr
    refine (hck.const_mul M).mono'
      (c.continuous.norm.mul ((hg r hr).norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖c t‖ * ‖g r t‖ ^ 2 ≤ ‖c t‖ * (M * (1 + |t|) ^ k) := by gcongr; exact hgr r hr t
      _ = M * (‖c t‖ * (1 + |t|) ^ k) := by ring
  have hI1 : ∀ r ∈ T, Integrable fun t => ‖c t‖ * ‖g r t‖ := by
    intro r hr
    refine (hc0.add (hI2 r hr)).mono'
      (c.continuous.norm.mul (hg r hr).norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖g r t‖ ≤ 1 + ‖g r t‖ ^ 2 := by nlinarith [sq_nonneg (‖g r t‖ - 1)]
    calc ‖c t‖ * ‖g r t‖ ≤ ‖c t‖ * (1 + ‖g r t‖ ^ 2) := by gcongr
      _ = ‖c t‖ + ‖c t‖ * ‖g r t‖ ^ 2 := by ring
  calc ∑ r ∈ T, ‖∫ t, c t * g r t‖ ^ 2
      ≤ ∑ r ∈ T, (∫ t, ‖c t‖) * ∫ t, ‖c t‖ * ‖g r t‖ ^ 2 := by
        refine Finset.sum_le_sum fun r hr => ?_
        have h1 : ‖∫ t, c t * g r t‖ ≤ ∫ t, ‖c t‖ * ‖g r t‖ := by
          refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
          congr 1; ext t; exact norm_mul _ _
        calc ‖∫ t, c t * g r t‖ ^ 2 ≤ (∫ t, ‖c t‖ * ‖g r t‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ _ := sq_integral_mul_le (fun t => norm_nonneg _) hc0 (hI1 r hr) (hI2 r hr)
    _ = (∫ t, ‖c t‖) * ∫ t, ∑ r ∈ T, ‖c t‖ * ‖g r t‖ ^ 2 := by
        rw [← Finset.mul_sum, integral_finsetSum _ hI2]
    _ ≤ (∫ t, ‖c t‖) * ∫ t, M * (‖c t‖ * (1 + |t|) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun t => norm_nonneg _)
        refine integral_mono (integrable_finsetSum _ hI2) (hck.const_mul M) fun t => ?_
        simp only
        rw [← Finset.mul_sum]
        calc ‖c t‖ * ∑ r ∈ T, ‖g r t‖ ^ 2 ≤ ‖c t‖ * (M * (1 + |t|) ^ k) := by
              gcongr; exact hb t
          _ = M * (‖c t‖ * (1 + |t|) ^ k) := by ring
    _ = _ := by rw [integral_const_mul]



/-! ### Dilated weights -/

/-- `‖ρ^{2πit}‖ = 1` for `ρ > 0`. -/
theorem norm_cpow_tI (ρ t : ℝ) (hρ : 0 < ρ) :
    ‖(ρ : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hρ]
  simp

theorem continuous_tI : Continuous fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ) * I :=
  (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const

theorem norm_tI_le (t : ℝ) : ‖((2 * Real.pi * t : ℝ) : ℂ) * I‖ ≤ 8 * |t| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have := Real.pi_lt_four
  gcongr
  linarith

/-- **Mean square of dilated weights.** Let the row sums `S_r(U) = Σ_{n∈C} a_r(n)·U(x_n)`
(`x_n > 0`) satisfy `Σ_r ‖S_r(U)‖² ≤ M·N²` for every smooth `U` supported in `tsupport V` whose
first `J` derivatives are bounded by `N`. Then, for dilations `ρ_r ∈ [ρ₀, ρ₁]` and `|Re s| ≤ A`,
`Σ_r ‖S_r(x ↦ W₀(ρ_r x)·x^s)‖² ≤ K·M·(1+|s|)^{2J}`, with `K` independent of the rows, the
columns, the coefficients, the points, `M`, the dilations and `s`. Here `V = 1` on
`[α/ρ₁, β/ρ₀]` and `W₀` is supported in `[α, β]`. -/
theorem dilated_meanSquare (W0 : ℝ → ℂ) (hW0 : ContDiff ℝ ∞ W0) {α β : ℝ} (hα : 0 < α)
    (hW0s : ∀ y, y < α ∨ β < y → W0 y = 0) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0) {ρ0 ρ1 : ℝ} (hρ0 : 0 < ρ0)
    (hV1 : ∀ y, α / ρ1 ≤ y → y ≤ β / ρ0 → V y = 1) (A : ℝ) (J : ℕ) :
    ∃ K, ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, ρ0 ≤ ρ r ∧ ρ r ≤ ρ1) → ∀ s : ℂ, |s.re| ≤ A →
      ∑ r ∈ T, ‖∑ n ∈ C, a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s)‖ ^ 2 ≤
        K * M * (1 + ‖s‖) ^ (2 * J) := by
  obtain ⟨c, hc⟩ := mellin_of_compact W0 hW0 hα hW0s
  obtain ⟨Ctf, hCtf0, hCtf⟩ := testFun_bound V hV hVc hVp A J
  refine ⟨(∫ t, ‖c t‖) * (Ctf ^ 2 * 64 ^ J * ∫ t, ‖c t‖ * (1 + |t|) ^ (2 * J)),
    fun T C a x hx M hM hyp ρ hρ s hs => ?_⟩
  set e : ℝ → ℂ := fun t => ((2 * Real.pi * t : ℝ) : ℂ) * I with he
  set U : ℝ → ℝ → ℂ := fun t y => V y * (y : ℂ) ^ (s + e t) with hU
  have hρpos : ∀ r ∈ T, 0 < ρ r := fun r hr => lt_of_lt_of_le hρ0 (hρ r hr).1
  have hre : ∀ t, (s + e t).re = s.re := fun t => by simp [he]
  -- the pointwise Mellin representation
  have hpt : ∀ r ∈ T, ∀ n ∈ C, W0 (ρ r * x n) * (x n : ℂ) ^ s =
      ∫ t, c t * ((ρ r : ℂ) ^ e t * U t (x n)) := by
    intro r hr n hn
    have hxn := hx n hn
    have hρr := hρpos r hr
    have hVW : W0 (ρ r * x n) * (x n : ℂ) ^ s = V (x n) * (x n : ℂ) ^ s * W0 (ρ r * x n) := by
      by_cases hW : W0 (ρ r * x n) = 0
      · rw [hW]; ring
      · have h1 : α ≤ ρ r * x n := by
          by_contra h; exact hW (hW0s _ (Or.inl (not_le.1 h)))
        have h2 : ρ r * x n ≤ β := by
          by_contra h; exact hW (hW0s _ (Or.inr (not_le.1 h)))
        have hρ1 : 0 < ρ1 := lt_of_lt_of_le hρr (hρ r hr).2
        have hV' : V (x n) = 1 := by
          refine hV1 _ ?_ ?_
          · rw [div_le_iff₀ hρ1]
            nlinarith [(hρ r hr).2]
          · rw [le_div_iff₀ hρ0]
            nlinarith [(hρ r hr).1]
        rw [hV']; ring
    rw [hVW, hc _ (mul_pos hρr hxn), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hU, he]
    rw [Complex.cpow_add _ _ (by exact_mod_cast hxn.ne'), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hρr.le hxn.le]
    ring
  -- continuity and boundedness in `t`
  have hcontU : ∀ n ∈ C, Continuous fun t => U t (x n) := fun n hn =>
    continuous_const.mul ((continuous_const.add continuous_tI).const_cpow
      (Or.inl (by exact_mod_cast (hx n hn).ne')))
  have hcontρ : ∀ r ∈ T, Continuous fun t => (ρ r : ℂ) ^ e t := fun r hr =>
    continuous_tI.const_cpow (Or.inl (by exact_mod_cast (hρpos r hr).ne'))
  have hnormρ : ∀ r ∈ T, ∀ t, ‖(ρ r : ℂ) ^ e t‖ = 1 := fun r hr t =>
    norm_cpow_tI (ρ r) t (hρpos r hr)
  have hint : ∀ r ∈ T, ∀ n ∈ C,
      Integrable fun t => a r n * (c t * ((ρ r : ℂ) ^ e t * U t (x n))) := by
    intro r hr n hn
    refine (c.integrable.mul_bdd (c := ‖V (x n)‖ * x n ^ s.re)
      ((hcontρ r hr).mul (hcontU n hn)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)).const_mul (a r n)
    simp only [Pi.mul_apply]
    rw [norm_mul, hnormρ r hr t, one_mul]
    simp only [hU]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx n hn), hre t]
  have hrep : ∀ r ∈ T, ∑ n ∈ C, a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s) =
      ∫ t, c t * ((ρ r : ℂ) ^ e t * ∑ n ∈ C, a r n * U t (x n)) := by
    intro r hr
    have h1 : ∀ n ∈ C, a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s) =
        ∫ t, a r n * (c t * ((ρ r : ℂ) ^ e t * U t (x n))) := by
      intro n hn; rw [hpt r hr n hn, integral_const_mul]
    rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ (hint r hr)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- the mean-square bound for the separated sums
  set g := fun r (t : ℝ) => (ρ r : ℂ) ^ e t * ∑ n ∈ C, a r n * U t (x n) with hg
  have hgc : ∀ r ∈ T, Continuous (g r) := fun r hr =>
    (hcontρ r hr).mul (continuous_finsetSum _ fun n hn => continuous_const.mul (hcontU n hn))
  have hb : ∀ t, ∑ r ∈ T, ‖g r t‖ ^ 2 ≤
      (M * (Ctf ^ 2 * 64 ^ J * (1 + ‖s‖) ^ (2 * J))) * (1 + |t|) ^ (2 * J) := by
    intro t
    have hgr : ∀ r ∈ T, ‖g r t‖ ^ 2 = ‖∑ n ∈ C, a r n * U t (x n)‖ ^ 2 := fun r hr => by
      simp only [hg]; rw [norm_mul, hnormρ r hr t, one_mul]
    rw [Finset.sum_congr rfl hgr]
    have hN := hyp (U t) (testFun_contDiff V hV hVp (s + e t)) tsupport_mul_subset_left
      (Ctf * (1 + ‖s + e t‖) ^ J) (fun j hj y => hCtf (s + e t) (by rw [hre t]; exact hs) j hj y)
    refine hN.trans ?_
    have h8 : 1 + ‖s + e t‖ ≤ 8 * ((1 + ‖s‖) * (1 + |t|)) := by
      have := norm_add_le s (e t)
      have := norm_tI_le t
      nlinarith [norm_nonneg s, abs_nonneg t, mul_nonneg (norm_nonneg s) (abs_nonneg t)]
    have h8' : (1 + ‖s + e t‖) ^ (2 * J) ≤ 64 ^ J * (1 + ‖s‖) ^ (2 * J) * (1 + |t|) ^ (2 * J) := by
      calc (1 + ‖s + e t‖) ^ (2 * J) ≤ (8 * ((1 + ‖s‖) * (1 + |t|))) ^ (2 * J) :=
            pow_le_pow_left₀ (by positivity) h8 _
        _ = 64 ^ J * (1 + ‖s‖) ^ (2 * J) * (1 + |t|) ^ (2 * J) := by
            rw [mul_pow, mul_pow, pow_mul, show (8 : ℝ) ^ 2 = 64 by norm_num]; ring
    calc M * (Ctf * (1 + ‖s + e t‖) ^ J) ^ 2 = M * Ctf ^ 2 * (1 + ‖s + e t‖) ^ (2 * J) := by
          rw [mul_pow, ← pow_mul, mul_comm J 2]; ring
      _ ≤ M * Ctf ^ 2 * (64 ^ J * (1 + ‖s‖) ^ (2 * J) * (1 + |t|) ^ (2 * J)) := by gcongr
      _ = _ := by ring
  have key := sum_norm_integral_sq_le T c g hgc hb
  rw [Finset.sum_congr rfl fun r hr => by rw [hrep r hr]]
  refine key.trans (le_of_eq ?_)
  ring



/-! ### The bilinear form with the dual kernel -/

theorem arg_ofReal_ne_pi {x : ℝ} (hx : 0 < x) : (x : ℂ).arg ≠ Real.pi := by
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne

/-- `(A/(x₁x₂))^z = A^z·x₁^{−z}·x₂^{−z}` for positive reals. -/
theorem cpow_div_mul (A x1 x2 : ℝ) (hA : 0 < A) (h1 : 0 < x1) (h2 : 0 < x2) (z : ℂ) :
    ((A / (x1 * x2) : ℝ) : ℂ) ^ z = (A : ℂ) ^ z * ((x1 : ℂ) ^ (-z) * (x2 : ℂ) ^ (-z)) := by
  have hx : (0 : ℝ) < x1 * x2 := mul_pos h1 h2
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hA.le (inv_nonneg.2 hx.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (arg_ofReal_ne_pi hx), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg h1.le h2.le, Complex.cpow_neg, Complex.cpow_neg, mul_inv]

theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    conj ((x : ℂ) ^ s) = (x : ℂ) ^ conj s := by
  rw [Complex.cpow_conj _ _ (arg_ofReal_ne_pi hx), Complex.conj_ofReal]

/-- **The bilinear form with the dual kernel.** Under the hypotheses of `dilated_meanSquare`,
for unimodular-bounded row coefficients `w_r`, dilations `ρ_r ∈ [ρ₀, ρ₁]` and kernel parameters
`A_r ≥ A_min > 0`, the bilinear form
`Σ_r w_r Σ_{n₁,n₂} a_r(n₁)·conj a_r(n₂)·W₀(ρ_r x_{n₁})·conj W₀(ρ_r x_{n₂})·G(√(A_r/(x_{n₁}x_{n₂})))`
is at most `K·A_min^{−σ}·M`, with `K` independent of the rows, columns, coefficients, points,
`M`, dilations, `w` and `A`. Here `G` is smooth with bounded derivatives and vanishes on `[R, ∞)`,
and `σ > 0`. -/
theorem bilinear_dual_bound (W0 : ℝ → ℂ) (hW0 : ContDiff ℝ ∞ W0) {α β : ℝ} (hα : 0 < α)
    (hW0s : ∀ y, y < α ∨ β < y → W0 y = 0) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0) {ρ0 ρ1 : ℝ} (hρ0 : 0 < ρ0)
    (hV1 : ∀ y, α / ρ1 ≤ y → y ≤ β / ρ0 → V y = 1) (J : ℕ)
    (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ n : ℕ, ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n G ρ‖ ≤ C)
    {R : ℝ} (hR : ∀ ρ, R ≤ ρ → G ρ = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K, ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, ρ0 ≤ ρ r ∧ ρ r ≤ ρ1) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (a r n2) *
          (W0 (ρ r * x n1) * conj (W0 (ρ r * x n2)) *
            G (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ K * Amin ^ (-σ) * M := by
  obtain ⟨Kd, hKd⟩ := dilated_meanSquare W0 hW0 hα hW0s V hV hVc hVp hρ0 hV1 σ J
  obtain ⟨h, hh⟩ := mellin_of_dual G hG hGb hR hσ
  refine ⟨Kd * 64 ^ J * (1 + σ) ^ (2 * J) * ∫ t, ‖h t‖ * (1 + |t|) ^ (2 * J), ?_⟩
  intro ι κ T C a x hx M hM hyp ρ hρ w hw Ar Amin hAmin hAr
  set e : ℝ → ℂ := fun t => ((2 * Real.pi * t : ℝ) : ℂ) * I with he
  set z : ℝ → ℂ := fun t => (-σ : ℂ) + e t with hz
  set s1 : ℝ → ℂ := fun t => (σ : ℂ) - e t with hs1
  set s2 : ℝ → ℂ := fun t => (σ : ℂ) + e t with hs2
  have hzs : ∀ t, -z t = s1 t := fun t => by simp only [hz, hs1]; ring
  have hconj : ∀ t, conj (s2 t) = s1 t := fun t => by
    simp only [hs1, hs2, he, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hre1 : ∀ t, (s1 t).re = σ := fun t => by simp [hs1, he]
  have hre2 : ∀ t, (s2 t).re = σ := fun t => by simp [hs2, he]
  have hrez : ∀ t, (z t).re = -σ := fun t => by simp [hz, he]
  have hArpos : ∀ r ∈ T, 0 < Ar r := fun r hr => lt_of_lt_of_le hAmin (hAr r hr)
  -- the two separated column sums
  set p : ι → κ → ℝ → ℂ := fun r n t => a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s1 t) with hp
  set q : ι → κ → ℝ → ℂ := fun r n t => a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s2 t) with hq
  set F : ι → κ → κ → ℝ → ℂ := fun r n1 n2 t =>
    w r * (h t * ((Ar r : ℂ) ^ z t * (p r n1 t * conj (q r n2 t)))) with hF
  have hcont_e : Continuous e := continuous_tI
  have hcpow : ∀ (y : ℝ), 0 < y → ∀ (f : ℝ → ℂ), Continuous f →
      Continuous fun t => (y : ℂ) ^ f t := fun y hy f hf =>
    hf.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  -- integrability of each term
  have hFint : ∀ r ∈ T, ∀ n1 ∈ C, ∀ n2 ∈ C, Integrable (F r n1 n2) := by
    intro r hr n1 hn1 n2 hn2
    have hb : ∀ t, ‖(Ar r : ℂ) ^ z t * (p r n1 t * conj (q r n2 t))‖ ≤
        Ar r ^ (-σ) * ((‖a r n1‖ * (‖W0 (ρ r * x n1)‖ * x n1 ^ σ)) *
          (‖a r n2‖ * (‖W0 (ρ r * x n2)‖ * x n2 ^ σ))) := by
      intro t
      simp only [hp, hq]
      rw [norm_mul, norm_mul, RCLike.norm_conj, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (hArpos r hr), hrez,
        Complex.norm_cpow_eq_rpow_re_of_pos (hx n1 hn1), hre1,
        Complex.norm_cpow_eq_rpow_re_of_pos (hx n2 hn2), hre2]
    have hc : Continuous fun t => (Ar r : ℂ) ^ z t * (p r n1 t * conj (q r n2 t)) := by
      simp only [hp, hq, hz, hs1, hs2]
      refine (hcpow _ (hArpos r hr) _ (continuous_const.add hcont_e)).mul
        ((continuous_const.mul (continuous_const.mul
          (hcpow _ (hx n1 hn1) _ (continuous_const.sub hcont_e)))).mul
          (Complex.continuous_conj.comp (continuous_const.mul (continuous_const.mul
            (hcpow _ (hx n2 hn2) _ (continuous_const.add hcont_e))))))
    exact (h.integrable.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).const_mul (w r)
  -- the pointwise Mellin representation of each summand
  have hterm : ∀ r ∈ T, ∀ n1 ∈ C, ∀ n2 ∈ C,
      w r * (a r n1 * conj (a r n2) * (W0 (ρ r * x n1) * conj (W0 (ρ r * x n2)) *
        G (Real.sqrt (Ar r / (x n1 * x n2))))) = ∫ t, F r n1 n2 t := by
    intro r hr n1 hn1 n2 hn2
    have hy : 0 < Ar r / (x n1 * x n2) := div_pos (hArpos r hr) (mul_pos (hx n1 hn1) (hx n2 hn2))
    rw [hh _ hy, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, hp, hq]
    rw [cpow_div_mul _ _ _ (hArpos r hr) (hx n1 hn1) (hx n2 hn2), hzs, map_mul, map_mul,
      conj_ofReal_cpow (hx n2 hn2), hconj]
    ring
  -- exchange the finite sums with the integral
  have hsum : ∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (a r n2) *
        (W0 (ρ r * x n1) * conj (W0 (ρ r * x n2)) * G (Real.sqrt (Ar r / (x n1 * x n2)))) =
      ∫ t, ∑ r ∈ T, ∑ n1 ∈ C, ∑ n2 ∈ C, F r n1 n2 t := by
    have hI2 : ∀ r ∈ T, ∀ n1 ∈ C, Integrable fun t => ∑ n2 ∈ C, F r n1 n2 t :=
      fun r hr n1 hn1 => integrable_finsetSum _ fun n2 hn2 => hFint r hr n1 hn1 n2 hn2
    have hI1 : ∀ r ∈ T, Integrable fun t => ∑ n1 ∈ C, ∑ n2 ∈ C, F r n1 n2 t :=
      fun r hr => integrable_finsetSum _ fun n1 hn1 => hI2 r hr n1 hn1
    rw [integral_finsetSum _ hI1]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [integral_finsetSum _ (hI2 r hr), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n1 hn1 => ?_
    rw [integral_finsetSum _ fun n2 hn2 => hFint r hr n1 hn1 n2 hn2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n2 hn2 => hterm r hr n1 hn1 n2 hn2
  -- the pointwise bound
  set Bd : ℝ → ℝ := fun t => Amin ^ (-σ) * (Kd * M * 64 ^ J * (1 + σ) ^ (2 * J)) *
    (‖h t‖ * (1 + |t|) ^ (2 * J)) with hBd
  have hBdint : Integrable Bd :=
    (integrable_norm_mul_one_add_pow h (2 * J)).const_mul _
  have hpt : ∀ t, ‖∑ r ∈ T, ∑ n1 ∈ C, ∑ n2 ∈ C, F r n1 n2 t‖ ≤ Bd t := by
    intro t
    have hfac : ∀ r ∈ T, ∑ n1 ∈ C, ∑ n2 ∈ C, F r n1 n2 t =
        w r * (h t * ((Ar r : ℂ) ^ z t *
          ((∑ n ∈ C, p r n t) * conj (∑ n ∈ C, q r n t)))) := by
      intro r hr
      rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n1 _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hfac]
    -- norms
    have hs1n : ‖s1 t‖ ≤ σ + 8 * |t| := by
      calc ‖s1 t‖ ≤ ‖(σ : ℂ)‖ + ‖e t‖ := norm_sub_le _ _
        _ ≤ σ + 8 * |t| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
          linarith [norm_tI_le t]
    have hs2n : ‖s2 t‖ = ‖s1 t‖ := by rw [← hconj t, RCLike.norm_conj]
    have hpoly : (1 + ‖s1 t‖) ^ (2 * J) ≤ 64 ^ J * (1 + σ) ^ (2 * J) * (1 + |t|) ^ (2 * J) := by
      have h8 : 1 + ‖s1 t‖ ≤ 8 * ((1 + σ) * (1 + |t|)) := by
        nlinarith [abs_nonneg t, mul_nonneg hσ.le (abs_nonneg t)]
      calc (1 + ‖s1 t‖) ^ (2 * J) ≤ (8 * ((1 + σ) * (1 + |t|))) ^ (2 * J) :=
            pow_le_pow_left₀ (by positivity) h8 _
        _ = 64 ^ J * (1 + σ) ^ (2 * J) * (1 + |t|) ^ (2 * J) := by
            rw [mul_pow, mul_pow, pow_mul, show (8 : ℝ) ^ 2 = 64 by norm_num]; ring
    have hP := hKd T C a x hx M hM hyp ρ hρ (s1 t) (by rw [hre1 t, abs_of_pos hσ])
    have hQ := hKd T C a x hx M hM hyp ρ hρ (s2 t) (by rw [hre2 t, abs_of_pos hσ])
    rw [hs2n] at hQ
    have hPQ : ∑ r ∈ T, ‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖ ≤
        Kd * M * (1 + ‖s1 t‖) ^ (2 * J) := by
      have hamgm : ∀ r ∈ T, ‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖ ≤
          (‖∑ n ∈ C, p r n t‖ ^ 2 + ‖∑ n ∈ C, q r n t‖ ^ 2) / 2 := fun r _ => by
        nlinarith [sq_nonneg (‖∑ n ∈ C, p r n t‖ - ‖∑ n ∈ C, q r n t‖)]
      refine (Finset.sum_le_sum hamgm).trans ?_
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp only [hp, hq]
      linarith
    have hAr' : ∀ r ∈ T, ‖(Ar r : ℂ) ^ z t‖ ≤ Amin ^ (-σ) := fun r hr => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hArpos r hr), hrez]
      exact Real.rpow_le_rpow_of_nonpos hAmin (hAr r hr) (by linarith)
    calc ‖∑ r ∈ T, w r * (h t * ((Ar r : ℂ) ^ z t *
            ((∑ n ∈ C, p r n t) * conj (∑ n ∈ C, q r n t))))‖
        ≤ ∑ r ∈ T, ‖w r * (h t * ((Ar r : ℂ) ^ z t *
            ((∑ n ∈ C, p r n t) * conj (∑ n ∈ C, q r n t))))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ T, ‖h t‖ * (Amin ^ (-σ) *
            (‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖)) := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj]
          calc ‖w r‖ * (‖h t‖ * (‖(Ar r : ℂ) ^ z t‖ *
                (‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖)))
              ≤ 1 * (‖h t‖ * (Amin ^ (-σ) *
                (‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖))) := by
                gcongr
                · exact hw r hr
                · exact hAr' r hr
            _ = _ := one_mul _
      _ = ‖h t‖ * Amin ^ (-σ) * ∑ r ∈ T, ‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
      _ ≤ ‖h t‖ * Amin ^ (-σ) * (Kd * M * (64 ^ J * (1 + σ) ^ (2 * J) * (1 + |t|) ^ (2 * J))) := by
          gcongr
          calc ∑ r ∈ T, ‖∑ n ∈ C, p r n t‖ * ‖∑ n ∈ C, q r n t‖
              ≤ Kd * M * (1 + ‖s1 t‖) ^ (2 * J) := hPQ
            _ ≤ _ := by
              have hKd0 : 0 ≤ Kd * M := by
                have := (hKd T C a x hx M hM hyp ρ hρ (s1 t) (by rw [hre1 t, abs_of_pos hσ]))
                -- Kd·M·(1+‖s‖)^{2J} ≥ a sum of squares ≥ 0
                have hpos : 0 < (1 + ‖s1 t‖) ^ (2 * J) := by positivity
                have h0 : 0 ≤ Kd * M * (1 + ‖s1 t‖) ^ (2 * J) :=
                  le_trans (Finset.sum_nonneg fun r _ => by positivity) this
                exact nonneg_of_mul_nonneg_left h0 hpos
              gcongr
      _ = Bd t := by simp only [hBd]; ring
  rw [hsum]
  refine (norm_integral_le_of_norm_le hBdint (Filter.Eventually.of_forall hpt)).trans
    (le_of_eq ?_)
  simp only [hBd]
  rw [integral_const_mul]
  ring

end MellinSep

end

#print axioms MellinSep.log_fourier_inversion
#print axioms MellinSep.mellin_of_compact
#print axioms MellinSep.schwartz_exp_comp
#print axioms MellinSep.mellin_of_dual
#print axioms MellinSep.iteratedDeriv_ofReal_cpow
#print axioms MellinSep.testFun_contDiff
#print axioms MellinSep.testFun_bound
#print axioms MellinSep.sq_integral_mul_le
#print axioms MellinSep.sum_norm_integral_sq_le
#print axioms MellinSep.dilated_meanSquare
#print axioms MellinSep.bilinear_dual_bound
