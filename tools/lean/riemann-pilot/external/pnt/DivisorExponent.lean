/-
# Round 473: the divisor problems in a zero-free half-plane

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `d_k = 1 ⋆ ⋯ ⋆ 1` (`k` factors; `dk k`, the `k`-th Dirichlet power of
`ArithmeticFunction.zeta`). If `ζ(s) ≠ 0` for `Re s > θ` (`0 ≤ θ < 1`), then for every `k ≥ 1` and `η > 0`,
`Σ_{n ≤ x} d_k(n) = xP_k(log x) + O(x^{θ+η})` (`divisor_isBigO_of_zeroFree`), where `P_k` (`Pk k`) is a real
polynomial of degree `k − 1` with leading coefficient `1/(k − 1)!` (`natDegree_Pk_eq`, `coeff_Pk`), built from
the Taylor coefficients of `((s − 1)ζ(s))^k` at `s = 1`. At `θ = 11/12` (round 466's half-plane) and at `θ = Θ`
(round 469's supremum of the real parts of the nontrivial zeros) this holds with no hypothesis
(`divisor_isBigO_eleven_twelfths`, `divisor_isBigO_Theta`).

* `zeta_pow_eq`: `ζ(s)^k = Σ_{j<k} c_j(s − 1)^{j−k} + g_k(s)` for `s ≠ 1`, where `c_j` and the entire `g_k` are
  the iterated slopes (`dslope`) at `1` of `Z(s)^k`, with round 220's entire `Z(s) = (s − 1)ζ(s)`
  (`PsiOmega.Zr`).
* `inv_sub_one_pow_eq_integral`: `(s − 1)^{−m} = ∫_0^∞ (u^{m−1}/(m − 1)!) e^{−(s−1)u} du` for `Re s > 1`, from
  `∫_0^∞ u^m e^{−cu} du = m!/c^{m+1}` for `Re c > 0` (`integral_pow_mul_cexp`, by integration by parts).
* `verticalIntegral_inv_sub_one_pow`: `(1/2πi) ∫_{(2)} (s − 1)^{−m}𝓜(Smooth1)(s)X^s ds
  = ∫_0^∞ (u^{m−1}/(m − 1)!) e^u Smooth1(e^u/X) du`, by Fubini and Mathlib's Mellin inversion
  (`mellinInv_mellin_eq`) at `e^u/X`.
* `smoothedSum_dk_eq`: `Σ_n d_k(n)Smooth1(n/Y) = Σ_{j<k} c_j J_{k−j}(Y) + G(Y)`, with `J_m(Y)` the integral above
  and `G(Y) = (1/2πi) ∫_{(2)} g_k(s)𝓜(Smooth1)(s)Y^s ds`, from round 472's
  `SmoothPerron.verticalIntegral_eq_smoothedSum` and `L(d_k, s) = ζ(s)^k` on `Re s > 1` (`LSeries_dk`).
* `norm_remainder_le`: for `θ < θ' < 1` and `0 < κ ≤ 1` there is `K` with `|G(Y)| ≤ Kε^{−κ}Y^{θ'}` for
  `0 < ε < 1` and `Y ≥ 1`. The line moves to `Re s = θ'` (`SmoothPerron.verticalIntegral_integrand_shift`),
  where `|g_k(s)| ≤ |ζ(s)|^k + Σ_j |c_j|` (`norm_gk_le`) and round 470's `|ζ(σ + it)| ≤ C|t|^{κ/(2k)}`
  (`HalfPlaneLindelof.zeta_bound_of_zeroFree`) meet `SmoothPerron.mellin_le_geom`.
* `abs_Jm_sub_Lm_le`: if `1 ≤ Y(1 − log 2 · ε) ≤ X ≤ Y(1 + 2 log 2 · ε) ≤ 3X`, `J_m(Y)` differs from
  `L_m(X) = ∫_0^{log X} e^u u^{m−1}/(m − 1)! du = Xp_m(log X) − p_m(0)` (`Lm_eq`) by at most
  `2 log((1 + 2 log 2 · ε)/(1 − log 2 · ε)) · 3X(log 3X)^{m−1}`, since `Smooth1(e^u/Y)` is `1` below and `0`
  above that window in `u`.
* `divisor_bound_at`, `divisor_isBigO_of_zeroFree`: since `d_k ≥ 0`, `Σ_{n≤X} d_k(n)` lies between the smoothed
  sums at `Y = X/(1 + 2 log 2 · ε)` and `Y = X/(1 − log 2 · ε)` (`tsum_smooth_le`, `le_tsum_smooth`); with
  `ε = X^{θ'−1}`, `θ' = θ + η₀/4`, `κ = η₀/4` and `η₀ = min(η, (1 − θ)/2)`, every error is `O(X^{θ'+κ})`.
-/
import MertensExponent

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform5) "𝓜" => mellin

namespace DivisorExponent

/-- `u ↦ u^m e^{−cu}` is integrable on `(0, ∞)` for `Re c > 0`. -/
lemma integrableOn_pow_mul_cexp (m : ℕ) {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ m * cexp (-(c * u))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := m) (b := c.re)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith) one_pos hc
  refine Integrable.mono' h (by fun_prop : Continuous fun u : ℝ ↦ (u : ℂ) ^ m * cexp (-(c * u))).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu ↦ ?_))
  have hu0 : 0 < u := hu
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_exp,
    Real.rpow_one, Real.rpow_natCast]
  apply le_of_eq
  congr 2
  simp [Complex.mul_re]

/-- **`∫_0^∞ u^m e^{−cu} du = m!/c^{m+1}`** for `Re c > 0`. -/
theorem integral_pow_mul_cexp (m : ℕ) {c : ℂ} (hc : 0 < c.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ m * cexp (-(c * u)) = m.factorial / c ^ (m + 1) := by
  have hc0 : c ≠ 0 := fun h ↦ by rw [h, zero_re] at hc; exact lt_irrefl _ hc
  induction m with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -c) (by simp; linarith) 0
    simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have e : (fun u : ℝ ↦ cexp (-(c * u))) = fun u : ℝ ↦ cexp (-c * u) := by
      funext u
      ring_nf
    rw [e, h]
    field_simp
  | succ m ih =>
    -- integration by parts: `U = u^{m+1}`, `V = −e^{−cu}/c`
    have hU : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * (x : ℂ) ^ m) x := fun x _ ↦ by
      simpa using (hasDerivAt_pow (m + 1) (x : ℂ)).comp_ofReal
    have hV : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ ↦ -cexp (-(c * x)) / c)
        (cexp (-(c * x))) x := fun x _ ↦ by
      have h1 : HasDerivAt (fun z : ℂ ↦ cexp (-(c * z))) (cexp (-(c * x)) * (-(c * 1))) (x : ℂ) :=
        (((hasDerivAt_id (x : ℂ)).const_mul c).neg).cexp
      have h2 := (h1.comp_ofReal).neg.div_const c
      convert h2 using 1
      field_simp
    have hint1 : IntegrableOn ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) * fun x : ℝ ↦ cexp (-(c * x))) (Ioi 0) :=
      integrableOn_pow_mul_cexp (m + 1) hc
    have hint2 : IntegrableOn ((fun x : ℝ ↦ ((m + 1 : ℕ) : ℂ) * (x : ℂ) ^ m) *
        fun x : ℝ ↦ -cexp (-(c * x)) / c) (Ioi 0) := by
      have := (integrableOn_pow_mul_cexp m hc).const_mul (-((m + 1 : ℕ) : ℂ) / c)
      refine IntegrableOn.congr_fun this (fun x _ ↦ ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]
      ring
    -- the boundary terms
    have hnorm : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ) ^ (m + 1) * (-cexp (-(c * x)) / c)‖ =
        ‖c‖⁻¹ * (x ^ ((m + 1 : ℕ) : ℝ) * Real.exp (-c.re * x)) := by
      intro x hx
      rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
        Complex.norm_exp, Real.rpow_natCast]
      have : (-(c * (x : ℂ))).re = -c.re * x := by simp [Complex.mul_re]
      rw [this]
      ring
    have hinf : Tendsto ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) * fun x : ℝ ↦ -cexp (-(c * x)) / c) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m + 1 : ℕ) : ℝ) c.re hc).const_mul ‖c‖⁻¹
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with x hx
      exact (hnorm x hx).symm
    have hzero : Tendsto ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) * fun x : ℝ ↦ -cexp (-(c * x)) / c)
        (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) * fun x : ℝ ↦ -cexp (-(c * x)) / c) := by
        fun_prop
      have := hcont.tendsto 0
      simp only [Pi.mul_apply, ofReal_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, zero_pow, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hU hV hint1 hint2 hzero hinf
    rw [hibp]
    have e : ∫ x in Ioi (0 : ℝ), ((m + 1 : ℕ) : ℂ) * (x : ℂ) ^ m * (-cexp (-(c * x)) / c) =
        -((m + 1 : ℕ) : ℂ) / c * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ m * cexp (-(c * x)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [e, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `(s − 1)^{−m} = ∫_0^∞ (u^{m−1}/(m−1)!) e^{−(s−1)u} du` for `Re s > 1`, `m ≥ 1`. -/
theorem inv_sub_one_pow_eq_integral {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re) :
    ((s - 1) ^ m)⁻¹ = ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (m - 1) / ((m - 1).factorial : ℂ) *
      cexp (-((s - 1) * u)) := by
  have hc : 0 < (s - 1).re := by simp; linarith
  have h := integral_pow_mul_cexp (m - 1) hc
  rw [Nat.sub_add_cancel hm] at h
  have hf : ((m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have e : (fun u : ℝ ↦ (u : ℂ) ^ (m - 1) / ((m - 1).factorial : ℂ) * cexp (-((s - 1) * u))) =
      fun u : ℝ ↦ ((m - 1).factorial : ℂ)⁻¹ * ((u : ℂ) ^ (m - 1) * cexp (-((s - 1) * u))) := by
    funext u
    field_simp
  rw [e, integral_const_mul, h]
  field_simp

/-! ### Taylor expansion by iterated slopes -/

/-- `f(s) = Σ_{j<k} c_j (s − a)^j + (s − a)^k g_k(s)` with `g_k = (dslope · a)^[k] f` and
`c_j = g_j(a)`. -/
lemma eq_sum_add_iterate_dslope (f : ℂ → ℂ) (a : ℂ) (k : ℕ) (s : ℂ) :
    f s = ∑ j ∈ Finset.range k, (fun g ↦ dslope g a)^[j] f a * (s - a) ^ j +
      (s - a) ^ k * (fun g ↦ dslope g a)^[k] f s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Finset.sum_range_succ, Function.iterate_succ_apply']
    have h := sub_smul_dslope ((fun g ↦ dslope g a)^[k] f) a s
    rw [smul_eq_mul] at h
    have e : (fun g ↦ dslope g a)^[k] f s =
        (fun g ↦ dslope g a)^[k] f a + (s - a) * dslope ((fun g ↦ dslope g a)^[k] f) a s := by
      rw [h]
      ring
    rw [e]
    ring

lemma differentiable_iterate_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (k : ℕ) :
    Differentiable ℂ ((fun g ↦ dslope g a)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [← differentiableOn_univ] at ih ⊢
    exact (differentiableOn_dslope Filter.univ_mem).2 ih

end DivisorExponent

namespace DivisorExponent

open ArithmeticFunction

/-- The `k`-fold divisor function `d_k = 1 ⋆ ⋯ ⋆ 1`, the `k`-th power of `ArithmeticFunction.zeta`
(Dirichlet convolution), with values in `ℕ`. -/
abbrev dk (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

lemma natCoe_pow (f : ArithmeticFunction ℕ) (k : ℕ) :
    ((f ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = (f : ArithmeticFunction ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, natCoe_mul, ih, pow_succ]

lemma coe_dk (k : ℕ) : (fun n ↦ ((dk k n : ℕ) : ℂ)) = ⇑((zeta : ArithmeticFunction ℂ) ^ k) := by
  funext n
  rw [← natCoe_pow, natCoe_apply]

/-- `L(d_k, s) = ζ(s)^k` on `Re s > 1`, with absolute convergence. -/
theorem LSeries_dk {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ ((dk k n : ℕ) : ℂ)) s ∧
      LSeries (fun n ↦ ((dk k n : ℕ) : ℂ)) s = riemannZeta s ^ k := by
  rw [coe_dk]
  have hz : LSeriesSummable ⇑(zeta : ArithmeticFunction ℂ) s := by
    have := LSeriesSummable_zeta_iff.2 hs
    convert this using 1
    funext n
    rw [natCoe_apply]
  have hzL : LSeries ⇑(zeta : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [← LSeries_zeta_eq_riemannZeta hs]
    congr 1
  induction k, hk using Nat.le_induction with
  | base => simpa using ⟨hz, hzL⟩
  | succ k hk ih =>
    obtain ⟨hS, hL⟩ := ih
    rw [pow_succ', ← coe_mul]
    exact ⟨hz.convolution hS, by rw [LSeries_convolution' hz hS, hzL, hL, pow_succ']⟩

end DivisorExponent

namespace DivisorExponent

open Polynomial

/-- `p_0 = 0`, `p_{m+1} = v^m/m! − p_m`, so that `(e^v p_{m+1}(v))′ = e^v v^m/m!`. -/
noncomputable def pm : ℕ → Polynomial ℝ
  | 0 => 0
  | m + 1 => C ((m.factorial : ℝ)⁻¹) * X ^ m - pm m

lemma natDegree_pm_succ (m : ℕ) : (pm (m + 1)).natDegree ≤ m := by
  induction m with
  | zero => simp [pm]
  | succ m ih =>
    rw [pm]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) (ih.trans (by omega)))

lemma hasDerivAt_exp_mul_pm (m : ℕ) (v : ℝ) :
    HasDerivAt (fun v ↦ Real.exp v * (pm (m + 1)).eval v)
      (Real.exp v * (v ^ m / m.factorial)) v := by
  induction m with
  | zero =>
    simp only [pm, pow_zero, mul_one, sub_zero, eval_C, Nat.factorial_zero, Nat.cast_one, inv_one,
      div_one]
    simpa using Real.hasDerivAt_exp v
  | succ m ih =>
    have e : (fun v ↦ Real.exp v * (pm (m + 1 + 1)).eval v) =
        fun v ↦ Real.exp v * (v ^ (m + 1) / (m + 1).factorial) - Real.exp v * (pm (m + 1)).eval v := by
      funext v
      simp only [pm, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      ring
    rw [e]
    have hp : HasDerivAt (fun v : ℝ ↦ v ^ (m + 1) / ((m + 1).factorial : ℝ))
        (v ^ m / m.factorial) v := by
      have := (hasDerivAt_pow (m + 1) v).div_const ((m + 1).factorial : ℝ)
      convert this using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    convert ((Real.hasDerivAt_exp v).mul hp).sub ih using 1
    ring

/-- `∫_0^{log X} e^u u^m/m! du = X p_{m+1}(log X) − p_{m+1}(0)` for `X > 0`. -/
theorem integral_exp_mul_pow_div (m : ℕ) {X : ℝ} (hX : 0 < X) :
    ∫ u in (0 : ℝ)..Real.log X, Real.exp u * (u ^ m / m.factorial) =
      X * (pm (m + 1)).eval (Real.log X) - (pm (m + 1)).eval 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ ↦ hasDerivAt_exp_mul_pm m v)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [Real.exp_log hX, Real.exp_zero, one_mul]

end DivisorExponent


namespace DivisorExponent

variable {ν : ℝ → ℝ}

/-- `X^s e^{−(s−1)u} = e^u (e^u/X)^{−s}` for `X > 0`. -/
lemma cpow_mul_cexp_eq {X : ℝ} (Xpos : 0 < X) (u : ℝ) (s : ℂ) :
    (X : ℂ) ^ s * cexp (-((s - 1) * u)) = cexp u * (((Real.exp u / X : ℝ)) : ℂ) ^ (-s) := by
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 Xpos.ne'
  have hXs : (X : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hX' h.1
  have hexp : ((Real.exp u : ℝ) : ℂ) ^ s = cexp (u * s) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'), ← ofReal_log (Real.exp_pos u).le,
      Real.log_exp]
  have key : (((Real.exp u / X : ℝ)) : ℂ) ^ s * (X : ℂ) ^ s = cexp (u * s) := by
    rw [← mul_cpow_ofReal_nonneg (div_nonneg (Real.exp_pos u).le Xpos.le) Xpos.le, ← hexp]
    congr 1
    push_cast
    field_simp
  rw [cpow_neg, eq_div_of_mul_eq hXs key, inv_div]
  have h1 : cexp (-((s - 1) * u)) = cexp u * cexp (-(u * s)) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [h1, Complex.exp_neg]
  field_simp

/-- **The principal parts against the smoothing.** For `m ≥ 1`, `X > 0` and `0 < ε < 1`:
`(1/2πi) ∫_{(2)} (s − 1)^{−m} 𝓜(Smooth1)(s) X^s ds = ∫_0^∞ (u^{m−1}/(m−1)!) e^u Smooth1(e^u/X) du`. -/
theorem verticalIntegral_inv_sub_one_pow {m : ℕ} (hm : 1 ≤ m) (diffν : ContDiff ℝ 1 ν)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (Xpos : 0 < X) :
    VerticalIntegral' (fun s ↦ ((s - 1) ^ m)⁻¹ * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s) 2 =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (m - 1) / ((m - 1).factorial : ℂ) * cexp u *
        (Smooth1 ν ε (Real.exp u / X) : ℂ) := by
  set M : ℝ → ℂ := fun t ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I) with hMdef
  have hM : Integrable M :=
    SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one
      (by norm_num) le_rfl
  have hMc : Continuous M := by
    rw [hMdef, ← continuousOn_univ]
    refine ContinuousOn.comp' (t := {z : ℂ | 0 < z.re}) ?_ (by fun_prop) ?_
    · refine continuousOn_of_forall_continuousAt fun z hz ↦ ?_
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one hz).continuousAt
    · intro t _
      simp
  set ℓ : ℝ → ℂ := fun u ↦ (u : ℂ) ^ (m - 1) / ((m - 1).factorial : ℂ) with hℓdef
  -- the integrand on `(t, u)`
  set G : ℝ → ℝ → ℂ := fun t u ↦ ℓ u * cexp (-(((2 : ℝ) + t * I - 1) * u)) * M t *
    (X : ℂ) ^ ((2 : ℝ) + t * I) with hGdef
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 Xpos.ne'
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun p : ℝ × ℝ ↦ (X : ℂ) ^ ((2 : ℝ) + p.1 * I) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hX')
    have h2 : Continuous fun p : ℝ × ℝ ↦ M p.1 := hMc.comp continuous_fst
    simp only [hGdef, hℓdef, Function.uncurry_def]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.2 : ℂ) ^ (m - 1) / ((m - 1).factorial : ℂ) *
      cexp (-(((2 : ℝ) + p.1 * I - 1) * p.2))).mul h2).mul h1
  -- the majorant
  have hℓint : IntegrableOn (fun u : ℝ ↦ ‖ℓ u‖ * Real.exp (-u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := ((m - 1 : ℕ) : ℝ)) (b := 1)
      (by have := Nat.cast_nonneg (α := ℝ) (m - 1); linarith) one_pos one_pos
    have h' := h.div_const ((m - 1).factorial : ℝ)
    refine IntegrableOn.congr_fun h' (fun u hu ↦ ?_) measurableSet_Ioi
    have hu0 : 0 < u := hu
    simp only [hℓdef, Real.rpow_one, neg_mul, one_mul, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_natCast, Real.rpow_natCast]
    ring
  have hnormG : ∀ t u : ℝ, ‖G t u‖ = ‖M t‖ * X ^ (2 : ℝ) * (‖ℓ u‖ * Real.exp (-u)) := by
    intro t u
    simp only [hGdef, norm_mul, norm_cpow_eq_rpow_re_of_pos Xpos, Complex.norm_exp]
    have h1 : (-(((2 : ℝ) + t * I - 1) * (u : ℂ))).re = -u := by simp; ring
    have h2 : (((2 : ℝ) : ℂ) + t * I).re = 2 := by simp
    rw [h1, h2]
    ring
  have hGint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi 0))) := by
    have hprod := (hM.norm.mul_const (X ^ (2 : ℝ))).mul_prod hℓint
    refine Integrable.mono' hprod hGc.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.uncurry_def]
    exact (hnormG p.1 p.2).le
  -- the line integrand as an integral over `u`
  have hline : ∀ t : ℝ, ((((2 : ℝ) : ℂ) + t * I - 1) ^ m)⁻¹ * M t * (X : ℂ) ^ ((2 : ℝ) + t * I) =
      ∫ u in Ioi (0 : ℝ), G t u := by
    intro t
    have hs : 1 < (((2 : ℝ) : ℂ) + t * I).re := by norm_num
    rw [inv_sub_one_pow_eq_integral hm hs, ← integral_mul_const, ← integral_mul_const]
  -- the integral over `t`, for fixed `u`
  have hinner : ∀ u : ℝ, ∫ t : ℝ, G t u =
      (2 * π : ℂ) * (ℓ u * cexp u * (Smooth1 ν ε (Real.exp u / X) : ℂ)) := by
    intro u
    have hx : 0 < Real.exp u / X := div_pos (Real.exp_pos u) Xpos
    have hinv := mellinInv_mellin_eq 2 (fun x ↦ (Smooth1 ν ε x : ℂ)) hx
      (Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one (by simp))
      hM (Smooth1ContinuousAt diffν νnonneg suppν εpos hx).ofReal
    rw [mellinInv] at hinv
    have hpt : ∀ t : ℝ, G t u = ℓ u * cexp u *
        ((((Real.exp u / X : ℝ)) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) • M t) := by
      intro t
      simp only [hGdef, smul_eq_mul]
      have := cpow_mul_cexp_eq Xpos u (((2 : ℝ) : ℂ) + t * I)
      linear_combination (ℓ u * M t) * this
    simp_rw [hpt]
    rw [integral_const_mul]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have e : ∫ t : ℝ, (((Real.exp u / X : ℝ)) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) • M t =
        (2 * π : ℂ) * (Smooth1 ν ε (Real.exp u / X) : ℂ) := by
      rw [← hinv, Complex.real_smul, ← mul_assoc]
      have h2 : (2 * π : ℂ) * (((1 / (2 * π) : ℝ)) : ℂ) = 1 := by
        push_cast
        field_simp
      rw [h2, one_mul]
    rw [e]
    ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hV : VerticalIntegral' (fun s ↦ ((s - 1) ^ m)⁻¹ * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s *
      (X : ℂ) ^ s) 2 = (1 / (2 * π * I)) * (I * ∫ t : ℝ, ∫ u in Ioi (0 : ℝ), G t u) := by
    show (1 / (2 * π * I)) • (I • ∫ t : ℝ, ((((2 : ℝ) : ℂ) + t * I - 1) ^ m)⁻¹ * M t *
      (X : ℂ) ^ (((2 : ℝ) : ℂ) + t * I)) = _
    rw [smul_eq_mul, smul_eq_mul]
    congr 2
    exact integral_congr_ae (Eventually.of_forall hline)
  rw [hV, integral_integral_swap hGint]
  simp_rw [hinner]
  rw [integral_const_mul]
  simp only [hℓdef]
  field_simp

end DivisorExponent

namespace DivisorExponent

open SmoothPerron PsiOmega PsiExponent

/-! ### `ζ(s)^k` as a principal part at `1` plus an entire function -/

/-- `Z(s)^k`, with round 220's entire `Z(s) = (s − 1)ζ(s)`. -/
noncomputable def zk (k : ℕ) (s : ℂ) : ℂ := Zr s ^ k

/-- The `k`-th iterated slope of `Z^k` at `1`. -/
noncomputable def gk (k : ℕ) : ℂ → ℂ := (fun g ↦ dslope g 1)^[k] (zk k)

/-- The Taylor coefficients of `Z^k` at `1`. -/
noncomputable def ck (k j : ℕ) : ℂ := (fun g ↦ dslope g 1)^[j] (zk k) 1

lemma differentiable_gk (k : ℕ) : Differentiable ℂ (gk k) :=
  differentiable_iterate_dslope (differentiable_Zr.pow k) 1 k

/-- **`ζ(s)^k = Σ_{j<k} c_j (s − 1)^{j−k} + g_k(s)`** for `s ≠ 1`, with `g_k` entire. -/
theorem zeta_pow_eq (k : ℕ) {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s ^ k = ∑ j ∈ Finset.range k, ck k j * ((s - 1) ^ (k - j))⁻¹ + gk k s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hpk : (s - 1) ^ k ≠ 0 := pow_ne_zero _ hs1
  have h : zk k s = ∑ j ∈ Finset.range k, ck k j * (s - 1) ^ j + (s - 1) ^ k * gk k s :=
    eq_sum_add_iterate_dslope (zk k) 1 k s
  have hz : zk k s = (s - 1) ^ k * riemannZeta s ^ k := by
    simp only [zk, Zr_of_ne hs, mul_pow]
  rw [hz] at h
  have hterm : ∀ j ∈ Finset.range k,
      ck k j * (s - 1) ^ j / (s - 1) ^ k = ck k j * ((s - 1) ^ (k - j))⁻¹ := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [pow_sub₀ _ hs1 hj.le, mul_inv, inv_inv]
    field_simp
  calc riemannZeta s ^ k = ((s - 1) ^ k * riemannZeta s ^ k) / (s - 1) ^ k := by field_simp
    _ = (∑ j ∈ Finset.range k, ck k j * (s - 1) ^ j + (s - 1) ^ k * gk k s) / (s - 1) ^ k := by rw [h]
    _ = (∑ j ∈ Finset.range k, ck k j * (s - 1) ^ j) / (s - 1) ^ k + gk k s := by
        rw [add_div]
        field_simp
    _ = _ := by rw [Finset.sum_div, Finset.sum_congr rfl hterm]

lemma norm_inv_sub_one_pow_le {s : ℂ} (hs : 1 ≤ ‖s - 1‖) (m : ℕ) : ‖((s - 1) ^ m)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_pow]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hs)

/-- `|g_k(s)| ≤ |ζ(s)|^k + Σ_{j<k} |c_j|` for `|s − 1| ≥ 1`. -/
lemma norm_gk_le (k : ℕ) {s : ℂ} (hs : 1 ≤ ‖s - 1‖) :
    ‖gk k s‖ ≤ ‖riemannZeta s‖ ^ k + ∑ j ∈ Finset.range k, ‖ck k j‖ := by
  have hs1 : s ≠ 1 := fun h ↦ by rw [h, sub_self, norm_zero] at hs; norm_num at hs
  have e : gk k s = riemannZeta s ^ k - ∑ j ∈ Finset.range k, ck k j * ((s - 1) ^ (k - j))⁻¹ := by
    rw [zeta_pow_eq k hs1]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_pow]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_inv_sub_one_pow_le hs _)

lemma one_le_norm_sub_one_of_re {s : ℂ} (hs : 2 ≤ s.re) : 1 ≤ ‖s - 1‖ := by
  have := Complex.abs_re_le_norm (s - 1)
  rw [sub_re, one_re, abs_of_nonneg (by linarith)] at this
  linarith

lemma one_le_norm_sub_one_of_im {s : ℂ} (hs : 1 ≤ |s.im|) : 1 ≤ ‖s - 1‖ := by
  have := Complex.abs_im_le_norm (s - 1)
  rw [sub_im, one_im, sub_zero] at this
  linarith

/-! ### The window around `log X` -/

/-- If `f ≥ 0` is continuous and monotone on `[0, ∞)`, `S` is continuous with `0 ≤ S ≤ 1`, `S = 1` on
`(−∞, a]` and `S = 0` on `[b, ∞)`, and `0 ≤ a ≤ c ≤ b`, then
`|∫_0^∞ f S − ∫_0^c f| ≤ 2(b − a) f(b)`. -/
lemma abs_integral_mul_sub_le {f S : ℝ → ℝ} (hfc : Continuous f) (hf0 : ∀ u, 0 ≤ u → 0 ≤ f u)
    (hfm : MonotoneOn f (Ici 0)) (hSc : Continuous S) (hS0 : ∀ u, 0 ≤ S u) (hS1 : ∀ u, S u ≤ 1)
    {a b c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hSa : ∀ u, u ≤ a → S u = 1) (hSb : ∀ u, b ≤ u → S u = 0) :
    |(∫ u in Ioi 0, f u * S u) - ∫ u in (0 : ℝ)..c, f u| ≤ 2 * (b - a) * f b := by
  have hb : 0 ≤ b := ha.trans (hac.trans hcb)
  have hfS : Continuous fun u ↦ f u * S u := hfc.mul hSc
  -- `∫_0^∞ f S = ∫_0^b f S`
  have h1 : (∫ u in Ioi 0, f u * S u) = ∫ u in (0 : ℝ)..b, f u * S u := by
    rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun u hu ↦ ?_
    have hub : b < u := by
      by_contra h
      exact hu.2 ⟨hu.1, not_lt.1 h⟩
    rw [hSb u hub.le, mul_zero]
  have hii : ∀ x y : ℝ, IntervalIntegrable (fun u ↦ f u * S u) volume x y :=
    fun x y ↦ hfS.intervalIntegrable x y
  have hfi : ∀ x y : ℝ, IntervalIntegrable f volume x y := fun x y ↦ hfc.intervalIntegrable x y
  have h2 : (∫ u in (0 : ℝ)..a, f u * S u) = ∫ u in (0 : ℝ)..a, f u := by
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le ha] at hu
    simp only [hSa u hu.2, mul_one]
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (hii 0 a) (hii a b), h2,
    ← intervalIntegral.integral_add_adjacent_intervals (hfi 0 a) (hfi a c)]
  have hfb : ∀ u ∈ Icc a b, |f u| ≤ f b := fun u hu ↦ by
    rw [abs_of_nonneg (hf0 u (ha.trans hu.1))]
    exact hfm (ha.trans hu.1) hb hu.2
  have e3 : ‖∫ u in a..b, f u * S u‖ ≤ f b * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    rw [uIoc_of_le (hac.trans hcb)] at hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hS0 u)]
    calc |f u| * S u ≤ f b * 1 :=
          mul_le_mul (hfb u ⟨hu.1.le, hu.2⟩) (hS1 u) (hS0 u) (by linarith [hfb u ⟨hu.1.le, hu.2⟩, abs_nonneg (f u)])
      _ = f b := mul_one _
  have e4 : ‖∫ u in a..c, f u‖ ≤ f b * |c - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    rw [uIoc_of_le hac] at hu
    exact hfb u ⟨hu.1.le, hu.2.trans hcb⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ b - a), Real.norm_eq_abs] at e3
  rw [abs_of_nonneg (by linarith : 0 ≤ c - a), Real.norm_eq_abs] at e4
  have hfb0 : 0 ≤ f b := hf0 b hb
  calc |(∫ u in (0 : ℝ)..a, f u) + (∫ u in a..b, f u * S u) - ((∫ u in (0 : ℝ)..a, f u) + ∫ u in a..c, f u)|
      = |(∫ u in a..b, f u * S u) - ∫ u in a..c, f u| := by ring_nf
    _ ≤ |∫ u in a..b, f u * S u| + |∫ u in a..c, f u| := abs_sub _ _
    _ ≤ f b * (b - a) + f b * (c - a) := add_le_add e3 e4
    _ ≤ 2 * (b - a) * f b := by nlinarith

/-! ### The sandwich -/

variable {ν : ℝ → ℝ}

/-- For `f ≥ 0` with `f(0) = 0`: `Σ_n f(n) Smooth1(n/Y) ≤ Σ_{1 ≤ n ≤ X} f(n)` when `X/Y = 1 + 2 log 2 · ε`. -/
lemma tsum_smooth_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {X : ℝ} (Xpos : 0 < X) :
    ∑' n, f n * Smooth1 ν ε (n / (X / (1 + 2 * Real.log 2 * ε))) ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n := by
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above suppν
  have hd : 0 < 1 + 2 * Real.log 2 * ε := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  set Y := X / (1 + 2 * Real.log 2 * ε) with hYdef
  have Ypos : 0 < Y := div_pos Xpos hd
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊) fun n hn ↦ ?_]
  · refine Finset.sum_le_sum fun n hn ↦ ?_
    have hn0 : 0 < n := (Finset.mem_Icc.1 hn).1
    exact mul_le_of_le_one_right (hf n)
      (Smooth1LeOne νnonneg mass_one εpos (div_pos (Nat.cast_pos.2 hn0) Ypos))
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hf0, zero_mul]
    · have hnX : X < n := by
        by_contra h
        exact hn (Finset.mem_Icc.2 ⟨hn0, Nat.le_floor (not_lt.1 h)⟩)
      rw [habove ε _ ⟨εpos, ε_lt_one⟩ ?_, mul_zero]
      rw [le_div_iff₀ Ypos, hYdef, hc₂]
      field_simp
      linarith

/-- For `f ≥ 0` with `f(0) = 0`: `Σ_{1 ≤ n ≤ X} f(n) ≤ Σ_n f(n) Smooth1(n/Y)` when `X/Y = 1 − log 2 · ε`. -/
lemma le_tsum_smooth {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {X : ℝ} (Xpos : 0 < X) :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n ≤ ∑' n, f n * Smooth1 ν ε (n / (X / (1 - Real.log 2 * ε))) := by
  obtain ⟨c₁, -, hc₁, hbelow⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above suppν
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 1 - Real.log 2 * ε := by nlinarith
  set Y := X / (1 - Real.log 2 * ε) with hYdef
  have Ypos : 0 < Y := div_pos Xpos hd
  -- the terms vanish beyond `N`
  set N : ℕ := ⌊Y * (1 + c₂ * ε)⌋₊ + 1 with hNdef
  have hvanish : ∀ n ∉ Finset.range N, f n * Smooth1 ν ε (n / Y) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have : Y * (1 + c₂ * ε) < n := by
      have := Nat.lt_floor_add_one (Y * (1 + c₂ * ε))
      have h' : ((⌊Y * (1 + c₂ * ε)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h'
      linarith
    rw [habove ε _ ⟨εpos, ε_lt_one⟩ (by rw [le_div_iff₀ Ypos]; linarith), mul_zero]
  have hsum : Summable fun n ↦ f n * Smooth1 ν ε (n / Y) :=
    summable_of_ne_finset_zero hvanish
  calc ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * Smooth1 ν ε (n / Y) := by
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.1 hn
        have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff Xpos.le).1 hnX
        rw [hbelow ε _ εpos (div_pos (Nat.cast_pos.2 hn1) Ypos) ?_, mul_one]
        rw [div_le_iff₀ Ypos, hYdef, hc₁]
        field_simp
        linarith
    _ ≤ ∑' n, f n * Smooth1 ν ε (n / Y) :=
        hsum.sum_le_tsum _ fun n _ ↦ by
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · rw [hf0, zero_mul]
          · exact mul_nonneg (hf n) (Smooth1Nonneg νnonneg (div_pos (Nat.cast_pos.2 hn0) Ypos) εpos)


/-! ### The smoothed divisor sum -/

/-- The coefficients `d_k(n)`, complex. -/
noncomputable abbrev dkc (k : ℕ) : ℕ → ℂ := fun n ↦ ((dk k n : ℕ) : ℂ)

/-- The principal-part integral `J_m(Y) = ∫_0^∞ (u^{m−1}/(m−1)!) e^u Smooth1(e^u/Y) du`. -/
noncomputable def Jm (ν : ℝ → ℝ) (ε : ℝ) (m : ℕ) (Y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ (m - 1) / ((m - 1).factorial : ℝ) * Real.exp u *
    Smooth1 ν ε (Real.exp u / Y)

lemma verticalIntegral'_integrand_pow {m : ℕ} (hm : 1 ≤ m) (diffν : ContDiff ℝ 1 ν)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {Y : ℝ} (Ypos : 0 < Y) :
    VerticalIntegral' (integrand ν ε Y fun s ↦ ((s - 1) ^ m)⁻¹) 2 = (Jm ν ε m Y : ℂ) := by
  have h := verticalIntegral_inv_sub_one_pow hm diffν νnonneg suppν mass_one εpos ε_lt_one Ypos
  refine h.trans ?_
  rw [Jm, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  push_cast
  rfl

/-- **The smoothed divisor sum**: `Σ_n d_k(n)Smooth1(n/Y) = Σ_{j<k} c_j J_{k−j}(Y) + G(Y)` with
`G(Y) = (1/2πi) ∫_{(2)} g_k(s)𝓜(Smooth1)(s)Y^s ds`. -/
theorem smoothedSum_dk_eq {k : ℕ} (hk : 1 ≤ k) (diffν : ContDiff ℝ 1 ν)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {Y : ℝ} (Ypos : 0 < Y) :
    smoothedSum ν ε Y (dkc k) = ∑ j ∈ Finset.range k, ck k j * (Jm ν ε (k - j) Y : ℂ) +
      VerticalIntegral' (integrand ν ε Y (gk k)) 2 := by
  have h2 : (1 : ℝ) < ((2 : ℝ) : ℂ).re := by norm_num
  have hS := (LSeries_dk hk h2).1
  rw [← verticalIntegral_eq_smoothedSum (by simp) diffν νnonneg suppν mass_one εpos ε_lt_one Ypos
    (by norm_num : (1 : ℝ) < 2) le_rfl hS]
  have hM2 : Integrable fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I) :=
    SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one
      (by norm_num) le_rfl
  have hre : ∀ t : ℝ, (((2 : ℝ) : ℂ) + t * I).re = 2 := fun t ↦ by simp
  have hone : ∀ t : ℝ, 1 ≤ ‖((2 : ℝ) : ℂ) + t * I - 1‖ :=
    fun t ↦ one_le_norm_sub_one_of_re (by rw [hre])
  have hne : ∀ t : ℝ, ((2 : ℝ) : ℂ) + t * I ≠ 1 := fun t h ↦ by
    have := hone t; rw [h, sub_self, norm_zero] at this; norm_num at this
  -- integrability of the pieces on `Re s = 2`
  have hintP : ∀ m : ℕ, Integrable fun t : ℝ ↦ integrand ν ε Y (fun s ↦ ((s - 1) ^ m)⁻¹)
      ((2 : ℝ) + t * I) := by
    intro m
    refine Integrable.mono' (hM2.norm.mul_const (Y ^ (2 : ℝ)))
      (continuous_integrand_line (by norm_num) ?_ diffν νnonneg suppν mass_one εpos ε_lt_one
        Ypos).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    · exact Continuous.inv₀ (by fun_prop) fun t ↦ pow_ne_zero _ (sub_ne_zero.2 (hne t))
    · rw [norm_integrand Ypos, hre]
      calc ‖((((2 : ℝ) : ℂ) + t * I - 1) ^ m)⁻¹‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ *
            Y ^ (2 : ℝ) ≤ 1 * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ * Y ^ (2 : ℝ) := by
            gcongr
            exact norm_inv_sub_one_pow_le (hone t) m
        _ = _ := by ring
  have hintG : Integrable fun t : ℝ ↦ integrand ν ε Y (gk k) ((2 : ℝ) + t * I) := by
    set B : ℝ := ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ^ k + ∑ j ∈ Finset.range k, ‖ck k j‖
    refine Integrable.mono' (hM2.norm.const_mul (B * Y ^ (2 : ℝ)))
      (continuous_integrand_line (by norm_num) ((differentiable_gk k).continuous.comp (by fun_prop))
        diffν νnonneg suppν mass_one εpos ε_lt_one Ypos).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [norm_integrand Ypos, hre]
    have hg : ‖gk k (((2 : ℝ) : ℂ) + t * I)‖ ≤ B := by
      refine (norm_gk_le k (hone t)).trans ?_
      exact add_le_add_left (pow_le_pow_left₀ (norm_nonneg _)
        (HalfPlaneLindelof.norm_zeta_le_three_halves (by rw [hre]; norm_num)) k) _
    calc ‖gk k (((2 : ℝ) : ℂ) + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ *
          Y ^ (2 : ℝ) ≤ B * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ * Y ^ (2 : ℝ) := by
          gcongr
      _ = _ := by ring
  -- the integrand of `L(d_k, s)` on `Re s = 2`, split
  have hpt : ∀ t : ℝ, integrand ν ε Y (LSeries (dkc k)) ((2 : ℝ) + t * I) =
      ∑ j ∈ Finset.range k, ck k j * integrand ν ε Y (fun s ↦ ((s - 1) ^ (k - j))⁻¹)
        ((2 : ℝ) + t * I) + integrand ν ε Y (gk k) ((2 : ℝ) + t * I) := by
    intro t
    have hL : LSeries (dkc k) (((2 : ℝ) : ℂ) + t * I) = riemannZeta (((2 : ℝ) : ℂ) + t * I) ^ k :=
      (LSeries_dk hk (by rw [hre]; norm_num)).2
    simp only [integrand]
    rw [hL, zeta_pow_eq k (hne t), add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsplit : VerticalIntegral' (integrand ν ε Y (LSeries (dkc k))) 2 =
      ∑ j ∈ Finset.range k, ck k j * VerticalIntegral' (integrand ν ε Y fun s ↦ ((s - 1) ^ (k - j))⁻¹) 2 +
        VerticalIntegral' (integrand ν ε Y (gk k)) 2 := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
    simp_rw [hpt]
    rw [integral_add (integrable_finsetSum _ fun j _ ↦ (hintP (k - j)).const_mul _) hintG,
      integral_finsetSum _ fun j _ ↦ (hintP (k - j)).const_mul _]
    simp_rw [integral_const_mul]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [verticalIntegral'_integrand_pow (by omega) diffν νnonneg suppν mass_one εpos ε_lt_one Ypos]


/-! ### The remainder in a zero-free half-plane -/

/-- **The remainder.** If `ζ ≠ 0` on `Re s > θ` (`0 ≤ θ < 1`), `θ < θ' < 1` and `0 < κ ≤ 1`, there is `K` with
`|(1/2πi) ∫_{(2)} g_k(s)𝓜(Smooth1)(s)Y^s ds| ≤ Kε^{−κ}Y^{θ'}` for `0 < ε < 1` and `Y ≥ 1`. -/
theorem norm_remainder_le {θ θ' κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθθ' : θ < θ') (hθ'1 : θ' < 1)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {k : ℕ} (hk : 1 ≤ k) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ Y : ℝ, 1 ≤ Y →
      ‖VerticalIntegral' (integrand ν ε Y (gk k)) 2‖ ≤ K * ε ^ (-κ) * Y ^ θ' := by
  have hθ'0 : 0 < θ' := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ε₁ : ℝ := κ / (2 * k) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hkε₁ : (k : ℝ) * ε₁ = κ / 2 := by rw [hε₁def]; field_simp
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν suppν hκ0.le hκ1 hθ'0 hθ'1.le
  obtain ⟨T, C, hTC⟩ := HalfPlaneLindelof.zeta_bound_of_zeroFree hθ0 hθ1 hθθ' hε₁ hzf
  set T' : ℝ := max T 1 with hT'def
  set C' : ℝ := max C 0 with hC'def
  set A : ℝ := ∑ j ∈ Finset.range k, ‖ck k j‖ with hAdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  -- `|g_k(σ + it)| ≤ C'^k |t|^{κ/2} + A` for `σ ≥ θ'`, `|t| ≥ T'`
  have hbig : ∀ σ t : ℝ, θ' ≤ σ → T' ≤ |t| → ‖gk k (σ + t * I)‖ ≤ C' ^ k * |t| ^ (κ / 2) + A := by
    intro σ t hσ ht
    have ht1 : 1 ≤ |t| := (le_max_right _ _).trans ht
    have him : 1 ≤ |((σ : ℂ) + t * I).im| := by simpa using ht1
    refine (norm_gk_le k (one_le_norm_sub_one_of_im him)).trans ?_
    gcongr
    have hz := (hTC σ t hσ ((le_max_left _ _).trans ht)).1
    calc ‖riemannZeta (σ + t * I)‖ ^ k ≤ (C' * |t| ^ ε₁) ^ k := by
          gcongr
          exact hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = C' ^ k * |t| ^ (κ / 2) := by
          rw [mul_pow, ← Real.rpow_natCast (|t| ^ ε₁), ← Real.rpow_mul (abs_nonneg t), mul_comm ε₁,
            hkε₁]
  -- linear growth on horizontal segments
  have hgrowth : ∀ σ t : ℝ, θ' ≤ σ → σ ≤ 2 → T' ≤ |t| → ‖gk k (σ + t * I)‖ ≤ (C' ^ k + A) * |t| := by
    intro σ t hσ _ ht
    have ht1 : 1 ≤ |t| := (le_max_right _ _).trans ht
    have hp : |t| ^ (κ / 2) ≤ |t| :=
      (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)).trans_eq (Real.rpow_one _)
    calc ‖gk k (σ + t * I)‖ ≤ C' ^ k * |t| ^ (κ / 2) + A := hbig σ t hσ ht
      _ ≤ C' ^ k * |t| + A * |t| := by
          gcongr
          · exact le_mul_of_one_le_right hA ht1
      _ = (C' ^ k + A) * |t| := by ring
  -- on `Re s = θ'`
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := -T') (b := T')).exists_bound_of_continuousOn
    ((differentiable_gk k).continuous.comp (by fun_prop : Continuous fun t : ℝ ↦ (θ' : ℂ) + t * I)).continuousOn
  set Kg : ℝ := max C₀ 0 + C' ^ k + A with hKgdef
  have hline : ∀ t : ℝ, ‖gk k (θ' + t * I)‖ ≤ Kg * (1 + |t|) ^ (κ / 2) := by
    intro t
    have h1 : 1 ≤ (1 + |t|) ^ (κ / 2) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
    by_cases ht : |t| ≤ T'
    · have hmem : t ∈ Icc (-T') T' := by
        rw [mem_Icc]
        constructor <;> linarith [abs_le.1 ht]
      calc ‖gk k (θ' + t * I)‖ ≤ max C₀ 0 := (hC₀ t hmem).trans (le_max_left _ _)
        _ ≤ max C₀ 0 * (1 + |t|) ^ (κ / 2) := le_mul_of_one_le_right (le_max_right _ _) h1
        _ ≤ Kg * (1 + |t|) ^ (κ / 2) := by
            gcongr
            rw [hKgdef]
            have : 0 ≤ C' ^ k := pow_nonneg (le_max_right _ _) _
            linarith
    · rw [not_le] at ht
      calc ‖gk k (θ' + t * I)‖ ≤ C' ^ k * |t| ^ (κ / 2) + A := hbig θ' t le_rfl ht.le
        _ ≤ C' ^ k * (1 + |t|) ^ (κ / 2) + A * (1 + |t|) ^ (κ / 2) := by
            gcongr
            · linarith
            · exact le_mul_of_one_le_right hA h1
        _ ≤ Kg * (1 + |t|) ^ (κ / 2) := by
            rw [← add_mul]
            gcongr
            rw [hKgdef]
            linarith [le_max_right C₀ 0]
  -- on `Re s = 2`
  have hB2 : ∀ t : ℝ, ‖gk k ((2 : ℝ) + t * I)‖ ≤ ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ^ k + A := by
    intro t
    have hre : (((2 : ℝ) : ℂ) + t * I).re = 2 := by simp
    refine (norm_gk_le k (one_le_norm_sub_one_of_re (by rw [hre]))).trans ?_
    exact add_le_add_left (pow_le_pow_left₀ (norm_nonneg _)
      (HalfPlaneLindelof.norm_zeta_le_three_halves (by rw [hre]; norm_num)) k) _
  set r : ℝ := 1 + κ / 2 with hrdef
  have hIr : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-r) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)
    simpa only [Real.norm_eq_abs] using this
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIrdef
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t ↦ by positivity
  have hKg0 : 0 ≤ Kg := by
    rw [hKgdef]
    have : 0 ≤ C' ^ k := pow_nonneg (le_max_right _ _) _
    linarith [le_max_right C₀ 0]
  refine ⟨Kg * KM * Ir, by positivity, fun ε εpos ε_lt_one Y hY ↦ ?_⟩
  have Ypos : 0 < Y := by linarith
  have hpt : ∀ t : ℝ, ‖integrand ν ε Y (gk k) (θ' + t * I)‖ ≤
      Kg * KM * ε ^ (-κ) * Y ^ θ' * (1 + |t|) ^ (-r) := by
    intro t
    rw [norm_integrand Ypos]
    have hre : ((θ' : ℂ) + t * I).re = θ' := by simp
    rw [hre]
    have hpow : (1 + |t|) ^ (κ / 2) * (1 + |t|) ^ (-(1 + κ)) = (1 + |t|) ^ (-r) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      rw [hrdef]
      ring
    calc ‖gk k (θ' + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (θ' + t * I)‖ * Y ^ θ'
        ≤ (Kg * (1 + |t|) ^ (κ / 2)) * (KM * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ))) * Y ^ θ' := by
          gcongr
          · exact hline t
          · exact hKM ε εpos ε_lt_one t
      _ = Kg * KM * ε ^ (-κ) * Y ^ θ' * ((1 + |t|) ^ (κ / 2) * (1 + |t|) ^ (-(1 + κ))) := by ring
      _ = Kg * KM * ε ^ (-κ) * Y ^ θ' * (1 + |t|) ^ (-r) := by rw [hpow]
  have hint' : Integrable fun t : ℝ ↦ integrand ν ε Y (gk k) (θ' + t * I) :=
    Integrable.mono' (hIr.const_mul (Kg * KM * ε ^ (-κ) * Y ^ θ'))
      (continuous_integrand_line hθ'0 ((differentiable_gk k).continuous.comp (by fun_prop)) diffν
        νnonneg suppν mass_one εpos ε_lt_one Ypos).aestronglyMeasurable (Eventually.of_forall hpt)
  rw [verticalIntegral_integrand_shift hθ'0 (by linarith) (fun s _ ↦ (differentiable_gk k) s) hB2
    hgrowth diffν νnonneg suppν mass_one εpos ε_lt_one hY hint']
  calc _ ≤ ∫ t, Kg * KM * ε ^ (-κ) * Y ^ θ' * (1 + |t|) ^ (-r) :=
        norm_verticalIntegral'_le (hIr.const_mul _) hpt
    _ = Kg * KM * ε ^ (-κ) * Y ^ θ' * Ir := integral_const_mul _ _
    _ = Kg * KM * Ir * ε ^ (-κ) * Y ^ θ' := by ring


/-! ### The main term -/

/-- `L_m(X) = ∫_0^{log X} e^u u^{m−1}/(m−1)! du`. -/
noncomputable def Lm (m : ℕ) (X : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.log X, Real.exp u * (u ^ (m - 1) / (m - 1).factorial)

lemma Lm_eq {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) :
    Lm m X = X * (pm m).eval (Real.log X) - (pm m).eval 0 := by
  have h := integral_exp_mul_pow_div (m - 1) hX
  rw [Nat.sub_add_cancel hm] at h
  exact h

/-- **The window.** If `1 ≤ Y(1 − log 2 · ε) ≤ X ≤ Y(1 + 2 log 2 · ε) ≤ 3X`, then
`|J_m(Y) − L_m(X)| ≤ 2 log((1 + 2 log 2 · ε)/(1 − log 2 · ε)) · 3X (log 3X)^{m−1}`. -/
lemma abs_Jm_sub_Lm_le {m : ℕ} (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {X Y : ℝ}
    (hY1 : 1 ≤ Y * (1 - Real.log 2 * ε)) (hYX : Y * (1 - Real.log 2 * ε) ≤ X)
    (hXY : X ≤ Y * (1 + 2 * Real.log 2 * ε)) (hY3 : Y * (1 + 2 * Real.log 2 * ε) ≤ 3 * X) :
    |Jm ν ε m Y - Lm m X| ≤
      2 * Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) * (3 * X * Real.log (3 * X) ^ (m - 1)) := by
  obtain ⟨c₁, -, hc₁, hbelow⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above suppν
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd1 : 0 < 1 - Real.log 2 * ε := by
    have := Real.log_two_lt_d9
    nlinarith
  have hd2 : 0 < 1 + 2 * Real.log 2 * ε := by positivity
  have Ypos : 0 < Y := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hX0 : 0 < X := by linarith
  set a : ℝ := Real.log (Y * (1 - Real.log 2 * ε)) with hadef
  set b : ℝ := Real.log (Y * (1 + 2 * Real.log 2 * ε)) with hbdef
  have ha0 : 0 ≤ a := Real.log_nonneg hY1
  have hac : a ≤ Real.log X := Real.log_le_log (by linarith) hYX
  have hcb : Real.log X ≤ b := Real.log_le_log hX0 hXY
  set f : ℝ → ℝ := fun u ↦ u ^ (m - 1) / ((m - 1).factorial : ℝ) * Real.exp u with hfdef
  set Sm : ℝ → ℝ := fun u ↦ Smooth1 ν ε (Real.exp u / Y) with hSdef
  have hfc : Continuous f := by fun_prop
  have hf0 : ∀ u, 0 ≤ u → 0 ≤ f u := fun u hu ↦
    mul_nonneg (div_nonneg (pow_nonneg hu _) (by positivity)) (Real.exp_pos u).le
  have hfm : MonotoneOn f (Ici 0) := by
    refine MonotoneOn.mul (fun x hx y _ hxy ↦ ?_) (Real.exp_monotone.monotoneOn _)
      (fun x hx ↦ div_nonneg (pow_nonneg hx _) (by positivity)) (fun x _ ↦ (Real.exp_pos x).le)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity)
  have hpos : ∀ u : ℝ, 0 < Real.exp u / Y := fun u ↦ div_pos (Real.exp_pos u) Ypos
  have hSc : Continuous Sm := by
    refine continuous_iff_continuousAt.2 fun u ↦ ?_
    have h1 : ContinuousAt (fun u : ℝ ↦ Real.exp u / Y) u := by fun_prop
    exact ContinuousAt.comp (g := fun x ↦ Smooth1 ν ε x)
      (Smooth1ContinuousAt diffν νnonneg suppν εpos (hpos u)) h1
  have hS0 : ∀ u, 0 ≤ Sm u := fun u ↦ Smooth1Nonneg νnonneg (hpos u) εpos
  have hS1 : ∀ u, Sm u ≤ 1 := fun u ↦ Smooth1LeOne νnonneg mass_one εpos (hpos u)
  have hSa : ∀ u, u ≤ a → Sm u = 1 := by
    intro u hu
    refine hbelow ε _ εpos (hpos u) ?_
    rw [div_le_iff₀ Ypos, hc₁]
    have := Real.exp_le_exp.2 hu
    rw [hadef, Real.exp_log (by positivity)] at this
    linarith
  have hSb : ∀ u, b ≤ u → Sm u = 0 := by
    intro u hu
    refine habove ε _ ⟨εpos, ε_lt_one⟩ ?_
    rw [le_div_iff₀ Ypos, hc₂]
    have := Real.exp_le_exp.2 hu
    rw [hbdef, Real.exp_log (by positivity)] at this
    linarith
  have hmain := abs_integral_mul_sub_le hfc hf0 hfm hSc hS0 hS1 ha0 hac hcb hSa hSb
  have hJ : Jm ν ε m Y = ∫ u in Ioi 0, f u * Sm u := rfl
  have hL : Lm m X = ∫ u in (0 : ℝ)..Real.log X, f u := by
    rw [Lm]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [hfdef]
    ring
  rw [hJ, hL]
  refine hmain.trans ?_
  have hba : b - a = Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) := by
    rw [hbdef, hadef, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hb0 : 0 ≤ b := ha0.trans (hac.trans hcb)
  have heb : Real.exp b ≤ 3 * X := by
    rw [hbdef, Real.exp_log (by positivity)]
    exact hY3
  have hb3 : b ≤ Real.log (3 * X) := by
    rw [← Real.exp_le_exp, Real.exp_log (show (0 : ℝ) < 3 * X by positivity)]
    exact heb
  have hfb : f b ≤ 3 * X * Real.log (3 * X) ^ (m - 1) := by
    simp only [hfdef]
    have h1 : b ^ (m - 1) / ((m - 1).factorial : ℝ) ≤ Real.log (3 * X) ^ (m - 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc b ^ (m - 1) ≤ Real.log (3 * X) ^ (m - 1) := pow_le_pow_left₀ hb0 hb3 _
        _ ≤ Real.log (3 * X) ^ (m - 1) * ((m - 1).factorial : ℝ) :=
          le_mul_of_one_le_right (pow_nonneg (hb0.trans hb3) _)
            (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
    calc b ^ (m - 1) / ((m - 1).factorial : ℝ) * Real.exp b ≤ Real.log (3 * X) ^ (m - 1) * (3 * X) :=
          mul_le_mul h1 heb (Real.exp_pos b).le (pow_nonneg (hb0.trans hb3) _)
      _ = 3 * X * Real.log (3 * X) ^ (m - 1) := by ring
  have hlogpos : 0 ≤ Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) := by
    rw [← hba]
    linarith
  rw [hba]
  exact mul_le_mul_of_nonneg_left hfb (by linarith)

/-- `log((1 + 2 log 2 · ε)/(1 − log 2 · ε)) ≤ 5ε` for `0 < ε ≤ 1/2`. -/
lemma log_window_le {ε : ℝ} (εpos : 0 < ε) (hε : ε ≤ 1 / 2) :
    Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) ≤ 5 * ε := by
  have h1 := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd1 : 0 < 1 - Real.log 2 * ε := by nlinarith
  have h2 : Real.log 2 * ε ≤ 0.6931471808 * (1 / 2) := mul_le_mul h1.le hε εpos.le (by norm_num)
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [div_sub_one hd1.ne', div_le_iff₀ hd1]
  nlinarith [mul_nonneg εpos.le (show 0 ≤ 5 - 5 * (Real.log 2 * ε) - 3 * Real.log 2 by linarith)]


/-! ### The divisor problems -/

open Polynomial in
/-- The main term's polynomial `P_k = Σ_{j<k} Re(c_j) p_{k−j}`, of degree less than `k`. -/
noncomputable def Pk (k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range k, C (ck k j).re * pm (k - j)

open Polynomial in
lemma natDegree_Pk {k : ℕ} (hk : 1 ≤ k) : (Pk k).natDegree < k := by
  refine (natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_).trans_lt (Nat.sub_lt hk one_pos)
  rw [Finset.mem_range] at hj
  refine (natDegree_C_mul_le _ _).trans ?_
  have e : k - j = (k - j - 1) + 1 := by omega
  rw [e]
  exact (natDegree_pm_succ _).trans (by omega)

/-- `c_0 = Z(1)^k = 1`. -/
lemma ck_zero (k : ℕ) : ck k 0 = 1 := by
  simp [ck, zk, Zr]

open Polynomial in
lemma coeff_pm_succ (m : ℕ) : (pm (m + 1)).coeff m = ((m.factorial : ℝ))⁻¹ := by
  have h0 : (pm m).coeff m = 0 := by
    rcases m with _ | m
    · simp [pm]
    · exact coeff_eq_zero_of_natDegree_lt ((natDegree_pm_succ m).trans_lt (Nat.lt_succ_self m))
  rw [pm, coeff_sub, coeff_C_mul_X_pow, h0, sub_zero]
  simp

open Polynomial in
/-- The leading coefficient: `P_k = v^{k−1}/(k−1)! + (lower terms)`. -/
lemma coeff_Pk {k : ℕ} (hk : 1 ≤ k) : (Pk k).coeff (k - 1) = ((k - 1).factorial : ℝ)⁻¹ := by
  rw [Pk, finsetSum_coeff, Finset.sum_eq_single 0]
  · rw [coeff_C_mul, ck_zero, Complex.one_re, one_mul, Nat.sub_zero]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact coeff_pm_succ m
  · intro j hj hj0
    rw [Finset.mem_range] at hj
    rw [coeff_C_mul]
    have e : k - j = (k - j - 1) + 1 := by omega
    rw [e, coeff_eq_zero_of_natDegree_lt ((natDegree_pm_succ _).trans_lt (by omega)), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

open Polynomial in
/-- `P_k` has degree exactly `k − 1`. -/
lemma natDegree_Pk_eq {k : ℕ} (hk : 1 ≤ k) : (Pk k).natDegree = k - 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (Nat.le_sub_one_of_lt (natDegree_Pk hk))
    (by rw [coeff_Pk hk]; positivity)

open Polynomial in
lemma sum_Lm_eq (k : ℕ) {X : ℝ} (hX : 0 < X) :
    ∑ j ∈ Finset.range k, (ck k j).re * Lm (k - j) X =
      X * (Pk k).eval (Real.log X) - (Pk k).eval 0 := by
  simp only [Pk, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [Lm_eq (by omega) hX]
  ring

/-- The real smoothed divisor sum `Σ_n d_k(n) Smooth1(n/Y)`, and its distance from the main term:
`|Σ_n d_k(n)Smooth1(n/Y) − Σ_{j<k} Re(c_j) L_{k−j}(X)| ≤ 30εX(log 3X)^{k−1} Σ_j |Re c_j| + |G(Y)|`. -/
lemma abs_tsum_sub_main_le {k : ℕ} (hk : 1 ≤ k) (diffν : ContDiff ℝ 1 ν)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (hε : ε ≤ 1 / 2) {X Y : ℝ}
    (hY1 : 1 ≤ Y * (1 - Real.log 2 * ε)) (hYX : Y * (1 - Real.log 2 * ε) ≤ X)
    (hXY : X ≤ Y * (1 + 2 * Real.log 2 * ε)) (hY3 : Y * (1 + 2 * Real.log 2 * ε) ≤ 3 * X)
    (hlog1 : 1 ≤ Real.log (3 * X)) :
    |(∑' n, (dk k n : ℝ) * Smooth1 ν ε (n / Y)) - ∑ j ∈ Finset.range k, (ck k j).re * Lm (k - j) X| ≤
      30 * ε * X * Real.log (3 * X) ^ (k - 1) * ∑ j ∈ Finset.range k, |(ck k j).re| +
        ‖VerticalIntegral' (integrand ν ε Y (gk k)) 2‖ := by
  have ε_lt_one : ε < 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd1 : 0 < 1 - Real.log 2 * ε := by
    have := Real.log_two_lt_d9
    nlinarith
  have Ypos : 0 < Y := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hX0 : 0 < X := by
    have : 0 < Y * (1 - Real.log 2 * ε) := by positivity
    linarith
  -- the real smoothed sum is the real part of the complex one
  have hR : ((∑' n, (dk k n : ℝ) * Smooth1 ν ε (n / Y) : ℝ) : ℂ) = smoothedSum ν ε Y (dkc k) := by
    rw [Complex.ofReal_tsum, smoothedSum]
    congr 1
    funext n
    push_cast
    rfl
  have hid := smoothedSum_dk_eq hk diffν νnonneg suppν mass_one εpos ε_lt_one Ypos
  have hre : (∑' n, (dk k n : ℝ) * Smooth1 ν ε (n / Y)) =
      ∑ j ∈ Finset.range k, (ck k j).re * Jm ν ε (k - j) Y +
        (VerticalIntegral' (integrand ν ε Y (gk k)) 2).re := by
    have := congrArg Complex.re (hR.trans hid)
    rw [Complex.ofReal_re] at this
    rw [this, Complex.add_re, Complex.re_sum]
    simp only [Complex.re_mul_ofReal]
  rw [hre]
  have hwin : ∀ j ∈ Finset.range k, |(ck k j).re * Jm ν ε (k - j) Y - (ck k j).re * Lm (k - j) X| ≤
      |(ck k j).re| * (30 * ε * X * Real.log (3 * X) ^ (k - 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← mul_sub, abs_mul]
    gcongr
    refine (abs_Jm_sub_Lm_le diffν νnonneg suppν mass_one εpos ε_lt_one hY1 hYX hXY hY3).trans ?_
    have hw := log_window_le εpos hε
    have hlp : Real.log (3 * X) ^ (k - j - 1) ≤ Real.log (3 * X) ^ (k - 1) :=
      pow_le_pow_right₀ hlog1 (by omega)
    have hl0 : 0 ≤ Real.log (3 * X) ^ (k - j - 1) := pow_nonneg (by linarith) _
    have hlw : 0 ≤ Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hd1]; nlinarith)
    calc 2 * Real.log ((1 + 2 * Real.log 2 * ε) / (1 - Real.log 2 * ε)) *
          (3 * X * Real.log (3 * X) ^ (k - j - 1))
        ≤ 2 * (5 * ε) * (3 * X * Real.log (3 * X) ^ (k - 1)) := by gcongr
      _ = 30 * ε * X * Real.log (3 * X) ^ (k - 1) := by ring
  calc |∑ j ∈ Finset.range k, (ck k j).re * Jm ν ε (k - j) Y +
        (VerticalIntegral' (integrand ν ε Y (gk k)) 2).re -
        ∑ j ∈ Finset.range k, (ck k j).re * Lm (k - j) X|
      = |∑ j ∈ Finset.range k, ((ck k j).re * Jm ν ε (k - j) Y - (ck k j).re * Lm (k - j) X) +
          (VerticalIntegral' (integrand ν ε Y (gk k)) 2).re| := by
        rw [Finset.sum_sub_distrib]
        ring_nf
    _ ≤ |∑ j ∈ Finset.range k, ((ck k j).re * Jm ν ε (k - j) Y - (ck k j).re * Lm (k - j) X)| +
          |(VerticalIntegral' (integrand ν ε Y (gk k)) 2).re| := abs_add_le _ _
    _ ≤ ∑ j ∈ Finset.range k, |(ck k j).re| * (30 * ε * X * Real.log (3 * X) ^ (k - 1)) +
          ‖VerticalIntegral' (integrand ν ε Y (gk k)) 2‖ :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hwin))
          (Complex.abs_re_le_norm _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- **One `X`.** With `K` from `norm_remainder_le` at `θ'` and `κ`: for `X ≥ 4` with `X^{θ'−1} ≤ 1/2` and
`(log 3X)^{k−1} ≤ 2^{k−1}X^κ`, `|Σ_{n≤X} d_k(n) − XP_k(log X)| ≤ (30 · 2^{k−1} Σ_j |Re c_j| + 3K + |P_k(0)|)
X^{θ'+κ}`. -/
lemma divisor_bound_at {k : ℕ} (hk : 1 ≤ k) (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) (mass_one : ∫ x in Ioi 0, ν x / x = 1)
    {θ' κ K : ℝ} (hθ'0 : 0 < θ') (hθ'1 : θ' < 1) (hκ0 : 0 < κ) (hK0 : 0 ≤ K)
    (hK : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ Y : ℝ, 1 ≤ Y →
      ‖VerticalIntegral' (integrand ν ε Y (gk k)) 2‖ ≤ K * ε ^ (-κ) * Y ^ θ')
    {X : ℝ} (hX4 : 4 ≤ X) (hεX : X ^ (θ' - 1) ≤ 1 / 2)
    (hlogX : Real.log (3 * X) ^ (k - 1) ≤ 2 ^ (k - 1) * X ^ κ) :
    |summ (fun n ↦ (dk k n : ℝ)) X - X * (Pk k).eval (Real.log X)| ≤
      (30 * (∑ j ∈ Finset.range k, |(ck k j).re|) * 2 ^ (k - 1) + 3 * K + |(Pk k).eval 0|) *
        X ^ (θ' + κ) := by
  have Xpos : 0 < X := by linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = X ^ (θ' - 1) := ⟨_, rfl⟩
  rw [← hεdef] at hεX
  have εpos : 0 < ε := hεdef ▸ Real.rpow_pos_of_pos Xpos _
  have ε_lt_one : ε < 1 := by linarith
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ j ∈ Finset.range k, |(ck k j).re| := ⟨_, rfl⟩
  rw [← hAdef]
  have hA : 0 ≤ A := hAdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hc1 : Real.log 2 * ε ≤ 0.6931471808 * (1 / 2) := mul_le_mul hl2.le hεX εpos.le (by norm_num)
  have hc0 : 0 < Real.log 2 * ε := mul_pos hlog2 εpos
  have hd1 : 0 < 1 - Real.log 2 * ε := by linarith
  have hd2 : 0 < 1 + 2 * Real.log 2 * ε := by linarith
  have hlog1 : 1 ≤ Real.log (3 * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  -- the two sandwich points
  obtain ⟨Yp, hYpdef⟩ : ∃ Y : ℝ, Y = X / (1 - Real.log 2 * ε) := ⟨_, rfl⟩
  obtain ⟨Ym, hYmdef⟩ : ∃ Y : ℝ, Y = X / (1 + 2 * Real.log 2 * ε) := ⟨_, rfl⟩
  have hYp1 : Yp * (1 - Real.log 2 * ε) = X := by rw [hYpdef]; field_simp
  have hYm2 : Ym * (1 + 2 * Real.log 2 * ε) = X := by rw [hYmdef]; field_simp
  have hYpos : 0 < Yp := hYpdef ▸ div_pos Xpos hd1
  have hYmpos : 0 < Ym := hYmdef ▸ div_pos Xpos hd2
  have hratio : 1 + 2 * Real.log 2 * ε ≤ 3 * (1 - Real.log 2 * ε) := by linarith
  have hratio' : 1 + 2 * Real.log 2 * ε ≤ 4 * (1 - Real.log 2 * ε) := by linarith
  have hle : 1 - Real.log 2 * ε ≤ 1 + 2 * Real.log 2 * ε := by linarith
  have hd1' : 1 - Real.log 2 * ε ≤ 1 := by linarith
  -- `Y⁺`
  have hp1 : X ≤ Yp * (1 + 2 * Real.log 2 * ε) := by
    rw [← hYp1]
    exact mul_le_mul_of_nonneg_left hle hYpos.le
  have hp3 : Yp * (1 + 2 * Real.log 2 * ε) ≤ 3 * X := by
    rw [← hYp1]
    calc Yp * (1 + 2 * Real.log 2 * ε) ≤ Yp * (3 * (1 - Real.log 2 * ε)) :=
          mul_le_mul_of_nonneg_left hratio hYpos.le
      _ = 3 * (Yp * (1 - Real.log 2 * ε)) := by ring
  have hp := abs_tsum_sub_main_le hk diffν νnonneg suppν mass_one εpos hεX (Y := Yp)
    (by rw [hYp1]; linarith) hYp1.le hp1 hp3 hlog1
  -- `Y⁻`
  have hm1 : 1 ≤ Ym * (1 - Real.log 2 * ε) := by
    rw [hYmdef, div_mul_eq_mul_div, le_div_iff₀ hd2, one_mul]
    calc 1 + 2 * Real.log 2 * ε ≤ 4 * (1 - Real.log 2 * ε) := hratio'
      _ ≤ X * (1 - Real.log 2 * ε) := mul_le_mul_of_nonneg_right hX4 hd1.le
  have hm := abs_tsum_sub_main_le hk diffν νnonneg suppν mass_one εpos hεX (Y := Ym) hm1
    (by rw [← hYm2]; exact mul_le_mul_of_nonneg_left hle hYmpos.le) hYm2.ge
    (by rw [hYm2]; linarith) hlog1
  -- the two sandwich points lie in `[1, 3X]`
  have hYp_ge : X ≤ Yp := by
    rw [← hYp1]
    exact mul_le_of_le_one_right hYpos.le hd1'
  have hYp3 : Yp ≤ 3 * X := by
    rw [← hYp1]
    calc Yp = Yp * 1 := (mul_one _).symm
      _ ≤ Yp * (3 * (1 - Real.log 2 * ε)) := mul_le_mul_of_nonneg_left (by linarith) hYpos.le
      _ = 3 * (Yp * (1 - Real.log 2 * ε)) := by ring
  have hYm_ge : 1 ≤ Ym := hm1.trans (mul_le_of_le_one_right hYmpos.le hd1')
  have hYm3 : Ym ≤ 3 * X := by
    have : Ym ≤ X := by
      rw [← hYm2]
      exact le_mul_of_one_le_right hYmpos.le (by linarith)
    linarith
  -- the remainders
  have hεκ : ε ^ (-κ) * X ^ θ' ≤ X ^ (θ' + κ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have e : (θ' - 1) * -κ + θ' = θ' + κ - κ * θ' := by ring
    rw [e]
    linarith [mul_nonneg hκ0.le hθ'0.le]
  have hGbound : ∀ Y : ℝ, 1 ≤ Y → Y ≤ 3 * X →
      ‖VerticalIntegral' (integrand ν ε Y (gk k)) 2‖ ≤ 3 * K * X ^ (θ' + κ) := by
    intro Y hY1 hY3
    refine (hK ε εpos ε_lt_one Y hY1).trans ?_
    have hY0 : 0 ≤ Y := by linarith
    have h1 : Y ^ θ' ≤ (3 * X) ^ θ' := Real.rpow_le_rpow hY0 hY3 hθ'0.le
    have h2 : (3 * X) ^ θ' ≤ 3 * X ^ θ' := by
      rw [Real.mul_rpow (by norm_num) Xpos.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg Xpos.le _)
      calc (3 : ℝ) ^ θ' ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ'1.le
        _ = 3 := Real.rpow_one 3
    have hεk : 0 ≤ ε ^ (-κ) := Real.rpow_nonneg εpos.le _
    calc K * ε ^ (-κ) * Y ^ θ' ≤ K * ε ^ (-κ) * (3 * X ^ θ') :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hK0 hεk)
      _ = 3 * K * (ε ^ (-κ) * X ^ θ') := by ring
      _ ≤ 3 * K * X ^ (θ' + κ) := mul_le_mul_of_nonneg_left hεκ (by linarith)
  have hGp := hGbound Yp (by linarith) hYp3
  have hGm := hGbound Ym hYm_ge hYm3
  -- the smoothing window's error
  have hεX' : ε * X = X ^ θ' := by
    rw [hεdef, ← Real.rpow_add_one Xpos.ne', sub_add_cancel]
  have hE1 : 30 * ε * X * Real.log (3 * X) ^ (k - 1) * A ≤ 30 * A * 2 ^ (k - 1) * X ^ (θ' + κ) := by
    have hXθ : 0 ≤ X ^ θ' := Real.rpow_nonneg Xpos.le _
    calc 30 * ε * X * Real.log (3 * X) ^ (k - 1) * A =
          30 * A * (ε * X) * Real.log (3 * X) ^ (k - 1) := by ring
      _ = 30 * A * X ^ θ' * Real.log (3 * X) ^ (k - 1) := by rw [hεX']
      _ ≤ 30 * A * X ^ θ' * (2 ^ (k - 1) * X ^ κ) :=
          mul_le_mul_of_nonneg_left hlogX (mul_nonneg (mul_nonneg (by norm_num) hA) hXθ)
      _ = 30 * A * 2 ^ (k - 1) * (X ^ θ' * X ^ κ) := by ring
      _ = 30 * A * 2 ^ (k - 1) * X ^ (θ' + κ) := by rw [← Real.rpow_add Xpos]
  -- the sandwich
  have hlow := tsum_smooth_le (f := fun n ↦ (dk k n : ℝ)) (fun n ↦ Nat.cast_nonneg _) (by simp)
    νnonneg suppν mass_one εpos ε_lt_one Xpos
  have hupp := le_tsum_smooth (f := fun n ↦ (dk k n : ℝ)) (fun n ↦ Nat.cast_nonneg _) (by simp)
    νnonneg suppν mass_one εpos ε_lt_one Xpos
  beta_reduce at hlow hupp
  rw [← hYmdef] at hlow
  rw [← hYpdef] at hupp
  have hp' := abs_le.1 hp
  have hm' := abs_le.1 hm
  rw [sum_Lm_eq k Xpos, ← hAdef] at hp' hm'
  have hP0 : 1 ≤ X ^ (θ' + κ) := Real.one_le_rpow (by linarith) (by linarith)
  have hP0' : |(Pk k).eval 0| ≤ |(Pk k).eval 0| * X ^ (θ' + κ) :=
    le_mul_of_one_le_right (abs_nonneg _) hP0
  have h1 := le_abs_self ((Pk k).eval 0)
  have h2 := neg_abs_le ((Pk k).eval 0)
  rw [show summ (fun n ↦ (dk k n : ℝ)) X = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (dk k n : ℝ) from rfl, abs_le]
  constructor
  · linarith [hm'.1]
  · linarith [hp'.2]

/-- **The divisor problems in a zero-free half-plane.** If `ζ ≠ 0` on `Re s > θ` with `0 ≤ θ < 1`, then for
every `k ≥ 1` and `η > 0`, `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{θ+η})`, with `P_k = Pk k` of degree less
than `k` (`natDegree_Pk`). -/
theorem divisor_isBigO_of_zeroFree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ (fun n ↦ (dk k n : ℝ)) x - x * (Pk k).eval (Real.log x)) =O[atTop]
      fun x ↦ x ^ (θ + η) := by
  obtain ⟨η₀, hη₀def⟩ : ∃ η₀ : ℝ, η₀ = min η ((1 - θ) / 2) := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := hη₀def ▸ lt_min hη (by linarith)
  have hη₀η : η₀ ≤ η := hη₀def ▸ min_le_left _ _
  have hη₀θ : η₀ ≤ (1 - θ) / 2 := hη₀def ▸ min_le_right _ _
  obtain ⟨θ', hθ'def⟩ : ∃ θ' : ℝ, θ' = θ + η₀ / 4 := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = η₀ / 4 := ⟨_, rfl⟩
  have hθθ' : θ < θ' := by rw [hθ'def]; linarith
  have hθ'1 : θ' < 1 := by rw [hθ'def]; linarith
  have hθ'0 : 0 < θ' := by linarith
  have hκ0 : 0 < κ := by rw [hκdef]; linarith
  have hκ1 : κ ≤ 1 := by rw [hκdef]; linarith
  have hexp : θ' + κ ≤ θ + η := by rw [hθ'def, hκdef]; linarith
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨K, hK0, hK⟩ :=
    norm_remainder_le hθ0 hθ1 hθθ' hθ'1 hzf hk hκ0 hκ1 diffν νnonneg ν_supp mass_one
  -- `(log 3x)^{k−1} ≤ 2^{k−1}x^κ` eventually
  have hlog : ∀ᶠ x : ℝ in atTop, Real.log (3 * x) ^ (k - 1) ≤ 2 ^ (k - 1) * x ^ κ := by
    have h := (isLittleO_log_rpow_rpow_atTop ((k - 1 : ℕ) : ℝ) hκ0).bound one_pos
    filter_upwards [h, eventually_ge_atTop 3] with x hx hx3
    have hx0 : 0 < x := by linarith
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h3x : Real.log (3 * x) ≤ 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) hx0.ne']
      have := Real.log_le_log (by norm_num) hx3
      linarith
    have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlx _), Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
      one_mul, Real.rpow_natCast] at hx
    calc Real.log (3 * x) ^ (k - 1) ≤ (2 * Real.log x) ^ (k - 1) := pow_le_pow_left₀ hl3 h3x _
      _ = 2 ^ (k - 1) * Real.log x ^ (k - 1) := mul_pow _ _ _
      _ ≤ 2 ^ (k - 1) * x ^ κ := mul_le_mul_of_nonneg_left hx (by positivity)
  -- `ε = x^{θ'−1} ≤ 1/2` eventually
  have hε0 : ∀ᶠ x : ℝ in atTop, x ^ (θ' - 1) ≤ 1 / 2 := by
    have h := (tendsto_rpow_neg_atTop (y := 1 - θ') (by linarith)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [h] with x hx
    rwa [show θ' - 1 = -(1 - θ') by ring]
  have hA : 0 ≤ ∑ j ∈ Finset.range k, |(ck k j).re| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  refine IsBigO.of_bound
    (30 * (∑ j ∈ Finset.range k, |(ck k j).re|) * 2 ^ (k - 1) + 3 * K + |(Pk k).eval 0|) ?_
  filter_upwards [hlog, hε0, eventually_ge_atTop 4] with X hXl hXε hX4
  have hb := divisor_bound_at hk diffν νnonneg ν_supp mass_one hθ'0 hθ'1 hκ0 hK0 hK hX4 hXε hXl
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) hexp

/-- **The divisor problems at `11/12`**: `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{11/12+η})` for every `k ≥ 1`
and `η > 0`, from round 466's half-plane. -/
theorem divisor_isBigO_eleven_twelfths {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ (fun n ↦ (dk k n : ℝ)) x - x * (Pk k).eval (Real.log x)) =O[atTop]
      fun x ↦ x ^ (11 / 12 + η) :=
  divisor_isBigO_of_zeroFree (by norm_num) (by norm_num)
    (fun _ hs ↦ (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1) hk hη

/-- **The divisor problems at `Θ`**: `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{Θ+η})`. -/
theorem divisor_isBigO_Theta {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ (fun n ↦ (dk k n : ℝ)) x - x * (Pk k).eval (Real.log x)) =O[atTop]
      fun x ↦ x ^ (Theta + η) :=
  divisor_isBigO_of_zeroFree (by linarith [half_le_Theta]) (by linarith [Theta_le])
    (fun _ hs ↦ zeta_ne_zero_of_Theta_lt hs) hk hη

end DivisorExponent

#print axioms DivisorExponent.integral_pow_mul_cexp
#print axioms DivisorExponent.inv_sub_one_pow_eq_integral
#print axioms DivisorExponent.LSeries_dk
#print axioms DivisorExponent.zeta_pow_eq
#print axioms DivisorExponent.verticalIntegral_inv_sub_one_pow
#print axioms DivisorExponent.smoothedSum_dk_eq
#print axioms DivisorExponent.norm_remainder_le
#print axioms DivisorExponent.coeff_Pk
#print axioms DivisorExponent.natDegree_Pk_eq
#print axioms DivisorExponent.divisor_isBigO_of_zeroFree
#print axioms DivisorExponent.divisor_isBigO_eleven_twelfths
#print axioms DivisorExponent.divisor_isBigO_Theta
