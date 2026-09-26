import Mathlib

open Complex Real MeasureTheory intervalIntegral

noncomputable section

namespace Pilot1bt

/-- The witness' transform, `ĝ_a(t) = ∫_{-a}^{a} cosh(u/2) e^{itu} du` (1bt(ii)). -/
def ghat (a : ℝ) (t : ℂ) : ℂ :=
  ∫ u in (-a)..a, ((Real.cosh (u / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * t * u)

/-- 1bt(ii): `ĝ_a(i/2) = ∫ cosh²(u/2) du = a + sinh a`. -/
theorem ghat_pole (a : ℝ) : ghat a (Complex.I / 2) = ((a + Real.sinh a : ℝ) : ℂ) := by
  unfold ghat
  have h : ∀ u : ℝ, ((Real.cosh (u / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (Complex.I / 2) * u)
      = ((Real.cosh (u / 2) * Real.exp (-(u / 2)) : ℝ) : ℂ) := by
    intro u
    have : Complex.I * (Complex.I / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
      push_cast
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (u / 2 : ℂ) * hI
    rw [this, ← Complex.ofReal_exp]
    push_cast
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have hderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun u => (u - Real.exp (-u)) / 2) (Real.cosh (x / 2) * Real.exp (-(x / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun u => (u - Real.exp (-u)) / 2)
        ((1 - Real.exp (-x) * (-1)) / 2) x := by
      apply HasDerivAt.div_const
      exact (hasDerivAt_id x).sub ((hasDerivAt_neg x).exp)
    convert h1 using 1
    rw [Real.cosh_eq]
    have e1 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(x / 2)) * Real.exp (-(x / 2)) = Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x : ℝ => Real.cosh (x / 2) * Real.exp (-(x / 2))).intervalIntegrable _ _)]
  rw [Real.sinh_eq]
  simp only [neg_neg]
  ring

/-- `∫_{-a}^{a} |sinh(x/2)| dx = 4(cosh(a/2) - 1)` for `a ≥ 0`. -/
theorem integral_abs_sinh_half (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in (-a)..a, |Real.sinh (x / 2)| = 4 * (Real.cosh (a / 2) - 1) := by
  have hc : Continuous (fun x : ℝ => |Real.sinh (x / 2)|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (-a)..0, |Real.sinh (x / 2)| = ∫ x in (-a)..0, -Real.sinh (x / 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    simp only
    rw [abs_of_nonpos]
    have : x / 2 ≤ 0 := by linarith [hx.2]
    have := (Real.sinh_nonneg_iff (x := -(x / 2))).2 (by linarith)
    rw [Real.sinh_neg] at this
    linarith
  have h2 : ∫ x in (0 : ℝ)..a, |Real.sinh (x / 2)| = ∫ x in (0 : ℝ)..a, Real.sinh (x / 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    simp only
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 (by linarith [hx.1]))]
  rw [h1, h2]
  have hd : ∀ x : ℝ, HasDerivAt (fun u => 2 * Real.cosh (u / 2)) (Real.sinh (x / 2)) x := by
    intro x
    have := ((Real.hasDerivAt_cosh (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).const_mul 2
    convert this using 1
    simp
    ring
  have hd' : ∀ x : ℝ, HasDerivAt (fun u => -(2 * Real.cosh (u / 2))) (-Real.sinh (x / 2)) x :=
    fun x => (hd x).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd' x)
      ((by fun_prop : Continuous fun x : ℝ => -Real.sinh (x / 2)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous fun x : ℝ => Real.sinh (x / 2)).intervalIntegrable _ _)]
  simp only [neg_div, Real.cosh_neg, zero_div, Real.cosh_zero]
  ring

/-- `V(a) = 4 cosh(a/2) - 2`, the IBP constant of 1bt(ii). -/
def V (a : ℝ) : ℝ := 4 * Real.cosh (a / 2) - 2

/-- 1bt(ii): one integration by parts gives `|ĝ_a(t)| ≤ V(a) e^{a|Im t|}/|t|`, `V(a) = 4cosh(a/2) - 2`
(the two jumps `2cosh(a/2)` and the variation `2(cosh(a/2) - 1)`). -/
theorem ghat_bound (a : ℝ) (ha : 0 ≤ a) (t : ℂ) (ht : t ≠ 0) :
    ‖ghat a t‖ ≤ V a * Real.exp (a * |t.im|) / ‖t‖ := by
  set E := Real.exp (a * |t.im|) with hE
  have hIt : Complex.I * t ≠ 0 := mul_ne_zero Complex.I_ne_zero ht
  have hnIt : ‖Complex.I * t‖ = ‖t‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht
  set u : ℝ → ℂ := fun x => ((Real.cosh (x / 2) : ℝ) : ℂ) with hu_def
  set u' : ℝ → ℂ := fun x => ((Real.sinh (x / 2) / 2 : ℝ) : ℂ) with hu'_def
  set v : ℝ → ℂ := fun x => Complex.exp (Complex.I * t * x) / (Complex.I * t) with hv_def
  set v' : ℝ → ℂ := fun x => Complex.exp (Complex.I * t * x) with hv'_def
  have hu : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt u (u' x) x := by
    intro x _
    have hd2 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
    have h' := (Real.hasDerivAt_cosh (x / 2)).comp x hd2
    have h1 : HasDerivAt (fun y : ℝ => Real.cosh (y / 2)) (Real.sinh (x / 2) / 2) x :=
      h'.congr_deriv (by ring)
    exact h1.ofReal_comp
  have hv : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Complex.I * t * (y : ℂ)) (Complex.I * t) x := by
      have := (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * t)
      simpa using this
    have h3 := h1.cexp.div_const (Complex.I * t)
    convert h3 using 1
    show Complex.exp (Complex.I * t * x) = _
    field_simp
  have hu'c : Continuous u' := by fun_prop
  have hv'c : Continuous v' := by fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'c.intervalIntegrable _ _) (hv'c.intervalIntegrable _ _)
  have hg : ghat a t = ∫ x in (-a)..a, u x * v' x := rfl
  have hvb : ∀ x : ℝ, |x| ≤ a → ‖v x‖ ≤ E / ‖t‖ := by
    intro x hx
    simp only [hv_def]
    rw [norm_div, hnIt, Complex.norm_exp]
    apply div_le_div_of_nonneg_right _ htpos.le
    apply Real.exp_le_exp.2
    have hre : (Complex.I * t * (x : ℂ)).re = -(x * t.im) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [hre]
    calc -(x * t.im) ≤ |x * t.im| := neg_le_abs _
      _ = |x| * |t.im| := abs_mul _ _
      _ ≤ a * |t.im| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hua : ‖u a‖ = Real.cosh (a / 2) := by
    simp only [hu_def, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (Real.cosh_pos _)
  have hum : ‖u (-a)‖ = Real.cosh (a / 2) := by
    simp only [hu_def, Complex.norm_real, Real.norm_eq_abs, neg_div, Real.cosh_neg]
    exact abs_of_pos (Real.cosh_pos _)
  have hint : ‖∫ x in (-a)..a, u' x * v x‖ ≤ 2 * (Real.cosh (a / 2) - 1) * (E / ‖t‖) := by
    have hbound : ∀ᵐ x ∂volume, x ∈ Set.Ioc (-a) a →
        ‖u' x * v x‖ ≤ |Real.sinh (x / 2)| / 2 * (E / ‖t‖) := by
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [norm_mul]
      have hx' : |x| ≤ a := abs_le.2 ⟨hx.1.le, hx.2⟩
      have h1 : ‖u' x‖ = |Real.sinh (x / 2)| / 2 := by
        simp only [hu'_def, Complex.norm_real, Real.norm_eq_abs, abs_div]
        norm_num
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hvb x hx') (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le (by linarith) hbound
      ((by fun_prop : Continuous fun x : ℝ => |Real.sinh (x / 2)| / 2 * (E / ‖t‖)).intervalIntegrable
        _ _)
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      integral_abs_sinh_half a ha]
    ring
  rw [hg, hibp]
  have hpos := Real.cosh_pos (a / 2)
  have h1 := hvb a (by rw [abs_of_nonneg ha])
  have h2 := hvb (-a) (by rw [abs_neg, abs_of_nonneg ha])
  calc ‖u a * v a - u (-a) * v (-a) - ∫ x in (-a)..a, u' x * v x‖
      ≤ ‖u a * v a‖ + ‖u (-a) * v (-a)‖ + ‖∫ x in (-a)..a, u' x * v x‖ := by
        have := norm_sub_le (u a * v a - u (-a) * v (-a)) (∫ x in (-a)..a, u' x * v x)
        have := norm_sub_le (u a * v a) (u (-a) * v (-a))
        linarith
    _ ≤ Real.cosh (a / 2) * (E / ‖t‖) + Real.cosh (a / 2) * (E / ‖t‖)
          + 2 * (Real.cosh (a / 2) - 1) * (E / ‖t‖) := by
        rw [norm_mul, norm_mul, hua, hum]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hpos.le)
          (mul_le_mul_of_nonneg_left h2 hpos.le)) hint
    _ = V a * E / ‖t‖ := by rw [V]; ring

/-- The zero-sum lemma of 1bt(ii): for a zero `ρ = β + iγ` in the open strip,
`Re 1/(ρ(1-ρ)) ≥ 1/(γ² + 5/4)`. -/
theorem re_inv_zero_term_ge (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 / (ρ.im ^ 2 + 5 / 4) ≤ (1 / (ρ * (1 - ρ))).re := by
  have hre : (ρ * (1 - ρ)).re = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
    simp [Complex.mul_re]; ring
  have him : (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
    simp [Complex.mul_im]; ring
  set β := ρ.re
  set γ := ρ.im
  have hx0 : 0 < β * (1 - β) := mul_pos h0 (by linarith)
  have hx1 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hX : 0 < β * (1 - β) + γ ^ 2 := by nlinarith [sq_nonneg γ]
  rw [one_div (ρ * (1 - ρ)), Complex.inv_re, Complex.normSq_apply, hre, him]
  have hden : 0 < (β * (1 - β) + γ ^ 2) * (β * (1 - β) + γ ^ 2)
      + γ * (1 - 2 * β) * (γ * (1 - 2 * β)) :=
    add_pos_of_pos_of_nonneg (mul_pos hX hX) (mul_self_nonneg _)
  rw [div_le_div_iff₀ (by positivity) hden]
  -- (x+γ²)(γ²+5/4) - (x+γ²)² - γ²(1-2β)² = x(5/4-x) + γ²(1/4+3x),  x = β(1-β)
  have key : (β * (1 - β) + γ ^ 2) * (γ ^ 2 + 5 / 4)
      - ((β * (1 - β) + γ ^ 2) * (β * (1 - β) + γ ^ 2)
         + γ * (1 - 2 * β) * (γ * (1 - 2 * β)))
      = β * (1 - β) * (5 / 4 - β * (1 - β)) + γ ^ 2 * (1 / 4 + 3 * (β * (1 - β))) := by ring
  have hA : 0 ≤ β * (1 - β) * (5 / 4 - β * (1 - β)) := by
    apply mul_nonneg hx0.le; linarith
  have hB : 0 ≤ γ ^ 2 * (1 / 4 + 3 * (β * (1 - β))) := by
    apply mul_nonneg (sq_nonneg γ); linarith
  nlinarith

/-- The Hadamard constant `K = 2 + γ_E - log(4π)` (true value 0.046191...) is below 0.0572.
Uses only Mathlib's `γ_E < H_64 - log 64`, `log 2 > 0.6931471803`, `e < 2.7182818286`,
`π > 3.141592` and a four-term Taylor bound for `exp 0.143`. -/
theorem hadamard_const_lt : 2 + eulerMascheroniConstant - Real.log (4 * π) < 0.0572 := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hseq : eulerMascheroniSeq' 64 = (harmonic 64 : ℝ) - Real.log 64 := by
    simp [eulerMascheroniSeq']
  have hH : (harmonic 64 : ℝ) < 47439 / 10000 := by
    have : harmonic 64 < (47439 / 10000 : ℚ) := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have h' : ((harmonic 64 : ℚ) : ℝ) < ((47439 / 10000 : ℚ) : ℝ) := Rat.cast_lt.mpr this
    simpa using h'
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have hlog4pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hlpi : 1.143 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have h1 : Real.exp 1.143 = Real.exp 1 * Real.exp 0.143 := by
      rw [← Real.exp_add]; norm_num
    have hb := Real.exp_bound (x := 0.143) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 4) (by norm_num)
    have hb' := (abs_sub_le_iff.1 hb).1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb'
    norm_num at hb'
    have he := Real.exp_one_lt_d9
    have hpi := Real.pi_gt_d6
    have hexp : Real.exp 0.143 < 1.1538 := by linarith
    rw [h1]
    calc Real.exp 1 * Real.exp 0.143 < 2.7182818286 * 1.1538 :=
          mul_lt_mul'' he hexp (Real.exp_pos 1).le (Real.exp_pos _).le
      _ < 3.141592 := by norm_num
      _ < π := hpi
  rw [hlog4pi]
  rw [hseq, hlog64] at hγ
  linarith


/-- The analytic core replacing 1bt's interval evaluation on `[0.2, 1]` and its `a ≥ 1` ratio:
for every `a ≥ 1/5` and every `K' ≤ 289/5000 (= 0.0578)`, `V(a)² eᵃ K' < 2(a + sinh a)²`. -/
theorem final_ineq (a : ℝ) (ha : 1 / 5 ≤ a) (K' : ℝ) (hK' : K' ≤ 289 / 5000) :
    V a ^ 2 * Real.exp a * K' < 2 * (a + Real.sinh a) ^ 2 := by
  set E := Real.exp (a / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hexpa : Real.exp a = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add]; ring_nf
  have hcosh : Real.cosh (a / 2) = (E + E⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have hsinh : Real.sinh a = (E ^ 2 - (E ^ 2)⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, hexpa]
  -- A = exp a, B = exp(-a) = A⁻¹
  have hA : 1 + a + a ^ 2 / 2 ≤ E ^ 2 := by
    rw [← hexpa]; exact Real.quadratic_le_exp_of_nonneg (by linarith)
  have hE1 : 1 + a / 2 ≤ E := by
    have h := Real.add_one_le_exp (a / 2); rw [← hE] at h; linarith
  have hB : (E ^ 2)⁻¹ ≤ (1 + a)⁻¹ := by
    have h1 : a + 1 ≤ E ^ 2 := by rw [← hexpa]; exact Real.add_one_le_exp a
    exact inv_anti₀ (by linarith) (by linarith)
  have hBpos : 0 < (E ^ 2)⁻¹ := by positivity
  -- 1/(1+a) < 0.32 + 2.66 a + 0.16 a²  for a ≥ 1/5
  have hpoly : (1 + a)⁻¹ < 8 / 25 + 133 / 50 * a + 4 / 25 * a ^ 2 := by
    rw [inv_lt_iff_one_lt_mul₀ (by linarith)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - 1 / 5) (by linarith : (0:ℝ) ≤ a),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a) (by linarith : (0:ℝ) ≤ a))
        (by linarith : (0:ℝ) ≤ a)]
  -- S := a + sinh a > c₀ P with c₀ = 17/50, P = E² - E + 1
  set P := E ^ 2 - E + 1 with hP
  have hPpos : 0 < P := by nlinarith [sq_nonneg (E - 1 / 2)]
  have hS : 17 / 50 * P < a + Real.sinh a := by
    rw [hsinh, hP]
    nlinarith
  have hSpos : 0 < a + Real.sinh a := by nlinarith
  -- V(a)² eᵃ = 4 P²
  have hVE : V a ^ 2 * Real.exp a = 4 * P ^ 2 := by
    rw [V, hcosh, hexpa, hP]
    field_simp
    ring
  have hVEnn : 0 ≤ V a ^ 2 * Real.exp a := by positivity
  calc V a ^ 2 * Real.exp a * K' ≤ V a ^ 2 * Real.exp a * (289 / 5000) :=
        mul_le_mul_of_nonneg_left hK' hVEnn
    _ = 2 * (17 / 50 * P) ^ 2 := by rw [hVE]; ring
    _ < 2 * (a + Real.sinh a) ^ 2 := by
        have h0 : 0 < 17 / 50 * P := by positivity
        have := pow_lt_pow_left₀ hS h0.le (by norm_num : (2:ℕ) ≠ 0)
        linarith


/-! ## The strip hypothesis, discharged from Mathlib -/
/-- A nontrivial zero of `ζ`, exactly as in Mathlib's `RiemannHypothesis`: `ζ s = 0` and `s` is not
a trivial zero `-2(n+1)`. (`s ≠ 1` is automatic, since Mathlib's `ζ 1 ≠ 0`.) -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬∃ n : ℕ, s = -2 * (n + 1)

/-- Nontrivial zeros have `Re s < 1` (Mathlib: `ζ ≠ 0` on `Re s ≥ 1`). -/
theorem IsNontrivialZero.re_lt_one {s : ℂ} (h : IsNontrivialZero s) : s.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h.1

/-- Nontrivial zeros have `Re s > 0`: for `Re s ≤ 0` the functional equation
`ζ(s) = 2(2π)^{-(1-s)} Γ(1-s) cos(π(1-s)/2) ζ(1-s)` has every factor but the cosine nonzero, and the
cosine vanishes only at `s = -2k`, which is `ζ(0) = -1/2 ≠ 0` for `k = 0` and a trivial zero for
`k ≥ 1`. -/
theorem IsNontrivialZero.re_pos {s : ℂ} (h : IsNontrivialZero s) : 0 < s.re := by
  by_contra hc'
  have hc : s.re ≤ 0 := not_lt.1 hc'
  obtain ⟨hz, hnt⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  set w := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    rw [hw, Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have h1 := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at h1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h1
    apply hs0
    have : s = 1 - w := by rw [hw]; ring
    rw [this, h1]; ring
  have hfe := riemannZeta_one_sub hwn hw1
  have h1w : 1 - w = s := by rw [hw]; ring
  rw [h1w, hz] at hfe
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    have h0 := hfe.symm
    rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h0 | h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · exact absurd h0 two_ne_zero
          · exact absurd h0 hpow
        · exact absurd h0 hΓ
      · exact h0
    · exact absurd h0 hζw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hwk : w = 2 * k + 1 := by
    have h2 : (Real.pi : ℂ) * w = (2 * k + 1) * Real.pi := by
      linear_combination 2 * hk
    have h3 : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * k + 1) := by rw [h2]; ring
    exact mul_left_cancel₀ hpi h3
  have hsk : s = -2 * (k : ℂ) := by
    have : s = 1 - w := by rw [hw]; ring
    rw [this, hwk]; ring
  -- `Re s = -2k ≤ 0` forces `k ≥ 0`; `s ≠ 0` forces `k ≠ 0`
  have hkre : s.re = -2 * (k : ℝ) := by
    rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    have : -2 * (k : ℝ) ≤ 0 := by rw [← hkre]; exact hc
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hkne : k ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hsk]; simp
  have hk1 : 0 ≤ k - 1 := by omega
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk1
  apply hnt
  refine ⟨m, ?_⟩
  rw [hsk]
  have : (k : ℂ) = (m : ℂ) + 1 := by
    have : k = (m : ℤ) + 1 := by omega
    rw [this]; push_cast; ring
  rw [this]

/-- **The strip hypothesis, discharged**: every nontrivial zero of Mathlib's `riemannZeta` lies in
the open critical strip. -/
theorem IsNontrivialZero.mem_strip {s : ℂ} (h : IsNontrivialZero s) : 0 < s.re ∧ s.re < 1 :=
  ⟨h.re_pos, h.re_lt_one⟩

/-! ## The canonical zero family: the nontrivial zeros of `ζ` with multiplicity -/

/-- The nontrivial zeros of Mathlib's `riemannZeta`. -/
def NontrivialZero : Type := {s : ℂ // IsNontrivialZero s}

/-- The multiplicity of a nontrivial zero: the analytic order of `ζ` there. -/
def zeroMult (z : NontrivialZero) : ℕ := (analyticOrderAt riemannZeta z.1).toNat

/-- Each nontrivial zero has multiplicity at least one (and finite order), so the family below
lists every nontrivial zero, repeated by multiplicity. -/
theorem zeroMult_pos (z : NontrivialZero) : 0 < zeroMult z := by
  have hz := z.2.1
  have h1 : z.1 ≠ 1 := by
    intro h; rw [h] at hz; exact riemannZeta_one_ne_zero hz
  have han : AnalyticAt ℂ riemannZeta z.1 := analyticOn_riemannZeta z.1 h1
  have hne0 : analyticOrderAt riemannZeta z.1 ≠ 0 := analyticOrderAt_ne_zero.2 ⟨han, hz⟩
  have hne_top : analyticOrderAt riemannZeta z.1 ≠ ⊤ := by
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
    have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [ne_eq, analyticOrderAt_eq_zero.2 (Or.inr (riemannZeta_ne_zero_of_one_le_re
        (by norm_num)))]
      exact ENat.zero_ne_top
    exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected h2 h1 hord2
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne_top
  unfold zeroMult
  rw [← hm, ENat.toNat_natCast]
  rw [← hm] at hne0
  exact Nat.pos_of_ne_zero (by exact_mod_cast hne0)

/-- The nontrivial zeros of `ζ` counted with multiplicity, as an indexed family. -/
def zetaZeroFamily : (Σ z : NontrivialZero, Fin (zeroMult z)) → ℂ := fun p => p.1.1

/-! ## Theorem 1bt(i): the pole-free form is negative on the witness, for every `a ≥ 0.2`

Named classical inputs (hypotheses, not proved here):
* `h_strip`    — every nontrivial zero `ρ` lies in the open critical strip `0 < Re ρ < 1`;
* `h_height`   — every zero has `|Im ρ| ≥ 14` (the first zero is at 14.1347...);
* `h_hadamard` — Hadamard's identity `Σ_ρ 1/(ρ(1-ρ)) = 2 + γ_E - log 4π`, summed over the
                 zeros with multiplicity (absolutely convergent, hence an unconditional `HasSum`);
* `h_explicit` — Weil's explicit formula for the autocorrelation of the even witness `g_a`:
                 the value `Q` of Weil's form is the zero sum `Σ_ρ ĝ_a(t_ρ)²`, `t_ρ = (ρ - 1/2)/i`.
The zeros are an arbitrary family `ρ : ι → ℂ` (multiplicity = repetition). -/
theorem pole_free_form_negative {ι : Type*} (ρ : ι → ℂ)
    (h_strip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (h_height : ∀ i, 14 ≤ |(ρ i).im|)
    (h_hadamard : HasSum (fun i => 1 / (ρ i * (1 - ρ i)))
      ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ))
    (a : ℝ) (ha : 1 / 5 ≤ a) (Q : ℂ)
    (h_explicit : HasSum (fun i => ghat a ((ρ i - 1 / 2) / Complex.I) ^ 2) Q) :
    ‖Q‖ < 2 * (a + Real.sinh a) ^ 2 ∧ (Q - 2 * ghat a (Complex.I / 2) ^ 2).re < 0 := by
  set K := 2 + eulerMascheroniConstant - Real.log (4 * π) with hK
  have hKlt : K < 0.0572 := hadamard_const_lt
  have ha0 : 0 ≤ a := by linarith
  set C := V a ^ 2 * Real.exp a * (1 + 5 / 784) with hC
  have hCnn : 0 ≤ C := by positivity
  -- termwise: ‖ĝ(t_ρ)²‖ ≤ C · Re 1/(ρ(1-ρ))
  have hterm : ∀ i, ‖ghat a ((ρ i - 1 / 2) / Complex.I) ^ 2‖ ≤ C * (1 / (ρ i * (1 - ρ i))).re := by
    intro i
    obtain ⟨h0, h1⟩ := h_strip i
    have hγ := h_height i
    set g := (ρ i).im with hg
    set t := (ρ i - 1 / 2) / Complex.I with ht_def
    have htre : t.re = g := by
      simp [ht_def, Complex.div_I, hg]
    have htim : t.im = 1 / 2 - (ρ i).re := by
      simp [ht_def, Complex.div_I]
    have hg2 : 196 ≤ g ^ 2 := by
      have h := mul_le_mul hγ hγ (by norm_num) (abs_nonneg g)
      rw [abs_mul_abs_self] at h
      nlinarith
    have hnt : g ^ 2 ≤ ‖t‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, htre]
      nlinarith [mul_self_nonneg t.im]
    have htpos : 0 < ‖t‖ := by
      by_contra hcon
      have h0' : ‖t‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
      rw [h0'] at hnt
      nlinarith
    have ht0 : t ≠ 0 := norm_pos_iff.1 htpos
    have hb := ghat_bound a ha0 t ht0
    have him : |t.im| ≤ 1 / 2 := by
      rw [htim, abs_le]; constructor <;> linarith
    have hexp : Real.exp (a * |t.im|) ^ 2 ≤ Real.exp a := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left him ha0]
    have hVnn : 0 ≤ V a ^ 2 := sq_nonneg _
    have hg2pos : 0 < g ^ 2 := by linarith
    have hlem := re_inv_zero_term_ge (ρ i) h0 h1
    have hinv : 1 / g ^ 2 ≤ (1 + 5 / 784) * (1 / (ρ i * (1 - ρ i))).re := by
      have h2 : 1 / g ^ 2 ≤ (1 + 5 / 784) * (1 / (g ^ 2 + 5 / 4)) := by
        rw [show (1 + 5 / 784 : ℝ) * (1 / (g ^ 2 + 5 / 4)) = (1 + 5 / 784) / (g ^ 2 + 5 / 4) by
          ring]
        rw [div_le_div_iff₀ hg2pos (by linarith)]
        nlinarith
      calc 1 / g ^ 2 ≤ (1 + 5 / 784) * (1 / (g ^ 2 + 5 / 4)) := h2
        _ ≤ (1 + 5 / 784) * (1 / (ρ i * (1 - ρ i))).re :=
          mul_le_mul_of_nonneg_left hlem (by norm_num)
    calc ‖ghat a t ^ 2‖ = ‖ghat a t‖ ^ 2 := norm_pow _ _
      _ ≤ (V a * Real.exp (a * |t.im|) / ‖t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = V a ^ 2 * Real.exp (a * |t.im|) ^ 2 / ‖t‖ ^ 2 := by ring
      _ ≤ V a ^ 2 * Real.exp a / g ^ 2 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hexp hVnn) hg2pos hnt
      _ = V a ^ 2 * Real.exp a * (1 / g ^ 2) := by ring
      _ ≤ V a ^ 2 * Real.exp a * ((1 + 5 / 784) * (1 / (ρ i * (1 - ρ i))).re) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = C * (1 / (ρ i * (1 - ρ i))).re := by rw [hC]; ring
  have hsumC : HasSum (fun i => C * (1 / (ρ i * (1 - ρ i))).re) (C * K) := by
    have := (Complex.hasSum_re h_hadamard).mul_left C
    simpa using this
  have hQle : ‖Q‖ ≤ C * K := h_explicit.norm_le_of_bounded hsumC hterm
  have hfin : C * K < 2 * (a + Real.sinh a) ^ 2 := by
    have h := final_ineq a ha ((1 + 5 / 784) * K) (by linarith)
    calc C * K = V a ^ 2 * Real.exp a * ((1 + 5 / 784) * K) := by rw [hC]; ring
      _ < _ := h
  have hQ : ‖Q‖ < 2 * (a + Real.sinh a) ^ 2 := lt_of_le_of_lt hQle hfin
  refine ⟨hQ, ?_⟩
  rw [ghat_pole]
  have hre : (Q - 2 * ((a + Real.sinh a : ℝ) : ℂ) ^ 2).re = Q.re - 2 * (a + Real.sinh a) ^ 2 := by
    rw [Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre]
  have := Complex.re_le_norm Q
  linarith

/-- **Theorem 1bt(i) over the zeros of Mathlib's `ζ`.** The strip hypothesis is now a theorem
(`IsNontrivialZero.mem_strip`); the family is the nontrivial zeros of `riemannZeta` counted with
multiplicity. Remaining named classical inputs: the first zero's height, Hadamard's identity and
Weil's explicit formula — each now a statement about `ζ` itself. -/
theorem pole_free_form_negative_zeta
    (h_height : ∀ p, 14 ≤ |(zetaZeroFamily p).im|)
    (h_hadamard : HasSum (fun p => 1 / (zetaZeroFamily p * (1 - zetaZeroFamily p)))
      ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ))
    (a : ℝ) (ha : 1 / 5 ≤ a) (Q : ℂ)
    (h_explicit : HasSum (fun p => ghat a ((zetaZeroFamily p - 1 / 2) / Complex.I) ^ 2) Q) :
    ‖Q‖ < 2 * (a + Real.sinh a) ^ 2 ∧ (Q - 2 * ghat a (Complex.I / 2) ^ 2).re < 0 :=
  pole_free_form_negative zetaZeroFamily (fun p => p.1.2.mem_strip) h_height h_hadamard a ha Q
    h_explicit

end Pilot1bt

#print axioms Pilot1bt.ghat_pole
#print axioms Pilot1bt.integral_abs_sinh_half
#print axioms Pilot1bt.ghat_bound
#print axioms Pilot1bt.re_inv_zero_term_ge
#print axioms Pilot1bt.hadamard_const_lt
#print axioms Pilot1bt.final_ineq
#print axioms Pilot1bt.pole_free_form_negative
#print axioms Pilot1bt.IsNontrivialZero.mem_strip
#print axioms Pilot1bt.zeroMult_pos
#print axioms Pilot1bt.pole_free_form_negative_zeta
