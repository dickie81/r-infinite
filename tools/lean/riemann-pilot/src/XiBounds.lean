import Mathlib
import HadamardApply

/-! # `Ξ(0) ≠ 0` and the order of `Ξ`, from Riemann's theta kernel

Mathlib's `completedRiemannZeta₀ s` is `mellin f_modif (s/2) / 2` for the FE-pair built on the theta
kernel `θ(x) = Σ_{n∈ℤ} e^{−πn²x}`. Here:
* `evenKernel_sub_one_le`: `0 ≤ θ(x) − 1 ≤ 3e^{−πx}` for `x ≥ 1` (from the ℤ-sum);
* `f_modif` is `θ(x) − 1` on `(1, ∞)` and `x^{−1/2}(θ(1/x) − 1)` on `(0, 1)` (functional equation);
* `norm_completedZeta₀_le`: `‖Λ₀(s)‖ ≤ (3m₁!/π^{m₁} + 3m₂!/(π − 1))/2` whenever
  `m₁ ≥ 3/2 − Re s/2`, `m₂ ≥ Re s/2 − 1` (`e^{−π/x} ≤ m!(x/π)^m`, `x^m ≤ m!eˣ`);
* `Xi_zero_ne_zero`: `|Λ₀(½)| < 4`, so `ξ(½) = (1 − Λ₀(½)/4)/2 ≠ 0`;
* `xiGrowth`: `‖Ξ(t)‖ ≤ C exp(A‖t‖^{3/2})`. -/

open Real Filter Topology Complex MeasureTheory Set HurwitzZeta

noncomputable section

namespace Pilot1ca

/-! ## The theta kernel -/

theorem evenKernel_sub_one_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else 2 * Real.exp (-π * (n : ℝ) ^ 2 * t))
      (evenKernel 0 t - 1) := by
  have h := hasSum_int_evenKernel₀ 0 ht
  simp only [add_zero, Int.cast_eq_zero, QuotientAddGroup.mk_zero, ite_true] at h
  have h2 := h.nat_add_neg
  simp only [ite_true, add_zero] at h2
  have e : (fun n : ℕ => (if (n : ℤ) = 0 then (0 : ℝ) else Real.exp (-π * ((n : ℤ) : ℝ) ^ 2 * t))
      + (if -(n : ℤ) = 0 then 0 else Real.exp (-π * ((-(n : ℤ) : ℤ) : ℝ) ^ 2 * t)))
      = fun n : ℕ => if n = 0 then (0 : ℝ) else 2 * Real.exp (-π * (n : ℝ) ^ 2 * t) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
      simp [hn]
      ring
  rw [e] at h2
  simpa using h2

/-- **`0 ≤ θ(t) − 1 ≤ 2q/(1 − q)`, `q = e^{−πt}`.** -/
theorem evenKernel_sub_one_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ evenKernel 0 t - 1 ∧
      evenKernel 0 t - 1 ≤ 2 * Real.exp (-π * t) / (1 - Real.exp (-π * t)) := by
  have hs := evenKernel_sub_one_hasSum ht
  have hq0 : 0 ≤ Real.exp (-π * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-π * t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  refine ⟨hs.nonneg (fun n => by split_ifs <;> positivity), ?_⟩
  -- compare with `2q^n − 2[n = 0]`
  have hg : HasSum (fun n : ℕ => 2 * Real.exp (-π * t) ^ n - if n = 0 then 2 else 0)
      (2 * (1 - Real.exp (-π * t))⁻¹ - 2) := by
    have h1 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left 2
    have h2 : HasSum (fun n : ℕ => if n = 0 then (2 : ℝ) else 0) 2 := hasSum_ite_eq 0 2
    exact h1.sub h2
  have hle := hasSum_le (fun n => ?_) hs hg
  · have hq1' : 1 - Real.exp (-π * t) ≠ 0 := by linarith
    have : 2 * (1 - Real.exp (-π * t))⁻¹ - 2
        = 2 * Real.exp (-π * t) / (1 - Real.exp (-π * t)) := by
      generalize Real.exp (-π * t) = x at hq1' ⊢
      field_simp; ring
    linarith
  · by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false, sub_zero]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have hqn : Real.exp (-π * t) ^ n = Real.exp (n * (-π * t)) := (Real.exp_nat_mul _ n).symm
      have hle' : -π * (n : ℝ) ^ 2 * t ≤ n * (-π * t) := by
        have hp : 0 < π * t := by positivity
        nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.2 hn1)) (by linarith : (0 : ℝ) ≤ n)]
      rw [hqn]
      linarith [Real.exp_le_exp.2 hle']

theorem exp_neg_pi_le : Real.exp (-π) ≤ 1 / 10 := by
  have h3 : (10 : ℝ) ≤ Real.exp 3 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this; linarith
  have : Real.exp 3 ≤ Real.exp π := Real.exp_le_exp.2 (by linarith [Real.pi_gt_three])
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- **`0 ≤ θ(t) − 1 ≤ 3e^{−πt}` for `t ≥ 1`.** -/
theorem evenKernel_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ evenKernel 0 t - 1 ∧ evenKernel 0 t - 1 ≤ 3 * Real.exp (-π * t) := by
  obtain ⟨h0, h1⟩ := evenKernel_sub_one_bounds (by linarith : (0 : ℝ) < t)
  refine ⟨h0, h1.trans ?_⟩
  have hq : Real.exp (-π * t) ≤ 1 / 10 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_pi_le
    nlinarith [Real.pi_pos]
  have hq0 := Real.exp_pos (-π * t)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The modified kernel -/

theorem fmodif_gt_one {x : ℝ} (hx : 1 < x) :
    ‖(hurwitzEvenFEPair 0).f_modif x‖ ≤ 3 * Real.exp (-π * x) := by
  have hx0 : ¬ x ∈ Ioo (0 : ℝ) 1 := fun h => by linarith [h.2]
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.2 hx),
    indicator_of_notMem hx0, add_zero, hurwitzEvenFEPair, Function.comp_apply, ite_true]
  rw [show ((evenKernel 0 x : ℝ) : ℂ) - 1 = ((evenKernel 0 x - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨h0, h1⟩ := evenKernel_sub_one_le hx.le
  rw [abs_of_nonneg h0]; exact h1

theorem fmodif_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖(hurwitzEvenFEPair 0).f_modif x‖ ≤ 3 * x ^ (-(1 / 2 : ℝ)) * Real.exp (-π / x) := by
  have hxi : ¬ x ∈ Ioi (1 : ℝ) := fun h => by linarith [mem_Ioi.1 h]
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem hxi,
    indicator_of_mem (mem_Ioo.2 ⟨hx0, hx1⟩), zero_add, hurwitzEvenFEPair, Function.comp_apply,
    one_mul, smul_eq_mul, mul_one]
  have hfe := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at hfe
  have h1x : 1 < 1 / x := by rw [lt_div_iff₀ hx0]; linarith
  obtain ⟨h0, h1⟩ := evenKernel_sub_one_le h1x.le
  have hxr : x ^ (-(1 / 2 : ℝ)) = 1 / x ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hx0.le, inv_eq_one_div]
  have hpos : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hreal : evenKernel 0 x - x ^ (-(1 / 2 : ℝ))
      = x ^ (-(1 / 2 : ℝ)) * (evenKernel 0 (1 / x) - 1) := by
    rw [hfe, hxr]; ring
  rw [show ((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      = ((x ^ (-(1 / 2 : ℝ)) * (evenKernel 0 (1 / x) - 1) : ℝ) : ℂ) by
      rw [← hreal]; push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : -π * (1 / x) = -π / x := by ring
  rw [e] at h1
  have : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by positivity
  nlinarith

/-! ## The Mellin bound -/

/-- `e^{−π/x} ≤ m!·(x/π)^m`. -/
theorem exp_neg_pi_div_le {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.exp (-π / x) ≤ m.factorial * (x / π) ^ m := by
  have h := Real.pow_div_factorial_le_exp (x := π / x) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  rw [show -π / x = -(π / x) by ring, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  calc (1 : ℝ) = (m.factorial * (x / π) ^ m) * (π / x) ^ m / m.factorial := by
        rw [mul_assoc, ← mul_pow, show x / π * (π / x) = 1 by field_simp, one_pow, mul_one]
        field_simp
    _ ≤ (m.factorial * (x / π) ^ m) * Real.exp (π / x) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hf]; linarith

/-- **`‖Λ₀(s)‖ ≤ (3m₁!/π^{m₁} + 3m₂!/(π − 1))/2`** for `m₁ ≥ 3/2 − Re s/2` and `m₂ ≥ Re s/2 − 1`. -/
theorem norm_completedZeta₀_le (s : ℂ) (m₁ m₂ : ℕ) (h₁ : 3 / 2 - (s / 2).re ≤ m₁)
    (h₂ : (s / 2).re - 1 ≤ m₂) :
    ‖completedRiemannZeta₀ s‖
      ≤ (3 * m₁.factorial / π ^ m₁ + 3 * m₂.factorial / (π - 1)) / 2 := by
  set w := s / 2
  set σ := w.re
  set K₁ : ℝ := 3 * m₁.factorial / π ^ m₁
  set K₂ : ℝ := 3 * m₂.factorial
  have hπ1 : 0 < π - 1 := by linarith [Real.pi_gt_three]
  set g : ℝ → ℝ := fun t => K₁ * (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t + K₂ * Real.exp (-(π - 1) * t)
  -- `g` is integrable with integral `K₁ + K₂/(π − 1)`
  have hind_int : Integrable ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (by simp [Real.volume_Ioc]))
  have hgi1 : IntegrableOn (fun t => K₁ * (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t) (Ioi 0) :=
    hind_int.integrableOn.const_mul K₁
  have hgi2 : IntegrableOn (fun t => K₂ * Real.exp (-(π - 1) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hπ1).const_mul K₂
  have hgi : IntegrableOn g (Ioi 0) := hgi1.add hgi2
  have hgv : ∫ t in Ioi (0 : ℝ), g t = K₁ + K₂ / (π - 1) := by
    rw [MeasureTheory.integral_add hgi1 hgi2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    have hind : ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t = 1 := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_self_of_subset_right Ioc_subset_Ioi_self]
      simp
    rw [hind]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  -- pointwise domination
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤ g t := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
    have hK₁ : 0 ≤ K₁ := by positivity
    have hK₂ : 0 ≤ K₂ := by positivity
    rcases lt_trichotomy t 1 with h | h | h
    · -- `(0, 1)`
      have hb := fmodif_lt_one ht0 h
      have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t = (1 : ℝ) := by
        rw [indicator_of_mem (mem_Ioc.2 ⟨ht0, h.le⟩)]; rfl
      simp only [g, hind, mul_one]
      have he := exp_neg_pi_div_le ht0 m₁
      have hexp : 0 ≤ σ - 1 - 1 / 2 + m₁ := by linarith
      calc t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ (σ - 1) * (3 * t ^ (-(1 / 2 : ℝ)) * (m₁.factorial * (t / π) ^ m₁)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hb.trans (mul_le_mul_of_nonneg_left he (by positivity))
        _ = K₁ * t ^ (σ - 1 - 1 / 2 + m₁) := by
            rw [show σ - 1 - 1 / 2 + (m₁ : ℝ) = (σ - 1) + (-(1 / 2 : ℝ)) + (m₁ : ℝ) by ring,
              Real.rpow_add ht0, Real.rpow_add ht0, Real.rpow_natCast, div_pow]
            simp only [K₁]
            field_simp
        _ ≤ K₁ * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one ht0.le h.le hexp) hK₁
        _ ≤ K₁ + K₂ * Real.exp (-(π - 1) * t) := by
            have := Real.exp_pos (-(π - 1) * t); nlinarith
    · -- `t = 1`: `f_modif 1 = 0`
      subst h
      have : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
        simp [WeakFEPair.f_modif]
      rw [this, norm_zero, mul_zero]
      exact add_nonneg (mul_nonneg hK₁ (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (by positivity)
    · -- `(1, ∞)`
      have hb := fmodif_gt_one h
      have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t = (0 : ℝ) :=
        indicator_of_notMem (fun hm => by linarith [(mem_Ioc.1 hm).2]) _
      simp only [g, hind, mul_zero, zero_add]
      have hpow : t ^ (σ - 1) ≤ t ^ (m₂ : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le h₂
      have hfac := Real.pow_div_factorial_le_exp (x := t) (by linarith) m₂
      have hf : (0 : ℝ) < m₂.factorial := by exact_mod_cast Nat.factorial_pos m₂
      rw [div_le_iff₀ hf] at hfac
      rw [Real.rpow_natCast] at hpow
      calc t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ m₂ * (3 * Real.exp (-π * t)) :=
            mul_le_mul hpow hb (norm_nonneg _) (by positivity)
        _ ≤ (Real.exp t * m₂.factorial) * (3 * Real.exp (-π * t)) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
        _ = K₂ * Real.exp (-(π - 1) * t) := by
            simp only [K₂]
            rw [show -(π - 1) * t = t + -π * t by ring, Real.exp_add]
            ring
  -- assemble
  have hΛ : completedRiemannZeta₀ s = mellin (hurwitzEvenFEPair 0).f_modif w / 2 := rfl
  rw [hΛ, norm_div, Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hmel := MeasureTheory.norm_integral_le_of_norm_le hgi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht)
  unfold mellin
  refine hmel.trans (le_of_eq ?_)
  rw [hgv]

/-! ## `Ξ(0) ≠ 0` -/

/-- **`Ξ(0) ≠ 0`**: `‖Λ₀(½)‖ ≤ (6/π² + 3/(π − 1))/2 < 4`, while `ξ(½) = (1 − Λ₀(½)/4)/2`. -/
theorem Xi_zero_ne_zero : Xi 0 ≠ 0 := by
  have hb := norm_completedZeta₀_le (1 / 2) 2 0 (by norm_num) (by norm_num)
  have hπ3 := Real.pi_gt_three
  have hb' : ‖completedRiemannZeta₀ (1 / 2)‖ < 4 := by
    refine lt_of_le_of_lt hb ?_
    simp only [Nat.factorial, Nat.succ_eq_add_one, zero_add, Nat.mul_one,
      Nat.cast_one]
    have h1 : 3 * 2 / π ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h2 : 3 * 1 / (π - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    norm_num at h1 h2 ⊢
    linarith
  intro h
  unfold Xi xi at h
  rw [mul_zero, add_zero] at h
  have : completedRiemannZeta₀ (1 / 2) = 4 := by
    have h' : (1 / 2 : ℂ) * (1 / 2 - 1) * completedRiemannZeta₀ (1 / 2) + 1 = 0 := by
      have := congrArg (· * 2) h; simpa using this
    linear_combination (-4 : ℂ) * h'
  rw [this] at hb'
  norm_num at hb'

/-! ## The order of `Ξ` -/

theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
  rw [Real.log_sqrt hy.le] at h
  linarith [Real.sqrt_nonneg y]

/-- `(x + 3)√(x + 3) ≤ 3x√x + 24` for `x ≥ 0`. -/
theorem shift_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x + 3) * Real.sqrt (x + 3) ≤ 3 * (x * Real.sqrt x) + 24 := by
  have hu := Real.sq_sqrt hx
  have hv := Real.sq_sqrt (by linarith : 0 ≤ x + 3)
  have hu0 := Real.sqrt_nonneg x
  have hv0 := Real.sqrt_nonneg (x + 3)
  rcases le_total 3 x with h | h
  · -- `√(x+3) ≤ (17/12)√x` since `(x + 3) ≤ (289/144) x`
    have hvu : Real.sqrt (x + 3) ≤ 17 / 12 * Real.sqrt x := by
      rw [show 17 / 12 * Real.sqrt x = Real.sqrt ((17 / 12) ^ 2 * x) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have : (x + 3) * Real.sqrt (x + 3) ≤ 2 * x * (17 / 12 * Real.sqrt x) :=
      mul_le_mul (by linarith) hvu hv0 (by linarith)
    nlinarith
  · have hv6 : Real.sqrt (x + 3) ≤ 3 := by
      have h9 : Real.sqrt 9 = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      calc Real.sqrt (x + 3) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by linarith)
        _ = 3 := h9
    have : (x + 3) * Real.sqrt (x + 3) ≤ 6 * 3 := mul_le_mul (by linarith) hv6 hv0 (by norm_num)
    nlinarith [mul_nonneg hx hu0]

/-- **The order of `Ξ`, proved**: `‖Ξ(t)‖ ≤ 3e^{144} exp(18‖t‖^{3/2})`. -/
theorem xiGrowth : XiGrowth := by
  refine ⟨3 * Real.exp 144, 18, ?_, by norm_num, fun t => ?_⟩
  · have := Real.add_one_le_exp (144 : ℝ); linarith
  set x := ‖t‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg t
  set N : ℕ := ⌈x⌉₊ + 2 with hN
  have hNx : (N : ℝ) ≤ x + 3 := by
    have := Nat.ceil_lt_add_one hx0
    simp only [hN]; push_cast; linarith
  have hxN : x + 2 ≤ (N : ℝ) := by
    have := Nat.le_ceil x
    simp only [hN]; push_cast; linarith
  have hN2 : (2 : ℝ) ≤ N := by linarith
  set s : ℂ := 1 / 2 + I * t with hs
  have hsre : (s / 2).re = (1 / 2 - t.im) / 2 := by
    simp [hs]; ring
  have him := abs_im_le_norm t
  have hΛ := norm_completedZeta₀_le s N N
    (by rw [hsre]; have := neg_abs_le t.im; linarith [abs_le.1 (le_refl |t.im|)])
    (by rw [hsre]; have := le_abs_self t.im; linarith [neg_abs_le t.im])
  have hπ3 := Real.pi_gt_three
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hΛ' : ‖completedRiemannZeta₀ s‖ ≤ 3 * N.factorial := by
    refine hΛ.trans ?_
    have h1 : 3 * (N.factorial : ℝ) / π ^ N ≤ 3 * N.factorial :=
      div_le_self (by positivity) (one_le_pow₀ (by linarith))
    have h2 : 3 * (N.factorial : ℝ) / (π - 1) ≤ 3 * N.factorial :=
      div_le_self (by positivity) (by linarith)
    linarith
  have hsn : ‖s‖ ≤ N := by
    have : ‖s‖ ≤ 1 / 2 + x := by
      calc ‖s‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖I * t‖ := norm_add_le _ _
        _ = 1 / 2 + x := by simp [hx]
    linarith
  have hs1 : ‖s - 1‖ ≤ N := by
    have : ‖s - 1‖ ≤ 1 / 2 + x := by
      calc ‖s - 1‖ = ‖(-(1 / 2) : ℂ) + I * t‖ := by congr 1; simp [hs]; ring
        _ ≤ ‖(-(1 / 2) : ℂ)‖ + ‖I * t‖ := norm_add_le _ _
        _ = 1 / 2 + x := by simp [hx]
    linarith
  -- `‖Ξ(t)‖ ≤ 3N²·N! ≤ 3N^{N+2}`
  have hXi : ‖Xi t‖ ≤ 3 * ((N : ℝ) ^ 2 * N.factorial) := by
    unfold Xi xi
    rw [← hs, norm_div, Complex.norm_ofNat]
    have : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤ (N : ℝ) * N * (3 * N.factorial) + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_one]
      gcongr
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 * N.factorial := by
      have : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero N)
      nlinarith
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hfac : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hpow : (N : ℝ) ^ 2 * N.factorial ≤ Real.exp (6 * ((N : ℝ) * Real.sqrt N)) := by
    have hNpos : (0 : ℝ) < N := by linarith
    calc (N : ℝ) ^ 2 * N.factorial ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Real.exp ((N + 2 : ℝ) * Real.log N) := by
          rw [← pow_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hNpos]
          push_cast; ring_nf
      _ ≤ Real.exp (6 * ((N : ℝ) * Real.sqrt N)) := by
          apply Real.exp_le_exp.2
          have hl := log_le_two_sqrt hNpos
          have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
          have : (N + 2 : ℝ) ≤ 3 * N := by linarith
          nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hNs : (N : ℝ) * Real.sqrt N ≤ 3 * (x * Real.sqrt x) + 24 := by
    refine le_trans ?_ (shift_three_halves hx0)
    exact mul_le_mul hNx (Real.sqrt_le_sqrt hNx) (Real.sqrt_nonneg _) (by linarith)
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  rw [hx32]
  calc ‖Xi t‖ ≤ 3 * Real.exp (6 * ((N : ℝ) * Real.sqrt N)) := by linarith
    _ ≤ 3 * Real.exp (6 * (3 * (x * Real.sqrt x) + 24)) := by
        gcongr
    _ = 3 * Real.exp 144 * Real.exp (18 * (x * Real.sqrt x)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **Roadmap item 1, final form**: RH follows from real-rootedness of the `ĝₙ`, the uniform
zero-sum bound, the `D`-convergence hypotheses and the vanishing tail — with both named `Ξ`
inputs (`XiGrowth`, `Ξ(0) ≠ 0`) now discharged. -/
theorem rh_of_D_and_realRooted_final {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {B : ℝ} (hB : ∀ n, (∑' i : ZeroIdx (sqF (ghatC (g n) (a n))), ‖i.1⁻¹‖) ≤ B)
    {t : ℕ → ℝ}
    (hD : ∀ n, DFamW (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF Xi) => i.1⁻¹) (t n))
    (hε : Tendsto (fun n => tailEps (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF Xi) => i.1⁻¹) (t n)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  rh_of_D_and_realRooted_proved ha hint heven hg0 hRR xiGrowth Xi_zero_ne_zero hB hD hε

end Pilot1ca

#print axioms Pilot1ca.evenKernel_sub_one_le
#print axioms Pilot1ca.norm_completedZeta₀_le
#print axioms Pilot1ca.Xi_zero_ne_zero
#print axioms Pilot1ca.xiGrowth
#print axioms Pilot1ca.rh_of_D_and_realRooted_final
