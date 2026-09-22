import Mathlib

open Real MeasureTheory
open Filter Topology

noncomputable section

namespace Pilot1ca

/-! ## 1ca(iv): the pole leftover `E_pole = 2ĝ(i/2)²χ(i/2)` -/

/-- The normal distribution function extended to `ℂ`: `Φ(z) = (2π)^{−1/2} ∫_0^∞ e^{−(z−u)²/2} du`
(for real `z`, the substitution `t = z − u` gives `(2π)^{−1/2}∫_{−∞}^z e^{−t²/2} dt`). -/
def Phi (z : ℂ) : ℂ :=
  ((1 / Real.sqrt (2 * π) : ℝ) : ℂ) * ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(z - u) ^ 2 / 2)

theorem re_gauss (z : ℂ) (u : ℝ) :
    (-(z - u) ^ 2 / 2).re = (z.im ^ 2 - (z.re - u) ^ 2) / 2 := by
  rw [Complex.div_ofNat_re]
  simp [sq, Complex.mul_re]

/-- **`|Φ(z)| ≤ e^{((Im z)² − (Re z)²)/2}/2` for `Re z ≤ 0`** (the Gaussian tail bound, complex). -/
theorem norm_Phi_le {z : ℂ} (hz : z.re ≤ 0) :
    ‖Phi z‖ ≤ Real.exp ((z.im ^ 2 - z.re ^ 2) / 2) / 2 := by
  set E := Real.exp ((z.im ^ 2 - z.re ^ 2) / 2) with hE
  have hpt : ∀ u : ℝ, 0 < u →
      ‖Complex.exp (-(z - u) ^ 2 / 2)‖ ≤ E * Real.exp (-(1 / 2) * u ^ 2) := by
    intro u hu
    rw [Complex.norm_exp, hE, ← Real.exp_add, re_gauss]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (neg_nonneg.2 hz) hu.le]
  have hint : Integrable (fun u : ℝ => E * Real.exp (-(1 / 2) * u ^ 2))
      (volume.restrict (Set.Ioi 0)) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul E).integrableOn
  have hb := MeasureTheory.norm_integral_le_of_norm_le hint (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpt u hu)
  rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi] at hb
  have hs : Real.sqrt (π / (1 / 2)) = Real.sqrt (2 * π) := by
    congr 1; field_simp
  rw [hs] at hb
  have h2π : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  unfold Phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / Real.sqrt (2 * π) * ‖∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(z - u) ^ 2 / 2)‖
      ≤ 1 / Real.sqrt (2 * π) * (E * (Real.sqrt (2 * π) / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = E / 2 := by field_simp

/-- The even smooth cut of 1ca(iv): `χ(z) = Φ((z−T)/Δ) − Φ((z−T′)/Δ)` extended by its mirror. -/
def chi (T T' Δ : ℝ) (z : ℂ) : ℂ :=
  Phi ((z - T) / Δ) - Phi ((z - T') / Δ) + Phi ((-z - T) / Δ) - Phi ((-z - T') / Δ)

theorem norm_Phi_shift_le {T Δ c : ℝ} (hT : 0 < T) (hΔ : 0 < Δ) (T' : ℝ) (hTT' : T ≤ T')
    (hc : c = 1 / 2 ∨ c = -(1 / 2)) :
    ‖Phi ((((c : ℂ) * Complex.I) - T') / Δ)‖ ≤ Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2)) / 2 := by
  have hre : ((((c : ℂ) * Complex.I) - T') / Δ).re = -T' / Δ := by
    rw [Complex.div_ofReal_re]; simp
  have him : ((((c : ℂ) * Complex.I) - T') / Δ).im = c / Δ := by
    rw [Complex.div_ofReal_im]; simp
  have hT'0 : 0 < T' := lt_of_lt_of_le hT hTT'
  have hre0 : ((((c : ℂ) * Complex.I) - T') / Δ).re ≤ 0 := by
    rw [hre]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ.le
  refine le_trans (norm_Phi_le hre0) ?_
  rw [hre, him]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.exp_le_exp.2
  have hc2 : c ^ 2 = 1 / 4 := by rcases hc with h | h <;> rw [h] <;> norm_num
  have hTT : T ^ 2 ≤ T' ^ 2 := pow_le_pow_left₀ hT.le hTT' 2
  have e1 : ((c / Δ) ^ 2 - (-T' / Δ) ^ 2) / 2 = (c ^ 2 - T' ^ 2) / (2 * Δ ^ 2) := by
    field_simp
  have e2 : -(T ^ 2 - 1 / 4) / (2 * Δ ^ 2) = (1 / 4 - T ^ 2) / (2 * Δ ^ 2) := by ring
  rw [e1, e2, hc2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- **`|χ(±i/2)| ≤ 2e^{−(T² − 1/4)/(2Δ²)}`** (1ca(iv)), for `0 < T ≤ T′`. -/
theorem norm_chi_le {T T' Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ) (hTT' : T ≤ T') :
    ‖chi T T' Δ (Complex.I / 2)‖ ≤ 2 * Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2)) := by
  have e1 : Complex.I / 2 = ((1 / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : -(Complex.I / 2) = ((-(1 / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h1 := norm_Phi_shift_le hT hΔ T le_rfl (c := 1 / 2) (Or.inl rfl)
  have h2 := norm_Phi_shift_le hT hΔ T' hTT' (c := 1 / 2) (Or.inl rfl)
  have h3 := norm_Phi_shift_le hT hΔ T le_rfl (c := -(1 / 2)) (Or.inr rfl)
  have h4 := norm_Phi_shift_le hT hΔ T' hTT' (c := -(1 / 2)) (Or.inr rfl)
  unfold chi
  rw [e1, e2] at *
  rw [e2]
  calc ‖Phi ((((1 / 2 : ℝ) : ℂ) * Complex.I - T) / Δ) - Phi ((((1 / 2 : ℝ) : ℂ) * Complex.I - T') / Δ)
        + Phi ((((-(1 / 2)) : ℝ) * Complex.I - T) / Δ) - Phi ((((-(1 / 2)) : ℝ) * Complex.I - T') / Δ)‖
      ≤ ‖Phi ((((1 / 2 : ℝ) : ℂ) * Complex.I - T) / Δ)‖ + ‖Phi ((((1 / 2 : ℝ) : ℂ) * Complex.I - T') / Δ)‖
        + ‖Phi ((((-(1 / 2)) : ℝ) * Complex.I - T) / Δ)‖
        + ‖Phi ((((-(1 / 2)) : ℝ) * Complex.I - T') / Δ)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        refine add_le_add ?_ le_rfl
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add ?_ le_rfl
        exact norm_sub_le _ _
    _ ≤ 2 * Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2)) := by linarith

/-- The probe's transform `ĝ(z) = ∫_{−a}^{a} g(u) e^{izu} du` for a real probe `g` on `[−a, a]`. -/
def ghatC (g : ℝ → ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (-a)..a, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)

/-- **`|ĝ(i/2)| ≤ e^{a/2}‖g‖₁ ≤ √(2a) e^{a/2}`** for `‖g‖₂ = 1` on `[−a, a]` (1ca(iv)); the `L¹`–`L²`
step by the pointwise AM–GM `|g| ≤ (√(2a) g² + 1/√(2a))/2`. -/
theorem norm_ghat_half_le {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hgi : IntervalIntegrable g volume (-a) a)
    (hg2i : IntervalIntegrable (fun u => g u ^ 2) volume (-a) a)
    (hg2 : ∫ u in (-a)..a, g u ^ 2 = 1) :
    ‖ghatC g a (Complex.I / 2)‖ ≤ Real.sqrt (2 * a) * Real.exp (a / 2) := by
  have hle : -a ≤ a := by linarith
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hss : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  -- pointwise: ‖g(u) e^{−u/2}‖ ≤ e^{a/2} |g(u)| on [−a, a]
  have hpt : ∀ u ∈ Set.Ioc (-a) a,
      ‖((g u : ℝ) : ℂ) * Complex.exp (Complex.I * (Complex.I / 2) * u)‖
        ≤ Real.exp (a / 2) * |g u| := by
    intro u hu
    have e : Complex.I * (Complex.I / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
      push_cast
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (u / 2 : ℂ) * hI
    rw [e, norm_mul, Complex.norm_real, Complex.norm_exp, Complex.ofReal_re, Real.norm_eq_abs,
      mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.exp_le_exp.2
    linarith [hu.1]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hle
    (Filter.Eventually.of_forall hpt) (hgi.abs.const_mul (Real.exp (a / 2)))
  rw [intervalIntegral.integral_const_mul] at h1
  -- ∫|g| ≤ √(2a) by AM–GM with ∫ g² = 1
  have hL1 : ∫ u in (-a)..a, |g u| ≤ Real.sqrt (2 * a) := by
    have hpt2 : ∀ u, |g u| ≤ (Real.sqrt (2 * a) * g u ^ 2 + 1 / Real.sqrt (2 * a)) / 2 := by
      intro u
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hsq : |g u| ^ 2 = g u ^ 2 := sq_abs _
      have : 0 ≤ (Real.sqrt (2 * a) * |g u| - 1) ^ 2 := sq_nonneg _
      have e : (Real.sqrt (2 * a) * g u ^ 2 + 1 / Real.sqrt (2 * a)) * Real.sqrt (2 * a)
          = Real.sqrt (2 * a) ^ 2 * g u ^ 2 + 1 := by field_simp
      nlinarith [hs]
    calc ∫ u in (-a)..a, |g u|
        ≤ ∫ u in (-a)..a, (Real.sqrt (2 * a) * g u ^ 2 + 1 / Real.sqrt (2 * a)) / 2 := by
          apply intervalIntegral.integral_mono_on hle hgi.abs
          · exact ((hg2i.const_mul _).add intervalIntegrable_const).div_const 2
          · intro u _; exact hpt2 u
      _ = (Real.sqrt (2 * a) * 1 + 1 / Real.sqrt (2 * a) * (2 * a)) / 2 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_add
            (hg2i.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul, hg2,
            intervalIntegral.integral_const]
          simp
          ring
      _ = Real.sqrt (2 * a) := by
          field_simp
          rw [hss]
          ring
  unfold ghatC
  calc ‖∫ u in (-a)..a, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * (Complex.I / 2) * u)‖
      ≤ Real.exp (a / 2) * ∫ u in (-a)..a, |g u| := h1
    _ ≤ Real.exp (a / 2) * Real.sqrt (2 * a) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = Real.sqrt (2 * a) * Real.exp (a / 2) := by ring

/-- **`|E_pole| ≤ 8a eᵃ e^{−(T² − 1/4)/(2Δ²)}`** (1ca(iv)), `E_pole = 2ĝ(i/2)²χ(i/2)`. -/
theorem norm_Epole_le {g : ℝ → ℝ} {a T T' Δ : ℝ} (ha : 0 < a) (hT : 0 < T) (hΔ : 0 < Δ)
    (hTT' : T ≤ T') (hgi : IntervalIntegrable g volume (-a) a)
    (hg2i : IntervalIntegrable (fun u => g u ^ 2) volume (-a) a)
    (hg2 : ∫ u in (-a)..a, g u ^ 2 = 1) :
    ‖2 * ghatC g a (Complex.I / 2) ^ 2 * chi T T' Δ (Complex.I / 2)‖
      ≤ 8 * a * Real.exp a * Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2)) := by
  have hg := norm_ghat_half_le ha hgi hg2i hg2
  have hc := norm_chi_le hT hΔ hTT'
  have hss : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hea : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_two]
  have hg2' : ‖ghatC g a (Complex.I / 2)‖ ^ 2 ≤ (Real.sqrt (2 * a) * Real.exp (a / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  rw [mul_pow, hss, hea] at hg2'
  calc 2 * ‖ghatC g a (Complex.I / 2)‖ ^ 2 * ‖chi T T' Δ (Complex.I / 2)‖
      ≤ 2 * (2 * a * Real.exp a) * (2 * Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2))) := by
        gcongr
    _ = 8 * a * Real.exp a * Real.exp (-(T ^ 2 - 1 / 4) / (2 * Δ ^ 2)) := by ring

/-! ## 1ca(iv): the Stirling remainder, `|Re ψ(1/4 + ir/2) − ln(r/2)| ≤ 3/(2r²)` for `r ≥ 8` -/

/-- **Binet's second formula** (the named classical input of 1ca(iv); Mathlib has `Complex.digamma`
but not this representation): `ψ(z) = log z − 1/(2z) − 2∫_0^∞ t dt/((t² + z²)(e^{2πt} − 1))`,
`Re z > 0`. -/
def BinetFormula : Prop :=
  ∀ z : ℂ, 0 < z.re → Complex.digamma z = Complex.log z - 1 / (2 * z)
    - 2 * ∫ t in Set.Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ))

theorem bose_le {t : ℝ} (ht : 0 < t) :
    t / (Real.exp (2 * π * t) - 1) ≤ Real.exp (-π * t) / (2 * π) := by
  have hx : 0 < π * t := by positivity
  have hsinh : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.2 hx.le
  have hden : 0 < Real.exp (2 * π * t) - 1 := by
    have h1 := Real.add_one_le_exp (2 * π * t)
    have h2 : 0 < 2 * π * t := by positivity
    linarith
  rw [div_le_div_iff₀ hden (by positivity)]
  have e : Real.exp (-π * t) * (Real.exp (2 * π * t) - 1) = 2 * Real.sinh (π * t) := by
    rw [Real.sinh_eq, mul_sub, ← Real.exp_add, mul_one,
      show -π * t + 2 * π * t = π * t by ring, show -(π * t) = -π * t by ring]
    ring
  rw [e]
  nlinarith [Real.pi_pos]

/-- `z = 1/4 + ir/2`. -/
def zB (r : ℝ) : ℂ := 1 / 4 + Complex.I * r / 2

theorem zB_re (r : ℝ) : (zB r).re = 1 / 4 := by
  unfold zB; simp

theorem zB_im (r : ℝ) : (zB r).im = r / 2 := by
  unfold zB; simp

theorem denom_re (r t : ℝ) : ((t : ℂ) ^ 2 + zB r ^ 2).re = t ^ 2 + 1 / 16 - r ^ 2 / 4 := by
  have h1 : ((t : ℂ) ^ 2).re = t ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Complex.add_re, h1, sq (zB r), Complex.mul_re, zB_re, zB_im]
  ring

theorem denom_im (r t : ℝ) : ((t : ℂ) ^ 2 + zB r ^ 2).im = r / 4 := by
  have h1 : ((t : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.add_im, h1, sq (zB r), Complex.mul_im, zB_re, zB_im]
  ring

theorem norm_denom_ge {r t : ℝ} (hr : 8 ≤ r) :
    r / 4 ≤ ‖(t : ℂ) ^ 2 + zB r ^ 2‖ ∧
      (0 ≤ t → t ≤ r / 4 → r ^ 2 / 8 ≤ ‖(t : ℂ) ^ 2 + zB r ^ 2‖) := by
  constructor
  · have := Complex.abs_im_le_norm ((t : ℂ) ^ 2 + zB r ^ 2)
    rw [denom_im, abs_of_pos (by linarith)] at this
    exact this
  · intro ht0 ht
    have := Complex.abs_re_le_norm ((t : ℂ) ^ 2 + zB r ^ 2)
    rw [denom_re] at this
    have h1 : t ^ 2 ≤ r ^ 2 / 16 := by nlinarith
    have hneg : t ^ 2 + 1 / 16 - r ^ 2 / 4 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hneg] at this
    nlinarith

/-- The Binet integrand is dominated by `(8/r²)e^{−πt}/(2π)` below `r/4` and `(4/r)e^{−πt}/(2π)` above. -/
theorem binet_integrand_le {r t : ℝ} (hr : 8 ≤ r) (ht : 0 < t) :
    ‖(t : ℂ) / (((t : ℂ) ^ 2 + zB r ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ))‖
      ≤ 8 / r ^ 2 * (Real.exp (-π * t) / (2 * π))
        + Set.indicator (Set.Ioi (r / 4)) (fun t => 4 / r * (Real.exp (-π * t) / (2 * π))) t := by
  have hden : 0 < Real.exp (2 * π * t) - 1 := by
    have h1 := Real.add_one_le_exp (2 * π * t)
    have h2 : 0 < 2 * π * t := by positivity
    linarith
  have hb := bose_le ht
  obtain ⟨hn1, hn2⟩ := norm_denom_ge (t := t) hr
  have hr0 : 0 < r := by linarith
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hden]
  set N := ‖(t : ℂ) ^ 2 + zB r ^ 2‖ with hN
  by_cases hcase : t ≤ r / 4
  · have hNl : r ^ 2 / 8 ≤ N := hn2 ht.le hcase
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hcase), add_zero]
    calc t / (N * (Real.exp (2 * π * t) - 1))
        ≤ t / (r ^ 2 / 8 * (Real.exp (2 * π * t) - 1)) :=
          div_le_div_of_nonneg_left ht.le (by positivity)
            (mul_le_mul_of_nonneg_right hNl hden.le)
      _ = 8 / r ^ 2 * (t / (Real.exp (2 * π * t) - 1)) := by field_simp
      _ ≤ 8 / r ^ 2 * (Real.exp (-π * t) / (2 * π)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
  · have hlt : r / 4 < t := lt_of_not_ge hcase
    rw [Set.indicator_of_mem (by simp only [Set.mem_Ioi]; exact hlt)]
    have h1 : t / (N * (Real.exp (2 * π * t) - 1)) ≤ 4 / r * (Real.exp (-π * t) / (2 * π)) := by
      calc t / (N * (Real.exp (2 * π * t) - 1))
          ≤ t / (r / 4 * (Real.exp (2 * π * t) - 1)) :=
            div_le_div_of_nonneg_left ht.le (by positivity)
              (mul_le_mul_of_nonneg_right hn1 hden.le)
        _ = 4 / r * (t / (Real.exp (2 * π * t) - 1)) := by field_simp
        _ ≤ 4 / r * (Real.exp (-π * t) / (2 * π)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
    have h0 : 0 ≤ 8 / r ^ 2 * (Real.exp (-π * t) / (2 * π)) := by positivity
    linarith

theorem binet_bound_integral {r : ℝ} (hr : 8 ≤ r) :
    IntegrableOn (fun t => 8 / r ^ 2 * (Real.exp (-π * t) / (2 * π))
        + Set.indicator (Set.Ioi (r / 4)) (fun t => 4 / r * (Real.exp (-π * t) / (2 * π))) t)
        (Set.Ioi 0) ∧
    ∫ t in Set.Ioi (0 : ℝ), (8 / r ^ 2 * (Real.exp (-π * t) / (2 * π))
        + Set.indicator (Set.Ioi (r / 4)) (fun t => 4 / r * (Real.exp (-π * t) / (2 * π))) t)
      = 4 / (π ^ 2 * r ^ 2) + 2 * Real.exp (-π * (r / 4)) / (π ^ 2 * r) := by
  have hr0 : 0 < r := by linarith
  have he : IntegrableOn (fun t => Real.exp (-π * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 Real.pi_pos
  have h1 : IntegrableOn (fun t => 8 / r ^ 2 * (Real.exp (-π * t) / (2 * π))) (Set.Ioi 0) :=
    (he.div_const _).const_mul _
  have h2' : IntegrableOn (fun t => 4 / r * (Real.exp (-π * t) / (2 * π))) (Set.Ioi 0) :=
    (he.div_const _).const_mul _
  have h2 : IntegrableOn (Set.indicator (Set.Ioi (r / 4))
      (fun t => 4 / r * (Real.exp (-π * t) / (2 * π)))) (Set.Ioi 0) :=
    h2'.indicator measurableSet_Ioi
  refine ⟨h1.add h2, ?_⟩
  rw [MeasureTheory.integral_add h1 h2, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right (by linarith : (0 : ℝ) ≤ r / 4),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_div, MeasureTheory.integral_div,
    integral_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) 0,
    integral_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) (r / 4)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- `r e^{−πr/4} ≤ 8/115` for `r ≥ 8` (using `e^{2π} ≥ e⁶ ≥ 115`). -/
theorem tail_exp_le {r : ℝ} (hr : 8 ≤ r) : r * Real.exp (-π * (r / 4)) ≤ 8 / 115 := by
  have h6 : (115 : ℝ) ≤ Real.exp 6 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have h2π : Real.exp 6 ≤ Real.exp (2 * π) := Real.exp_le_exp.2 (by linarith [Real.pi_gt_three])
  have hlin : r / 8 ≤ 1 + π * (r - 8) / 4 := by nlinarith [Real.pi_gt_three]
  have hexp : 1 + π * (r - 8) / 4 ≤ Real.exp (π * (r - 8) / 4) := by
    have := Real.add_one_le_exp (π * (r - 8) / 4); linarith
  have hsplit : Real.exp (π * (r / 4)) = Real.exp (2 * π) * Real.exp (π * (r - 8) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hbig : 115 * (r / 8) ≤ Real.exp (π * (r / 4)) := by
    rw [hsplit]
    have h0 : 0 ≤ r / 8 := by linarith
    calc 115 * (r / 8) ≤ Real.exp (2 * π) * (1 + π * (r - 8) / 4) :=
          mul_le_mul (by linarith) hlin h0 (by positivity)
      _ ≤ Real.exp (2 * π) * Real.exp (π * (r - 8) / 4) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  rw [show -π * (r / 4) = -(π * (r / 4)) by ring, Real.exp_neg]
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **1ca(iv): `|Re ψ(1/4 + ir/2) − ln(r/2)| ≤ 3/(2r²)` for `r ≥ 8`**, from Binet's formula. The
three pieces are `(1/2)ln(1 + 1/(4r²)) ≤ 1/(8r²)`, `Re 1/(2z) = 2/(1 + 4r²) ≤ 1/(2r²)`, and the Binet
integral `≤ 8/(π²r²) + 4e^{−πr/4}/(π²r)`. -/
theorem binet_remainder_le (hB : BinetFormula) {r : ℝ} (hr : 8 ≤ r) :
    |(Complex.digamma (zB r)).re - Real.log (r / 2)| ≤ 3 / (2 * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hψ := hB (zB r) (by rw [zB_re]; norm_num)
  rw [hψ]
  set I := ∫ t in Set.Ioi (0 : ℝ),
      (t : ℂ) / (((t : ℂ) ^ 2 + zB r ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) with hI
  -- the log term
  have hnsq : Complex.normSq (zB r) = r ^ 2 / 4 * (1 + 1 / (4 * r ^ 2)) := by
    rw [Complex.normSq_apply, zB_re, zB_im]; field_simp; ring
  have hlog : (Complex.log (zB r)).re = Real.log (r / 2) + Real.log (1 + 1 / (4 * r ^ 2)) / 2 := by
    rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), hnsq,
      Real.log_mul (by positivity) (by positivity),
      show r ^ 2 / 4 = (r / 2) ^ 2 by ring, Real.log_pow]
    push_cast
    ring
  -- the 1/(2z) term
  have hinv : (1 / (2 * zB r)).re = 2 / (1 + 4 * r ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have hre : (2 * zB r).re = 1 / 2 := by
      rw [Complex.mul_re, zB_re, zB_im]; norm_num
    have him : (2 * zB r).im = r := by
      rw [Complex.mul_im, zB_re, zB_im]; norm_num; ring
    rw [hre, him]
    field_simp
    ring
  -- the Binet integral
  obtain ⟨hbi, hbv⟩ := binet_bound_integral hr
  have hInorm : ‖I‖ ≤ 4 / (π ^ 2 * r ^ 2) + 2 * Real.exp (-π * (r / 4)) / (π ^ 2 * r) := by
    rw [← hbv]
    exact MeasureTheory.norm_integral_le_of_norm_le hbi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact binet_integrand_le hr ht)
  have hre : (Complex.log (zB r) - 1 / (2 * zB r) - 2 * I).re
      = (Complex.log (zB r)).re - (1 / (2 * zB r)).re - 2 * I.re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hre, hlog, hinv]
  have hIre := Complex.abs_re_le_norm I
  have hy : 0 < 1 / (4 * r ^ 2) := by positivity
  have hl0 : 0 ≤ Real.log (1 + 1 / (4 * r ^ 2)) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (1 + 1 / (4 * r ^ 2)) ≤ 1 / (4 * r ^ 2) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / (4 * r ^ 2))
    linarith
  have hB0 : 0 ≤ 2 / (1 + 4 * r ^ 2) := by positivity
  have hB1 : 2 / (1 + 4 * r ^ 2) ≤ 1 / (2 * r ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have htail := tail_exp_le hr
  have hpi2 : 9.86 ≤ π ^ 2 := by nlinarith [Real.pi_gt_d6]
  -- ‖I‖ ≤ 7/(16 r²)
  have hI2 : 2 * ‖I‖ ≤ 7 / (8 * r ^ 2) := by
    have h1 : 2 * (4 / (π ^ 2 * r ^ 2) + 2 * Real.exp (-π * (r / 4)) / (π ^ 2 * r))
        = (8 + 4 * (r * Real.exp (-π * (r / 4)))) / (π ^ 2 * r ^ 2) := by
      field_simp; ring
    have h2 : (8 + 4 * (r * Real.exp (-π * (r / 4)))) / (π ^ 2 * r ^ 2) ≤ 7 / (8 * r ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hr2 : 0 < r ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right htail hr2.le]
    linarith
  have h8 : Real.log (1 + 1 / (4 * r ^ 2)) / 2 ≤ 1 / (8 * r ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have := mul_le_mul_of_nonneg_right hl1 (by positivity : (0 : ℝ) ≤ 8 * r ^ 2)
    rw [show 1 / (4 * r ^ 2) * (8 * r ^ 2) = 2 by field_simp; ring] at this
    linarith
  have e1 : 1 / (2 * r ^ 2) + 7 / (8 * r ^ 2) ≤ 3 / (2 * r ^ 2) := by
    have : 1 / (2 * r ^ 2) + 7 / (8 * r ^ 2) = 11 / (8 * r ^ 2) := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e2 : 1 / (8 * r ^ 2) + 7 / (8 * r ^ 2) ≤ 3 / (2 * r ^ 2) := by
    have : 1 / (8 * r ^ 2) + 7 / (8 * r ^ 2) = 1 / r ^ 2 := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hlo := le_abs_self I.re
  have hhi := neg_abs_le I.re
  rw [abs_le]
  constructor <;> linarith

/-! ## 1ca(iv): the Stirling remainder `E_arch` and the exterior identity -/

/-- `Re ψ(1/4 + ir/2)`. -/
def psiRe (r : ℝ) : ℝ := (Complex.digamma (zB r)).re

/-- **The Stirling remainder** `E_arch = (1/π)∫_0^∞ h(r)[Re ψ(1/4 + ir/2) − ln(r/2)] dr`. -/
def Earch (hR : ℝ → ℝ) : ℝ := 1 / π * ∫ r in Set.Ioi (0 : ℝ), hR r * (psiRe r - Real.log (r / 2))

/-- **1ca(iv): `|E_arch| ≤ (3/2)/(T² ln(T/2π))` × the smooth count's integral beyond `T`, up to the
cut's tail below `T`** (the two explicit tail terms), for a weight `h ≥ 0` and `T ≥ 8`. -/
theorem Earch_bound (hB : BinetFormula) {hR : ℝ → ℝ} {T : ℝ} (hT : 8 ≤ T)
    (hpos : ∀ r, 0 < r → 0 ≤ hR r)
    (hf : IntegrableOn (fun r => hR r * (psiRe r - Real.log (r / 2))) (Set.Ioi 0))
    (hsm : IntegrableOn (fun r => hR r * Real.log (r / (2 * π))) (Set.Ioi T))
    (hmid : IntegrableOn (fun r => hR r * (1 / r ^ 2)) (Set.Ioc 8 T)) :
    |Earch hR| ≤ 3 / 2 / (T ^ 2 * Real.log (T / (2 * π)))
          * (1 / π * ∫ r in Set.Ioi T, hR r * Real.log (r / (2 * π)))
        + 3 / (2 * π) * (∫ r in Set.Ioc 8 T, hR r * (1 / r ^ 2))
        + 1 / π * ∫ r in Set.Ioc 0 8, |hR r * (psiRe r - Real.log (r / 2))| := by
  set f := fun r => hR r * (psiRe r - Real.log (r / 2)) with hf_def
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log (T / (2 * π)) := by
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    linarith [Real.pi_lt_d2]
  have hfa : IntegrableOn (fun r => |f r|) (Set.Ioi 0) := hf.abs
  -- split (0, ∞) = (0, 8] ∪ (8, T] ∪ (T, ∞)
  have hU1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 8 ∪ Set.Ioi 8 := (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hU2 : Set.Ioi (8 : ℝ) = Set.Ioc 8 T ∪ Set.Ioi T := (Set.Ioc_union_Ioi_eq_Ioi hT).symm
  have hs8 : Set.Ioi (8 : ℝ) ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi (by norm_num)
  have hsplit : ∫ r in Set.Ioi (0 : ℝ), |f r| = (∫ r in Set.Ioc (0 : ℝ) 8, |f r|)
      + (∫ r in Set.Ioc 8 T, |f r|) + ∫ r in Set.Ioi T, |f r| := by
    rw [hU1, MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hfa.mono_set (by rw [hU1]; exact Set.subset_union_left))
      (hfa.mono_set (by rw [hU1]; exact Set.subset_union_right)), hU2,
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hfa.mono_set (fun x hx => lt_trans (by norm_num) hx.1))
      (hfa.mono_set (fun x hx => lt_trans hT0 hx))]
    ring
  -- the middle piece: |f| ≤ (3/2) h/r²
  have hmidb : ∫ r in Set.Ioc 8 T, |f r| ≤ 3 / 2 * ∫ r in Set.Ioc 8 T, hR r * (1 / r ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_mono_on
      (hfa.mono_set (Set.Ioc_subset_Ioi_self.trans hs8)) (hmid.const_mul _) measurableSet_Ioc
    intro r hr
    have hr8 : 8 ≤ r := hr.1.le
    have hb := binet_remainder_le hB hr8
    have hh := hpos r (by linarith [hr.1])
    simp only [hf_def, abs_mul, abs_of_nonneg hh]
    unfold psiRe
    calc hR r * |(Complex.digamma (zB r)).re - Real.log (r / 2)| ≤ hR r * (3 / (2 * r ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hh
      _ = 3 / 2 * (hR r * (1 / r ^ 2)) := by field_simp
  -- the far piece: |f| ≤ (3/2)/(T² ln(T/2π)) · h ln(r/2π)
  have hfarb : ∫ r in Set.Ioi T, |f r| ≤ 3 / 2 / (T ^ 2 * Real.log (T / (2 * π)))
      * ∫ r in Set.Ioi T, hR r * Real.log (r / (2 * π)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_mono_on
      (hfa.mono_set ((Set.Ioi_subset_Ioi (by linarith)).trans (le_refl _)))
      (hsm.const_mul _) measurableSet_Ioi
    intro r hr
    have hrT : T < r := hr
    have hr8 : 8 ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    have hb := binet_remainder_le hB hr8
    have hh := hpos r hr0
    have hlogr : Real.log (T / (2 * π)) ≤ Real.log (r / (2 * π)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hrT.le (by positivity))
    simp only [hf_def, abs_mul, abs_of_nonneg hh]
    unfold psiRe
    have hkey : 3 / (2 * r ^ 2) ≤ 3 / 2 / (T ^ 2 * Real.log (T / (2 * π))) * Real.log (r / (2 * π)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hT2 : T ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hT0.le hrT.le 2
      have h1 : T ^ 2 * Real.log (T / (2 * π)) ≤ r ^ 2 * Real.log (r / (2 * π)) :=
        mul_le_mul hT2 hlogr hlogT.le (by positivity)
      nlinarith
    calc hR r * |(Complex.digamma (zB r)).re - Real.log (r / 2)| ≤ hR r * (3 / (2 * r ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hh
      _ ≤ hR r * (3 / 2 / (T ^ 2 * Real.log (T / (2 * π))) * Real.log (r / (2 * π))) :=
          mul_le_mul_of_nonneg_left hkey hh
      _ = 3 / 2 / (T ^ 2 * Real.log (T / (2 * π))) * (hR r * Real.log (r / (2 * π))) := by ring
  have habs : |∫ r in Set.Ioi (0 : ℝ), f r| ≤ ∫ r in Set.Ioi (0 : ℝ), |f r| :=
    MeasureTheory.abs_integral_le_integral_abs
  unfold Earch
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have hπ : 0 < 1 / π := by positivity
  calc 1 / π * |∫ r in Set.Ioi (0 : ℝ), hR r * (psiRe r - Real.log (r / 2))|
      ≤ 1 / π * ((∫ r in Set.Ioc (0 : ℝ) 8, |f r|) + (∫ r in Set.Ioc 8 T, |f r|)
          + ∫ r in Set.Ioi T, |f r|) := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left habs hπ.le
    _ ≤ 1 / π * ((∫ r in Set.Ioc (0 : ℝ) 8, |f r|)
          + 3 / 2 * (∫ r in Set.Ioc 8 T, hR r * (1 / r ^ 2))
          + 3 / 2 / (T ^ 2 * Real.log (T / (2 * π))) * ∫ r in Set.Ioi T, hR r * Real.log (r / (2 * π))) := by
        gcongr
    _ = _ := by ring

/-- `Re ψ(1/4 − ir/2) = Re ψ(1/4 + ir/2)`, from `Γ(s̄) = Γ(s)‾`. -/
theorem psiRe_even (r : ℝ) : psiRe (-r) = psiRe r := by
  have hconj : zB (-r) = (starRingEnd ℂ) (zB r) := by
    apply Complex.ext
    · rw [Complex.conj_re, zB_re, zB_re]
    · rw [Complex.conj_im, zB_im, zB_im]; ring
  have hnp : ∀ m : ℕ, zB r ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [zB_re] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hdiff := (Complex.differentiableAt_Gamma (zB r) hnp).hasDerivAt
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext z; simp [Complex.Gamma_conj]
  have hd := hdiff.conj_conj
  rw [hG] at hd
  unfold psiRe
  rw [hconj, Complex.digamma, logDeriv_apply, logDeriv_apply, hd.deriv, Complex.Gamma_conj,
    ← map_div₀, Complex.conj_re]

/-- `g_h(u) = (1/2π)∫_ℝ h(r)cos(ru) dr` and the paper's `f_χ(u) = (1/π)∫_0^∞ h(r)cos(ru) dr`. -/
def gh (hR : ℝ → ℝ) (u : ℝ) : ℝ := 1 / (2 * π) * ∫ r, hR r * Real.cos (r * u)
def fchi (hR : ℝ → ℝ) (u : ℝ) : ℝ := 1 / π * ∫ r in Set.Ioi (0 : ℝ), hR r * Real.cos (r * u)

/-- **Weil's explicit formula** (Guinand–Weil; the named classical input of 1ca(iv)) for a test
function `h` with real values `hR` on `ℝ`: `Σ_ρ h(t_ρ) = h(i/2) + h(−i/2) − g_h(0) ln π
+ (1/2π)∫_ℝ h(r) Re ψ(1/4 + ir/2) dr − 2Σ_n Λ(n) n^{−1/2} g_h(ln n)`, `t_ρ = (ρ − 1/2)/i`, the
zeros counted with multiplicity by the family `ρ`. -/
def WeilExplicit {ι : Type*} (ρ : ι → ℂ) (h : ℂ → ℂ) (hR : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, h r = hR r) ∧ HasSum (fun i => h ((ρ i - 1 / 2) / Complex.I))
    (h (Complex.I / 2) + h (-(Complex.I / 2))
      + ((-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
        - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ))

theorem gh_eq_fchi {hR : ℝ → ℝ} (heven : ∀ r, hR (-r) = hR r) (u : ℝ) : gh hR u = fchi hR u := by
  unfold gh fchi
  have h1 : ∫ r, hR r * Real.cos (r * u) = ∫ r, hR |r| * Real.cos (|r| * u) := by
    congr 1; funext r
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr]; simp only [heven, neg_mul, Real.cos_neg]
  have h2 : ∫ r, hR |r| * Real.cos (|r| * u)
      = 2 * ∫ r in Set.Ioi (0 : ℝ), hR r * Real.cos (r * u) :=
    integral_comp_abs (f := fun x => hR x * Real.cos (x * u))
  have hc : ∀ X : ℝ, 1 / (2 * π) * (2 * X) = 1 / π * X := by
    intro X; field_simp
  rw [h1, h2]
  exact hc _

/-- **1ca(iv), the exterior identity, exactly**: from Weil's explicit formula for an even `h = ĝ²χ`,
`Σ_ρ h(t_ρ) = (1/π)∫_0^∞ h ln(r/2π) + E_arch + E_pole − 2Σ Λ(n) n^{−1/2} f_χ(ln n)` with
`E_pole = 2h(i/2)` — the smooth count's integral of the transform squared, the Stirling remainder, the
pole term, and the prime shells. -/
theorem exterior_identity {ι : Type*} {ρ : ι → ℂ} {h : ℂ → ℂ} {hR : ℝ → ℝ}
    (hEF : WeilExplicit ρ h hR) (hevenC : ∀ z, h (-z) = h z)
    (hi0 : IntegrableOn hR (Set.Ioi 0))
    (hi1 : IntegrableOn (fun r => hR r * Real.log (r / (2 * π))) (Set.Ioi 0))
    (hi2 : IntegrableOn (fun r => hR r * (psiRe r - Real.log (r / 2))) (Set.Ioi 0)) :
    HasSum (fun i => h ((ρ i - 1 / 2) / Complex.I))
      (((1 / π * (∫ r in Set.Ioi (0 : ℝ), hR r * Real.log (r / (2 * π))) + Earch hR
          - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * fchi hR (Real.log n) : ℝ) : ℂ)
        + 2 * h (Complex.I / 2)) := by
  obtain ⟨hRh, hEF⟩ := hEF
  have heven : ∀ r, hR (-r) = hR r := by
    intro r
    have := hevenC (r : ℂ)
    rw [← Complex.ofReal_neg, hRh, hRh] at this
    exact_mod_cast this
  have hpole : h (-(Complex.I / 2)) = h (Complex.I / 2) := hevenC _
  -- the archimedean integral over ℝ is twice the half-line one (even integrand)
  have harch : 1 / (2 * π) * (∫ r, hR r * psiRe r)
      = 1 / π * ∫ r in Set.Ioi (0 : ℝ), hR r * psiRe r := by
    have h1 : ∫ r, hR r * psiRe r = ∫ r, hR |r| * psiRe |r| := by
      congr 1; funext r
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr]; simp only [heven, psiRe_even]
    have h2 : ∫ r, hR |r| * psiRe |r| = 2 * ∫ r in Set.Ioi (0 : ℝ), hR r * psiRe r :=
      integral_comp_abs (f := fun x => hR x * psiRe x)
    rw [h1, h2]
    field_simp
  have hg0 : gh hR 0 = 1 / π * ∫ r in Set.Ioi (0 : ℝ), hR r := by
    rw [gh_eq_fchi heven]; unfold fchi; simp only [mul_zero, Real.cos_zero, mul_one]
  -- the log split on (0, ∞): Re ψ − ln π = ln(r/2π) + (Re ψ − ln(r/2))
  have hi3 : IntegrableOn (fun r => hR r * Real.log π) (Set.Ioi 0) := hi0.mul_const _
  have hsum : IntegrableOn (fun r => hR r * Real.log (r / (2 * π))
      + hR r * (psiRe r - Real.log (r / 2))) (Set.Ioi 0) := hi1.add hi2
  have hpsi : IntegrableOn (fun r => hR r * psiRe r) (Set.Ioi 0) := by
    refine (hsum.add hi3).congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr0 : 0 < r := hr
    show hR r * Real.log (r / (2 * π)) + hR r * (psiRe r - Real.log (r / 2)) + hR r * Real.log π
      = hR r * psiRe r
    rw [Real.log_div hr0.ne' (by positivity), Real.log_div hr0.ne' (by norm_num),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  have hsplit : -(1 / π * ∫ r in Set.Ioi (0 : ℝ), hR r) * Real.log π
      + 1 / π * (∫ r in Set.Ioi (0 : ℝ), hR r * psiRe r)
      = 1 / π * (∫ r in Set.Ioi (0 : ℝ), hR r * Real.log (r / (2 * π))) + Earch hR := by
    unfold Earch
    have e : ∫ r in Set.Ioi (0 : ℝ), hR r * psiRe r
        = (∫ r in Set.Ioi (0 : ℝ), hR r * Real.log (r / (2 * π)))
          + (∫ r in Set.Ioi (0 : ℝ), hR r * (psiRe r - Real.log (r / 2)))
          + ∫ r in Set.Ioi (0 : ℝ), hR r * Real.log π := by
      rw [← MeasureTheory.integral_add hi1 hi2, ← MeasureTheory.integral_add hsum hi3]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 < r := hr
      simp only
      rw [Real.log_div hr0.ne' (by positivity), Real.log_div hr0.ne' (by norm_num),
        Real.log_mul (by norm_num) Real.pi_ne_zero]
      ring
    rw [e, MeasureTheory.integral_mul_const]
    ring
  have hprimes : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n)
      = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * fchi hR (Real.log n) := by
    congr 1; funext n; rw [gh_eq_fchi heven]
  convert hEF using 1
  rw [hpole, harch, hg0, hprimes, ← hsplit]
  push_cast
  ring

/-- The cut is even: `χ(−z) = χ(z)`. -/
theorem chi_even (T T' Δ : ℝ) (z : ℂ) : chi T T' Δ (-z) = chi T T' Δ z := by
  unfold chi
  rw [neg_neg]
  ring

/-- An even probe has an even transform: `ĝ(−z) = ĝ(z)`. -/
theorem ghatC_even {g : ℝ → ℝ} (hg : ∀ u, g (-u) = g u) (a : ℝ) (z : ℂ) :
    ghatC g a (-z) = ghatC g a z := by
  unfold ghatC
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
    (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
  simp only [neg_neg] at h
  rw [← h]
  congr 1
  funext u
  simp only [hg, Complex.ofReal_neg]
  congr 2
  ring

/-- **1ca(iv) for the paper's `h = ĝ²χ`** with an even probe `g` on `[−a, a]`: the zeros' sum
`Σ_ρ ĝ(t_ρ)²χ(t_ρ)` is the smooth count's integral plus `E_arch` plus the pole term
`E_pole = 2ĝ(i/2)²χ(i/2)` (bounded by `norm_Epole_le`) less the prime shells. -/
theorem exterior_identity_probe {ι : Type*} {ρ : ι → ℂ} {g : ℝ → ℝ} {a T T' Δ : ℝ}
    {hR : ℝ → ℝ} (hg : ∀ u, g (-u) = g u)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2 * chi T T' Δ z) hR)
    (hi0 : IntegrableOn hR (Set.Ioi 0))
    (hi1 : IntegrableOn (fun r => hR r * Real.log (r / (2 * π))) (Set.Ioi 0))
    (hi2 : IntegrableOn (fun r => hR r * (psiRe r - Real.log (r / 2))) (Set.Ioi 0)) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2
        * chi T T' Δ ((ρ i - 1 / 2) / Complex.I))
      (((1 / π * (∫ r in Set.Ioi (0 : ℝ), hR r * Real.log (r / (2 * π))) + Earch hR
          - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * fchi hR (Real.log n) : ℝ) : ℂ)
        + 2 * ghatC g a (Complex.I / 2) ^ 2 * chi T T' Δ (Complex.I / 2)) := by
  have h := exterior_identity hEF (fun z => by simp only [chi_even, ghatC_even hg]) hi0 hi1 hi2
  rw [mul_assoc 2]
  exact h

end Pilot1ca

#print axioms Pilot1ca.norm_Phi_le
#print axioms Pilot1ca.norm_chi_le
#print axioms Pilot1ca.norm_ghat_half_le
#print axioms Pilot1ca.norm_Epole_le
#print axioms Pilot1ca.binet_remainder_le
#print axioms Pilot1ca.Earch_bound
#print axioms Pilot1ca.psiRe_even
#print axioms Pilot1ca.exterior_identity
#print axioms Pilot1ca.exterior_identity_probe
