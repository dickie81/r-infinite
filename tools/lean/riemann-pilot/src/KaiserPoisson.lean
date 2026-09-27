import Mathlib
import KaiserPW

/-! # Poisson summation for the Kaiser pair (round 163, part 3)

`H = kH` on the real line and `h = 𝓕⁻ H`. By Paley–Wiener (`kh_eq_zero`), `h` is continuous, even and
supported in `[−L, L]`, and `𝓕 h = H`. Poisson summation for `y ↦ h(xy)` gives

  `Σ_{n∈ℤ} h(nx) = x⁻¹ Σ_{n∈ℤ} H(n/x)`,

and with `h(0) = ∫H = 0` and `H(0) = 0` this is Connes' `E(h)(x) = E(H)(1/x)` (`poisson_E`), where
`E(F)(x) = √x Σ_{n≥1} F(nx)`.
-/

open Complex Filter Topology MeasureTheory Real
open scoped FourierTransform

noncomputable section

namespace Kaiser

/-- Standing hypotheses on the parameters. -/
structure Par (L η : ℝ) : Prop where
  pos : 0 < η
  small : π * η ≤ 1
  big : 4 * η ≤ L

/-- `H` on the real line. -/
def Hr (L η α : ℝ) (x : ℝ) : ℂ := kH L η α x

/-- `h = 𝓕⁻ H`. -/
def kh (L η α : ℝ) : ℝ → ℂ := 𝓕⁻ (Hr L η α)

/-- Connes' map: `E(F)(x) = √x Σ_{n≥1} F(nx)`. -/
def E (F : ℝ → ℂ) (x : ℝ) : ℂ := (Real.sqrt x : ℂ) * ∑' n : ℕ, F ((n + 1) * x)

variable {L η α : ℝ}

theorem Hr_neg (x : ℝ) : Hr L η α (-x) = Hr L η α x := by
  simp only [Hr, ofReal_neg, kH_neg]

theorem Hr_zero : Hr L η α 0 = 0 := by simp [Hr, kH]

theorem integrable_Hr (hp : Par L η) : Integrable (Hr L η α) :=
  integrable_kH_real hp.pos hp.small hp.big

theorem continuous_Hr : Continuous (Hr L η α) := continuous_kH_real L η α

theorem norm_Hr_le (hp : Par L η) (x : ℝ) : ‖Hr L η α x‖ ≤ kA L η α / (1 + x ^ 2) :=
  norm_kH_real_le hp.pos hp.small hp.big x

theorem kh_zero : kh L η α 0 = ∫ x, Hr L η α x := by
  simp [kh, fourierInv_eq]

theorem kh_neg (ξ : ℝ) : kh L η α (-ξ) = kh L η α ξ := by
  unfold kh
  rw [fourierInv_eq, fourierInv_eq]
  rw [← integral_neg_eq_self]
  congr 1; funext v
  simp only [inner_neg_left, inner_neg_right, neg_neg, Hr_neg]

theorem kh_vanish (hp : Par L η) {ξ : ℝ} (hξ : L < |ξ|) : kh L η α ξ = 0 := by
  rcases le_or_gt 0 ξ with h | h
  · rw [abs_of_nonneg h] at hξ
    exact kh_eq_zero hp.pos hp.small hp.big hξ
  · rw [abs_of_neg h] at hξ
    rw [← neg_neg ξ, kh_neg]
    exact kh_eq_zero hp.pos hp.small hp.big hξ

theorem continuous_kh (hp : Par L η) : Continuous (kh L η α) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (integrable_Hr hp)

theorem hasCompactSupport_kh (hp : Par L η) : HasCompactSupport (kh L η α) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(L + 1)) (L + 1)) isCompact_Icc fun ξ hξ => ?_
  apply kh_vanish hp
  simp only [Set.mem_Icc, not_and_or, not_le] at hξ
  rcases hξ with h | h
  · rw [abs_of_neg (by linarith [hp.big, hp.pos])]; linarith
  · rw [abs_of_pos (by linarith [hp.big, hp.pos])]; linarith

theorem integrable_kh (hp : Par L η) : Integrable (kh L η α) :=
  (continuous_kh hp).integrable_of_hasCompactSupport (hasCompactSupport_kh hp)

/-- `𝓕 H = h` (evenness). -/
theorem fourier_Hr : 𝓕 (Hr L η α) = kh L η α := by
  funext w
  have h := fourierInv_eq_fourier_neg (Hr L η α) (-w)
  rw [neg_neg] at h
  rw [← h]
  exact kh_neg w

/-- **Fourier inversion**: `𝓕 h = H`. -/
theorem fourier_kh (hp : Par L η) : 𝓕 (kh L η α) = Hr L η α := by
  funext v
  have := (integrable_Hr hp (α := α)).fourier_fourierInv_eq (by rw [fourier_Hr]; exact integrable_kh hp)
    (continuous_Hr.continuousAt (x := v))
  exact this

/-- Fourier transform of `y ↦ h(xy)`. -/
theorem fourier_scaled (hp : Par L η) {x : ℝ} (hx : 0 < x) (w : ℝ) :
    𝓕 (fun y : ℝ => kh L η α (x * y)) w = ((x⁻¹ : ℝ) : ℂ) * Hr L η α (w / x) := by
  rw [← fourier_kh hp, fourier_real_eq, fourier_real_eq]
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => 𝐞 (-(y * (w / x))) • kh L η α y) x
  have e : ∀ v : ℝ, 𝐞 (-(x * v * (w / x))) • kh L η α (x * v) = 𝐞 (-(v * w)) • kh L η α (x * v) := by
    intro v; congr 3; field_simp
  simp_rw [e] at h
  rw [h, abs_of_pos (inv_pos.2 hx), ← smul_eq_mul, ← Complex.coe_smul]

theorem isBigO_of_eventually_zero {f : ℝ → ℂ} {b : ℝ} (hf : f =ᶠ[cocompact ℝ] 0) :
    f =O[cocompact ℝ] (|·| ^ (-b)) :=
  (hf.isBigO).trans (Asymptotics.isBigO_zero _ _)

/-- **Poisson summation, scaled.** -/
theorem poisson_scaled (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℤ, kh L η α (x * n) = ((x⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, Hr L η α (n / x) := by
  set φ : ℝ → ℂ := fun y => kh L η α (x * y)
  have hc : Continuous φ := (continuous_kh hp).comp (continuous_const.mul continuous_id)
  have hsupp : HasCompactSupport φ :=
    (hasCompactSupport_kh hp).comp_homeomorph (Homeomorph.mulLeft₀ x hx.ne')
  have hφ : φ =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    have h0 := hasCompactSupport_iff_eventuallyEq.1 hsupp
    rw [coclosedCompact_eq_cocompact] at h0
    exact isBigO_of_eventually_zero h0
  have hFφ : 𝓕 φ =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    have e : 𝓕 φ = fun w => ((x⁻¹ : ℝ) : ℂ) * Hr L η α (w / x) := funext (fourier_scaled hp hx)
    rw [e]
    refine Asymptotics.IsBigO.of_bound (x⁻¹ * kA L η α * x ^ 2) ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with w hw
    have hw0 : w ≠ 0 := hw
    have hw2 : 0 < w ^ 2 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hx), Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
    have hb := norm_Hr_le hp (w / x) (α := α)
    have hA := kA_nonneg L η α
    have h1 : kA L η α / (1 + (w / x) ^ 2) ≤ kA L η α * x ^ 2 * (w ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have eqn : x ^ 2 * (w ^ 2)⁻¹ * (1 + (w / x) ^ 2) = x ^ 2 / w ^ 2 + 1 := by
        field_simp
      have : x ^ 2 * (w ^ 2)⁻¹ * (1 + (w / x) ^ 2) ≥ 1 := by
        rw [eqn]; have := div_nonneg (sq_nonneg x) hw2.le; linarith
      nlinarith [mul_le_mul_of_nonneg_left this hA]
    calc x⁻¹ * ‖Hr L η α (w / x)‖ ≤ x⁻¹ * (kA L η α * x ^ 2 * (w ^ 2)⁻¹) := by
          gcongr; exact hb.trans h1
      _ = x⁻¹ * kA L η α * x ^ 2 * (w ^ 2)⁻¹ := by ring
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc (by norm_num : (1 : ℝ) < 2) hφ hFφ 0
  have hf0 : ∀ n : ℤ, fourier n (((0 : ℝ)) : UnitAddCircle) = 1 := by
    intro n; rw [fourier_coe_apply]; simp
  simp only [hf0, mul_one] at hP
  have hP' : ∑' n : ℤ, φ n = ∑' n : ℤ, 𝓕 φ n := by
    rw [← hP]; congr 1; funext n; rw [zero_add]
  change ∑' n : ℤ, φ n = _
  rw [hP', show 𝓕 φ = fun w => ((x⁻¹ : ℝ) : ℂ) * Hr L η α (w / x) from funext (fourier_scaled hp hx)]
  rw [tsum_mul_left]

theorem summable_kh_nat (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => kh L η α ((n + 1) * x) := by
  refine summable_of_ne_finset_zero (s := Finset.range ⌈L / x⌉₊) fun n hn => ?_
  apply kh_vanish hp
  simp only [Finset.mem_range, not_lt] at hn
  have h1 : L / x ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : L < (n + 1) * x := by
    rw [div_le_iff₀ hx] at h1; nlinarith
  rw [abs_of_pos (by nlinarith [hp.big, hp.pos] : (0:ℝ) < (n + 1) * x)]; exact h2

theorem summable_inv_sq_succ : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine this.congr fun n => ?_
  push_cast; rw [inv_pow, one_div]

theorem summable_Hr_nat (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => Hr L η α ((n + 1) / x) := by
  refine Summable.of_norm_bounded (summable_inv_sq_succ.mul_left (kA L η α * x ^ 2)) fun n => ?_
  have hb := norm_Hr_le hp ((n + 1) / x) (α := α)
  have hA := kA_nonneg L η α
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine hb.trans ?_
  rw [div_le_iff₀ (by positivity), inv_pow]
  have eqn : kA L η α * x ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ * (1 + (((n : ℝ) + 1) / x) ^ 2)
      = kA L η α * (x ^ 2 / ((n : ℝ) + 1) ^ 2 + 1) := by field_simp
  rw [eqn]
  have := div_nonneg (sq_nonneg x) (sq_nonneg ((n : ℝ) + 1))
  nlinarith

/-- An even `ℤ`-sum is twice its positive half plus the centre. -/
theorem tsum_int_even (f : ℤ → ℂ) (heven : ∀ n, f (-n) = f n) (hs : Summable fun n : ℕ => f (n + 1)) :
    ∑' n : ℤ, f n = 2 * ∑' n : ℕ, f (n + 1) + f 0 := by
  have hs' : Summable fun n : ℕ => f (-(n + 1)) := hs.congr fun n => (heven _).symm
  rw [tsum_of_add_one_of_neg_add_one hs hs']
  have : (fun n : ℕ => f (-(n + 1))) = fun n : ℕ => f (n + 1) := funext fun n => heven _
  rw [this]; ring

theorem kh_int_cast (x : ℝ) (n : ℕ) : kh L η α (x * ((n : ℤ) + 1 : ℤ)) = kh L η α ((n + 1) * x) := by
  congr 1; push_cast; ring

theorem Hr_int_cast (x : ℝ) (n : ℕ) :
    Hr L η α (((n : ℤ) + 1 : ℤ) / x) = Hr L η α ((n + 1) * (1 / x)) := by
  congr 1; push_cast; ring

/-- **Connes' `E(h)(x) = E(H)(1/x)`**, when `∫ H = 0`. -/
theorem poisson_E (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {x : ℝ} (hx : 0 < x) :
    E (kh L η α) x = E (Hr L η α) (1 / x) := by
  have hP := poisson_scaled hp hx (α := α)
  have hk0 : kh L η α 0 = 0 := by rw [kh_zero, hint]
  have sk : Summable fun n : ℕ => kh L η α (x * ((n : ℤ) + 1 : ℤ)) :=
    (summable_kh_nat hp hx (α := α)).congr fun n => (kh_int_cast x n).symm
  have sH : Summable fun n : ℕ => Hr L η α (((n : ℤ) + 1 : ℤ) / x) :=
    (summable_Hr_nat hp hx (α := α)).congr fun n => by rw [Hr_int_cast]; congr 1; ring
  rw [tsum_int_even (fun n : ℤ => kh L η α (x * n)) (fun n => by
        simp only [Int.cast_neg, mul_neg]; exact kh_neg _) sk,
      tsum_int_even (fun n : ℤ => Hr L η α (n / x)) (fun n => by
        simp only [Int.cast_neg, neg_div]; exact Hr_neg _) sH] at hP
  simp only [Int.cast_zero, mul_zero, zero_div, hk0, Hr_zero, add_zero] at hP
  simp only [kh_int_cast, Hr_int_cast] at hP
  set S := ∑' n : ℕ, kh L η α ((n + 1) * x)
  set T := ∑' n : ℕ, Hr L η α ((n + 1) * (1 / x))
  have hST : S = ((x⁻¹ : ℝ) : ℂ) * T := by
    have h2 : (2 : ℂ) * S = 2 * (((x⁻¹ : ℝ) : ℂ) * T) := by rw [hP]; ring
    exact mul_left_cancel₀ two_ne_zero h2
  have hs : Real.sqrt x * x⁻¹ = Real.sqrt (1 / x) := by
    rw [Real.sqrt_div' 1 hx.le, Real.sqrt_one]
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    field_simp
    rw [Real.sq_sqrt hx.le]
  show (Real.sqrt x : ℂ) * S = (Real.sqrt (1 / x) : ℂ) * T
  rw [hST, ← mul_assoc, ← ofReal_mul, hs]

end Kaiser

#print axioms Kaiser.kh_vanish
#print axioms Kaiser.fourier_kh
#print axioms Kaiser.poisson_scaled
#print axioms Kaiser.poisson_E
