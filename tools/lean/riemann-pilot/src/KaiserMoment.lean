import Mathlib
import KaiserWindow

/-! # The moment condition of the Kaiser trial (round 163, part 10)

`∫ H = 0` forces `α = m₄/m₂` with `m_k = ∫ x^k K(x) sinc(πηx)^8`. We show `0 < m₂` and
`-m₂ ≤ m₄ ≤ (3/4) m₂`, by comparing `K` with the Gaussian `(E/2) e^{-b x²}` (`E = e^{βL}`,
`b = β/(2L)`) whose moments are exact by integration by parts: `G₄ = (3/(2b)) G₂`,
`G₂ = √(π/b)/(2b)`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

/-! ## Gaussian moments -/

theorem integrable_gpow {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ)) (by have := n.cast_nonneg (α := ℝ); linarith)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [Real.rpow_natCast]

theorem gauss_step {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∫ x : ℝ, x ^ (n + 2) * Real.exp (-b * x ^ 2) =
      (n + 1) / (2 * b) * ∫ x : ℝ, x ^ n * Real.exp (-b * x ^ 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x ^ (n + 1) * Real.exp (-b * x ^ 2))
      ((n + 1) * (x ^ n * Real.exp (-b * x ^ 2)) - 2 * b * (x ^ (n + 2) * Real.exp (-b * x ^ 2))) x := by
    intro x
    have h1 := hasDerivAt_pow (n + 1) x
    have h2 := ((hasDerivAt_pow 2 x).const_mul (-b)).exp
    convert h1.mul h2 using 1
    simp only [Nat.add_sub_cancel]; push_cast; ring
  have H := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (((integrable_gpow hb n).const_mul _).sub ((integrable_gpow hb (n + 2)).const_mul _))
    (integrable_gpow hb (n + 1))
  rw [integral_sub ((integrable_gpow hb n).const_mul _) ((integrable_gpow hb (n + 2)).const_mul _),
    integral_const_mul, integral_const_mul, sub_eq_zero] at H
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm, ← H]

theorem gauss_two {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = Real.sqrt (π / b) / (2 * b) := by
  have := gauss_step hb 0
  simp only [zero_add, pow_zero, one_mul, Nat.cast_zero, integral_gaussian] at this
  rw [this]; ring

theorem gauss_four {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 4 * Real.exp (-b * x ^ 2) = 3 / (2 * b) * ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) := by
  have := gauss_step hb 2; norm_num at this ⊢; rw [this]

/-! ## The real kernel -/

/-- `β = 2π(L − 4η)`. -/
def bt (L η : ℝ) : ℝ := 2 * π * (L - 4 * η)
/-- The Gaussian rate `b = β/(2L)`. -/
def gb (L η : ℝ) : ℝ := bt L η / (2 * L)
/-- The peak `E = e^{βL}`. -/
def kE (L η : ℝ) : ℝ := Real.exp (bt L η * L)
/-- The polynomial error scale `V = L⁶ + P`. -/
def kV (L η : ℝ) : ℝ := L ^ 6 + kP η
/-- The inner Gaussian loss on `|x| ≤ 2`. -/
def c1 (L η : ℝ) : ℝ := Real.exp (-(16 * gb L η / L ^ 2)) * (1 - (2 * π * η) ^ 2 / 6) ^ 8

/-- `K` on the real line. -/
def Kr (L η : ℝ) (x : ℝ) : ℝ := (kK (bt L η) L x).re
/-- `sinc(πηx)` on the real line. -/
def Sr (η : ℝ) (x : ℝ) : ℝ := (sincE ((π * η * x : ℝ) : ℂ)).re

variable {L η α : ℝ}

theorem Hr_eq (x : ℝ) : Hr L η α x = ((x ^ 2 * (x ^ 2 - α) * Kr L η x * Sr η x ^ 8 : ℝ) : ℂ) := by
  obtain ⟨r₁, h₁⟩ := kK_real_ex (2 * π * (L - 4 * η)) L x
  obtain ⟨r₂, h₂⟩ := sincE_real_ex (π * η * x)
  have e1 : Kr L η x = r₁ := by simp only [Kr, bt, h₁, ofReal_re]
  have e2 : Sr η x = r₂ := by simp only [Sr, h₂, ofReal_re]
  rw [e1, e2]; simp only [Hr, kH, h₁, cast_pey, h₂]; push_cast; ring_nf

theorem Kr_in {x : ℝ} (hx : x ^ 2 ≤ L ^ 2) :
    Kr L η x = Real.cosh (bt L η * Real.sqrt (L ^ 2 - x ^ 2)) := by
  simp only [Kr, kK_real_le hx, ofReal_re]

theorem abs_Kr_out {x : ℝ} (hx : L ^ 2 ≤ x ^ 2) : |Kr L η x| ≤ 1 := by
  simp only [Kr, kK_real_ge hx, ofReal_re]; exact Real.abs_cos_le_one _

theorem abs_Sr_le (x : ℝ) : |Sr η x| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_sincE_real_le_one _)

theorem abs_Sr_le_inv {x : ℝ} (hx : π * η * x ≠ 0) : |Sr η x| ≤ 1 / |π * η * x| :=
  (Complex.abs_re_le_norm _).trans (norm_sincE_real_le_inv hx)

theorem Sr_ge (x : ℝ) : 1 - (π * η * x) ^ 2 / 6 ≤ Sr η x := by
  set y := π * η * x
  have hS0 : Sr η x = (sincE (y : ℂ)).re := rfl
  rcases eq_or_ne y 0 with h | h
  · rw [hS0, h, ofReal_zero, sincE_zero, one_re]; norm_num
  · rw [hS0, sincE_real y h, ofReal_re]
    rcases lt_or_gt_of_ne h with hn | hpos
    · have := Real.sin_gt_sub_cube (neg_pos.2 hn)
      rw [Real.sin_neg] at this
      rw [le_div_iff_of_neg hn]; nlinarith
    · have := Real.sin_gt_sub_cube hpos
      rw [le_div_iff₀ hpos]; nlinarith

theorem Sr8_nonneg (x : ℝ) : 0 ≤ Sr η x ^ 8 := Even.pow_nonneg (by decide) _

theorem Sr8_le_one (x : ℝ) : Sr η x ^ 8 ≤ 1 := by
  rw [← Even.pow_abs (by decide)]; exact pow_le_one₀ (abs_nonneg _) (abs_Sr_le x)

theorem Sr8_le_inv (hη : 0 < η) {x : ℝ} (hx : x ≠ 0) : Sr η x ^ 8 ≤ kP η / x ^ 8 := by
  have hy : π * η * x ≠ 0 := by have := pi_pos; positivity
  rw [← Even.pow_abs (by decide)]
  refine (pow_le_pow_left₀ (abs_nonneg _) (abs_Sr_le_inv hy) 8).trans (le_of_eq ?_)
  have hxa : x ^ 8 = |x| ^ 8 := (Even.pow_abs (by decide) x).symm
  rw [kP, hxa, abs_mul, abs_of_pos (by have := pi_pos; positivity : 0 < π * η)]
  field_simp

/-! ## Square-root bounds -/

theorem sqrt_upper {x : ℝ} (hL : 0 < L) (hx : x ^ 2 ≤ L ^ 2) :
    Real.sqrt (L ^ 2 - x ^ 2) ≤ L - x ^ 2 / (2 * L) := by
  have h0 : 0 ≤ L - x ^ 2 / (2 * L) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have : (L - x ^ 2 / (2 * L)) ^ 2 = L ^ 2 - x ^ 2 + (x ^ 2 / (2 * L)) ^ 2 := by
    field_simp; ring
  rw [this]; nlinarith [sq_nonneg (x ^ 2 / (2 * L))]

theorem sqrt_lower {x : ℝ} (hL : 0 < L) (hx : x ^ 2 ≤ L ^ 2) :
    L - x ^ 2 / (2 * L) - x ^ 4 / (2 * L ^ 3) ≤ Real.sqrt (L ^ 2 - x ^ 2) := by
  have hq : L - x ^ 2 / (2 * L) - x ^ 4 / (2 * L ^ 3) = (L ^ 2 - x ^ 2) * (2 * L ^ 2 + x ^ 2) / (2 * L ^ 3) := by
    field_simp; ring
  rw [hq]
  have hu : 0 ≤ L ^ 2 - x ^ 2 := by linarith
  have hx2 := sq_nonneg x
  refine Real.le_sqrt_of_sq_le ?_
  rw [div_pow, div_le_iff₀ (by positivity)]
  have key : (L ^ 2 - x ^ 2) * (2 * L ^ 2 + x ^ 2) ^ 2 ≤ 4 * L ^ 6 := by
    nlinarith [mul_nonneg hx2 hx2, mul_nonneg (mul_nonneg hx2 hx2) hx2, sq_nonneg L]
  calc ((L ^ 2 - x ^ 2) * (2 * L ^ 2 + x ^ 2)) ^ 2
      = (L ^ 2 - x ^ 2) * ((L ^ 2 - x ^ 2) * (2 * L ^ 2 + x ^ 2) ^ 2) := by ring
    _ ≤ (L ^ 2 - x ^ 2) * (4 * L ^ 6) := mul_le_mul_of_nonneg_left key hu
    _ = _ := by ring

/-! ## Pointwise comparison with the Gaussian -/

theorem L_pos (hp : Par L η) : 0 < L := by linarith [hp.pos, hp.big]

theorem bt_nonneg (hp : Par L η) : 0 ≤ bt L η := by
  unfold bt; have := pi_pos; nlinarith [hp.big, hp.pos]

theorem gb_nonneg (hp : Par L η) : 0 ≤ gb L η := by
  unfold gb; have := bt_nonneg hp; have := L_pos hp; positivity

theorem Kr_upper (hp : Par L η) {x : ℝ} (hx : x ^ 2 ≤ L ^ 2) :
    Kr L η x ≤ (kE L η * Real.exp (-(gb L η * x ^ 2)) + 1) / 2 := by
  have hL := L_pos hp
  have hb := bt_nonneg hp
  rw [Kr_in hx, Real.cosh_eq]
  set t := bt L η * Real.sqrt (L ^ 2 - x ^ 2)
  have ht : 0 ≤ t := mul_nonneg hb (Real.sqrt_nonneg _)
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : Real.exp t ≤ kE L η * Real.exp (-(gb L η * x ^ 2)) := by
    rw [kE, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (sqrt_upper hL hx) hb
    have e : bt L η * (L - x ^ 2 / (2 * L)) = bt L η * L + -(gb L η * x ^ 2) := by
      unfold gb; field_simp; ring
    linarith
  linarith

theorem Kr_lower (hp : Par L η) {x : ℝ} (hx : x ^ 2 ≤ L ^ 2) :
    kE L η * Real.exp (-(gb L η * x ^ 2)) * Real.exp (-(gb L η * x ^ 4 / L ^ 2)) / 2 ≤ Kr L η x := by
  have hL := L_pos hp
  have hb := bt_nonneg hp
  rw [Kr_in hx, Real.cosh_eq]
  set t := bt L η * Real.sqrt (L ^ 2 - x ^ 2)
  have h2 : kE L η * Real.exp (-(gb L η * x ^ 2)) * Real.exp (-(gb L η * x ^ 4 / L ^ 2)) ≤ Real.exp t := by
    rw [kE, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (sqrt_lower hL hx) hb
    have e : bt L η * (L - x ^ 2 / (2 * L) - x ^ 4 / (2 * L ^ 3)) =
        bt L η * L + -(gb L η * x ^ 2) + -(gb L η * x ^ 4 / L ^ 2) := by
      unfold gb; field_simp; ring
    linarith
  have := (Real.exp_pos (-t)).le
  linarith

theorem Kr_nonneg {x : ℝ} (hx : x ^ 2 ≤ L ^ 2) : 0 ≤ Kr L η x := by
  rw [Kr_in hx]; exact (Real.cosh_pos _).le

theorem inv_le_of_one_le {x : ℝ} (hx : 1 ≤ x ^ 2) : 1 / x ^ 4 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h4 : 0 < x ^ 4 := by nlinarith
  rw [div_le_iff₀ h4, show 2 * (1 + x ^ 2)⁻¹ * x ^ 4 = 2 * x ^ 4 / (1 + x ^ 2) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith

theorem w4_tail (hp : Par L η) (hL1 : 1 ≤ L) {x : ℝ} (hx : L ^ 2 ≤ x ^ 2) :
    |x ^ 4 * Kr L η x * Sr η x ^ 8| ≤ 2 * kP η * (1 + x ^ 2)⁻¹ := by
  have hx1 : 1 ≤ x ^ 2 := by nlinarith
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
  have hP := (kP_pos hp.pos).le
  rw [abs_mul, abs_mul, abs_of_nonneg (Sr8_nonneg x), abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 4)]
  calc x ^ 4 * |Kr L η x| * Sr η x ^ 8 ≤ x ^ 4 * 1 * (kP η / x ^ 8) := by
        gcongr
        · exact abs_Kr_out hx
        · exact Sr8_le_inv hp.pos hx0
    _ = kP η * (1 / x ^ 4) := by field_simp
    _ ≤ kP η * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (inv_le_of_one_le hx1) hP
    _ = _ := by ring

theorem kV_ge (hp : Par L η) : kP η ≤ kV L η := by
  unfold kV; have := L_pos hp; nlinarith [pow_pos this 6]

theorem w4_upper (hp : Par L η) (hL1 : 1 ≤ L) (x : ℝ) :
    x ^ 4 * Kr L η x * Sr η x ^ 8 ≤
      kE L η / 2 * (x ^ 4 * Real.exp (-(gb L η * x ^ 2))) + 2 * kV L η * (1 + x ^ 2)⁻¹ := by
  have hE : 0 ≤ kE L η := (Real.exp_pos _).le
  have hV := kV_ge hp
  have hP := (kP_pos hp.pos).le
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hG : 0 ≤ x ^ 4 * Real.exp (-(gb L η * x ^ 2)) := by positivity
  rcases le_total (x ^ 2) (L ^ 2) with hx | hx
  · have hK := Kr_upper hp hx
    have hK0 := Kr_nonneg (η := η) hx
    have hS := Sr8_le_one (η := η) x
    have hS0 := Sr8_nonneg (η := η) x
    have hx4 : 0 ≤ x ^ 4 := by positivity
    have h1 : x ^ 4 * Kr L η x * Sr η x ^ 8 ≤ x ^ 4 * Kr L η x :=
      mul_le_of_le_one_right (mul_nonneg hx4 hK0) hS
    have h2 : x ^ 4 / 2 ≤ L ^ 6 * (1 + x ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have hx2 := sq_nonneg x
      have : x ^ 4 * (1 + x ^ 2) ≤ L ^ 4 * (1 + L ^ 2) := by
        have e1 : x ^ 4 = (x ^ 2) ^ 2 := by ring
        have e2 : L ^ 4 = (L ^ 2) ^ 2 := by ring
        rw [e1, e2]; gcongr
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL1 4]
    have h3 : L ^ 6 * (1 + x ^ 2)⁻¹ ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ hinv; unfold kV; nlinarith [pow_pos (L_pos hp) 6]
    calc _ ≤ x ^ 4 * Kr L η x := h1
      _ ≤ x ^ 4 * ((kE L η * Real.exp (-(gb L η * x ^ 2)) + 1) / 2) := mul_le_mul_of_nonneg_left hK hx4
      _ = kE L η / 2 * (x ^ 4 * Real.exp (-(gb L η * x ^ 2))) + x ^ 4 / 2 := by ring
      _ ≤ _ := by linarith
  · have := (le_abs_self _).trans (w4_tail hp hL1 hx)
    have : 2 * kP η * (1 + x ^ 2)⁻¹ ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hinv
    nlinarith [mul_nonneg hE hG]

theorem w4_lower (hp : Par L η) (hL1 : 1 ≤ L) (x : ℝ) :
    -(2 * kV L η * (1 + x ^ 2)⁻¹) ≤ x ^ 4 * Kr L η x * Sr η x ^ 8 := by
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hV := kV_ge hp
  have hP := (kP_pos hp.pos).le
  rcases le_total (x ^ 2) (L ^ 2) with hx | hx
  · have := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ x ^ 4) (Kr_nonneg (η := η) hx)) (Sr8_nonneg (η := η) x)
    have : 0 ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ := mul_nonneg (by linarith) hinv
    linarith
  · have := neg_abs_le (x ^ 4 * Kr L η x * Sr η x ^ 8)
    have := w4_tail hp hL1 hx
    have : 2 * kP η * (1 + x ^ 2)⁻¹ ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hinv
    linarith

theorem s0_bounds (hp : Par L η) : 0 ≤ 1 - (2 * π * η) ^ 2 / 6 ∧ 1 - (2 * π * η) ^ 2 / 6 ≤ 1 := by
  have h1 := hp.small; have h0 : 0 ≤ π * η := by have := pi_pos; have := hp.pos; positivity
  constructor <;> nlinarith

theorem c1_nonneg (hp : Par L η) : 0 ≤ c1 L η := by
  unfold c1; have := (s0_bounds hp).1; positivity

theorem c1_le_one (hp : Par L η) : c1 L η ≤ 1 := by
  unfold c1
  have hs := s0_bounds hp
  have h1 : Real.exp (-(16 * gb L η / L ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; have := gb_nonneg hp; positivity
  calc _ ≤ 1 * 1 := mul_le_mul h1 (pow_le_one₀ hs.1 hs.2) (pow_nonneg hs.1 8) zero_le_one
    _ = 1 := one_mul 1

theorem w2_lower (hp : Par L η) (hL2 : 2 ≤ L) (x : ℝ) :
    kE L η / 2 * (c1 L η * (x ^ 2 * Real.exp (-(gb L η * x ^ 2))) - x ^ 4 * Real.exp (-(gb L η * x ^ 2)) / 4)
      - 2 * kV L η * (1 + x ^ 2)⁻¹ ≤ x ^ 2 * Kr L η x * Sr η x ^ 8 := by
  have hE : 0 ≤ kE L η := (Real.exp_pos _).le
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hV := kV_ge hp
  have hP := (kP_pos hp.pos).le
  have hc0 := c1_nonneg hp
  have hc1 := c1_le_one hp
  have hL := L_pos hp
  have hx2 := sq_nonneg x
  set e := Real.exp (-(gb L η * x ^ 2))
  have he : 0 < e := Real.exp_pos _
  have hW : 0 ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ := mul_nonneg (by linarith) hinv
  -- the Gaussian part is `≤ 0` once `x² ≥ 4`
  have hneg : 4 ≤ x ^ 2 → kE L η / 2 * (c1 L η * (x ^ 2 * e) - x ^ 4 * e / 4) ≤ 0 := by
    intro h4
    have : c1 L η * (x ^ 2 * e) - x ^ 4 * e / 4 = x ^ 2 * e * (c1 L η - x ^ 2 / 4) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  rcases le_total (x ^ 2) 4 with h4 | h4
  · have hxL : x ^ 2 ≤ L ^ 2 := by nlinarith
    have hK := Kr_lower hp hxL
    have hq : gb L η * x ^ 4 / L ^ 2 ≤ 16 * gb L η / L ^ 2 := by
      have := gb_nonneg hp
      have hx4 : x ^ 4 ≤ 16 := by nlinarith
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have hK' : kE L η * e * Real.exp (-(16 * gb L η / L ^ 2)) / 2 ≤ Kr L η x := by
      refine le_trans ?_ hK
      gcongr
    have hs := s0_bounds hp
    have hS : 1 - (2 * π * η) ^ 2 / 6 ≤ Sr η x := by
      refine le_trans ?_ (Sr_ge x)
      have : (π * η * x) ^ 2 ≤ (2 * π * η) ^ 2 := by
        have : (π * η * x) ^ 2 = (π * η) ^ 2 * x ^ 2 := by ring
        rw [this]; nlinarith [sq_nonneg (π * η)]
      linarith
    have hS8 : (1 - (2 * π * η) ^ 2 / 6) ^ 8 ≤ Sr η x ^ 8 := pow_le_pow_left₀ hs.1 hS 8
    have hmain : kE L η / 2 * (c1 L η * (x ^ 2 * e)) ≤ x ^ 2 * Kr L η x * Sr η x ^ 8 := by
      have hA : 0 ≤ kE L η * e * Real.exp (-(16 * gb L η / L ^ 2)) / 2 := by positivity
      calc kE L η / 2 * (c1 L η * (x ^ 2 * e))
          = x ^ 2 * (kE L η * e * Real.exp (-(16 * gb L η / L ^ 2)) / 2) *
              (1 - (2 * π * η) ^ 2 / 6) ^ 8 := by unfold c1; ring
        _ ≤ x ^ 2 * Kr L η x * Sr η x ^ 8 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hK' hx2) hS8 (pow_nonneg hs.1 8)
            (mul_nonneg hx2 (hA.trans hK'))
    have : 0 ≤ kE L η / 2 * (x ^ 4 * e / 4) := by positivity
    nlinarith
  · rcases le_total (x ^ 2) (L ^ 2) with hx | hx
    · have := mul_nonneg (mul_nonneg hx2 (Kr_nonneg (η := η) hx)) (Sr8_nonneg (η := η) x)
      linarith [hneg h4]
    · have hx1 : 1 ≤ x ^ 2 := by linarith
      have h24 : |x ^ 2 * Kr L η x * Sr η x ^ 8| ≤ |x ^ 4 * Kr L η x * Sr η x ^ 8| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hx2, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 4)]
        have : x ^ 2 ≤ x ^ 4 := by nlinarith
        gcongr
      have := (w4_tail hp (by linarith) hx)
      have := neg_abs_le (x ^ 2 * Kr L η x * Sr η x ^ 8)
      have : 2 * kP η * (1 + x ^ 2)⁻¹ ≤ 2 * kV L η * (1 + x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hinv
      linarith [hneg h4]

/-! ## The moments -/

/-- `m_k = ∫ x^k K(x) sinc(πηx)^8`. -/
def mom (L η : ℝ) (k : ℕ) : ℝ := ∫ x : ℝ, x ^ k * Kr L η x * Sr η x ^ 8

theorem integrable_w4 (hp : Par L η) : Integrable fun x : ℝ => x ^ 4 * Kr L η x * Sr η x ^ 8 :=
  (integrable_Hr hp (α := 0)).re.congr (ae_of_all _ fun x => by
    simp only [RCLike.re_to_complex, Hr_eq, ofReal_re]; ring)

theorem integrable_w2 (hp : Par L η) : Integrable fun x : ℝ => x ^ 2 * Kr L η x * Sr η x ^ 8 :=
  ((integrable_w4 hp).sub (integrable_Hr hp (α := 1)).re).congr
    (ae_of_all _ fun x => by simp only [Pi.sub_apply, RCLike.re_to_complex, Hr_eq, ofReal_re]; ring)

theorem integral_Hr_eq (hp : Par L η) : ∫ x, Hr L η α x = ((mom L η 4 - α * mom L η 2 : ℝ) : ℂ) := by
  have h : (fun x => Hr L η α x) = fun x : ℝ =>
      ((x ^ 4 * Kr L η x * Sr η x ^ 8 - α * (x ^ 2 * Kr L η x * Sr η x ^ 8) : ℝ) : ℂ) := by
    funext x; rw [Hr_eq]; congr 1; ring
  rw [h, integral_complex_ofReal, integral_sub (integrable_w4 hp) ((integrable_w2 hp).const_mul _),
    integral_const_mul, mom, mom]

theorem integrable_gexp {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * Real.exp (-(b * x ^ 2)) := by
  simpa only [neg_mul] using integrable_gpow hb n

theorem integral_gexp4 {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 4 * Real.exp (-(b * x ^ 2)) = 3 / (2 * b) * ∫ x : ℝ, x ^ 2 * Real.exp (-(b * x ^ 2)) := by
  simpa only [neg_mul] using gauss_four hb

theorem integral_gexp2 {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-(b * x ^ 2)) = Real.sqrt (π / b) / (2 * b) := by
  simpa only [neg_mul] using gauss_two hb

theorem mom4_upper (hp : Par L η) (hL1 : 1 ≤ L) (hb : 0 < gb L η) :
    mom L η 4 ≤ kE L η / 2 * (∫ x : ℝ, x ^ 4 * Real.exp (-(gb L η * x ^ 2))) + 2 * kV L η * π := by
  have hi : Integrable fun x : ℝ =>
      kE L η / 2 * (x ^ 4 * Real.exp (-(gb L η * x ^ 2))) + 2 * kV L η * (1 + x ^ 2)⁻¹ :=
    ((integrable_gexp hb 4).const_mul (kE L η / 2)).add (integrable_inv_one_add_sq.const_mul (2 * kV L η))
  refine (integral_mono (integrable_w4 hp) hi (w4_upper hp hL1)).trans (le_of_eq ?_)
  rw [integral_add ((integrable_gexp hb 4).const_mul _) (integrable_inv_one_add_sq.const_mul _),
    integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq]

theorem mom4_lower (hp : Par L η) (hL1 : 1 ≤ L) : -(2 * kV L η * π) ≤ mom L η 4 := by
  have hi : Integrable fun x : ℝ => -(2 * kV L η * (1 + x ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.const_mul (2 * kV L η)).neg
  refine le_trans (le_of_eq ?_) (integral_mono hi (integrable_w4 hp) (w4_lower hp hL1))
  rw [integral_neg, integral_const_mul, integral_univ_inv_one_add_sq]

theorem mom2_lower (hp : Par L η) (hL2 : 2 ≤ L) (hb : 0 < gb L η) :
    kE L η / 2 * (c1 L η * (∫ x : ℝ, x ^ 2 * Real.exp (-(gb L η * x ^ 2))) -
      (∫ x : ℝ, x ^ 4 * Real.exp (-(gb L η * x ^ 2))) / 4) - 2 * kV L η * π ≤ mom L η 2 := by
  have i2 := integrable_gexp hb 2
  have i4 := integrable_gexp hb 4
  have hi : Integrable fun x : ℝ =>
      kE L η / 2 * (c1 L η * (x ^ 2 * Real.exp (-(gb L η * x ^ 2))) - x ^ 4 * Real.exp (-(gb L η * x ^ 2)) / 4)
        - 2 * kV L η * (1 + x ^ 2)⁻¹ :=
    (((i2.const_mul (c1 L η)).sub (i4.div_const 4)).const_mul (kE L η / 2)).sub
      (integrable_inv_one_add_sq.const_mul (2 * kV L η))
  have j1 : Integrable fun x : ℝ =>
      c1 L η * (x ^ 2 * Real.exp (-(gb L η * x ^ 2))) - x ^ 4 * Real.exp (-(gb L η * x ^ 2)) / 4 :=
    (i2.const_mul _).sub (i4.div_const 4)
  refine le_trans (le_of_eq ?_) (integral_mono hi (integrable_w2 hp) (w2_lower hp hL2))
  symm
  rw [integral_sub (j1.const_mul _) (integrable_inv_one_add_sq.const_mul _),
    integral_const_mul, integral_sub (i2.const_mul _) (i4.div_const 4), integral_const_mul,
    integral_div, integral_const_mul, integral_univ_inv_one_add_sq]

/-- **The moment window.** Under explicit numerical conditions on `(L, η)`,
`0 < m₂` and `-m₂ ≤ m₄ ≤ (3/4) m₂`. -/
theorem moment_bounds (hp : Par L η) (hL2 : 2 ≤ L) (hb3 : 3 ≤ gb L η) (hc : 9 / 10 ≤ c1 L η)
    (hAW : 22 * (2 * kV L η * π) ≤ kE L η / 2 * ∫ x : ℝ, x ^ 2 * Real.exp (-(gb L η * x ^ 2))) :
    0 < mom L η 2 ∧ mom L η 4 ≤ 3 / 4 * mom L η 2 ∧ -mom L η 2 ≤ mom L η 4 := by
  have hb : 0 < gb L η := by linarith
  have h4 := mom4_upper hp (by linarith) hb
  have h4l := mom4_lower hp (by linarith)
  have h2 := mom2_lower hp hL2 hb
  rw [integral_gexp4 hb] at h4 h2
  set G := ∫ x : ℝ, x ^ 2 * Real.exp (-(gb L η * x ^ 2))
  set W := 2 * kV L η * π
  have hW : 0 < W := by
    have := kV_ge hp; have := kP_pos hp.pos
    exact mul_pos (mul_pos two_pos (by linarith)) pi_pos
  set A := kE L η / 2 * G
  have hA : 0 ≤ A := by linarith
  have hκ : 3 / (2 * gb L η) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hκ0 : 0 ≤ 3 / (2 * gb L η) := by positivity
  have e4 : kE L η / 2 * (3 / (2 * gb L η) * G) = 3 / (2 * gb L η) * A := by ring
  have e2 : kE L η / 2 * (c1 L η * G - 3 / (2 * gb L η) * G / 4) = (c1 L η - 3 / (2 * gb L η) / 4) * A := by ring
  rw [e4] at h4; rw [e2] at h2
  have k1 : 3 / (2 * gb L η) * A ≤ 1 / 2 * A := mul_le_mul_of_nonneg_right hκ hA
  have k2 : (9 / 10 - 1 / 2 / 4) * A ≤ (c1 L η - 3 / (2 * gb L η) / 4) * A :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## The parameters `η = 1/L`, `L ≥ 50` -/

theorem par_inv (hL : 50 ≤ L) : Par L (1 / L) := by
  have hL0 : 0 < L := by linarith
  have := Real.pi_lt_d2
  refine ⟨by positivity, ?_, ?_⟩
  · rw [mul_one_div, div_le_one hL0]; linarith
  · rw [mul_one_div, div_le_iff₀ hL0]; nlinarith

theorem gb_inv (hL : 50 ≤ L) : gb L (1 / L) = π * (1 - 4 / L ^ 2) := by
  have hL0 : L ≠ 0 := by positivity
  unfold gb bt; field_simp

theorem gb_inv_bounds (hL : 50 ≤ L) : 3 ≤ gb L (1 / L) ∧ gb L (1 / L) ≤ π := by
  rw [gb_inv hL]
  have h1 : 4 / L ^ 2 ≤ 4 / 2500 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
  have h0 : 0 ≤ 4 / L ^ 2 := by positivity
  have := Real.pi_gt_d2; have := pi_pos
  constructor <;> nlinarith

theorem c1_inv (hL : 50 ≤ L) : 9 / 10 ≤ c1 L (1 / L) := by
  have hL0 : 0 < L := by linarith
  have hb := gb_inv_bounds hL
  have hpi := Real.pi_lt_d2
  have hpi0 := pi_pos
  unfold c1
  set y := 16 * gb L (1 / L) / L ^ 2
  have hy : y ≤ 1 / 40 := by
    have : 16 * gb L (1 / L) ≤ 16 * 3.15 := by linarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith [hb.1]) (by positivity)
  have he : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  set z := (2 * π * (1 / L)) ^ 2 / 6
  have hz : z ≤ 1 / 300 := by
    have e : z = 2 * π ^ 2 / (3 * L ^ 2) := by simp only [z]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]; nlinarith
  have hz0 : 0 ≤ z := by positivity
  have hs : 1 - 8 * z ≤ (1 - z) ^ 8 := by
    have := one_add_mul_le_pow (a := -z) (by linarith) 8
    simpa [sub_eq_add_neg, mul_neg] using this
  have hA : (0 : ℝ) ≤ 1 - y := by linarith
  have hB : (0 : ℝ) ≤ 1 - 8 * z := by linarith
  calc (9 : ℝ) / 10 ≤ (1 - y) * (1 - 8 * z) := by nlinarith
    _ ≤ Real.exp (-y) * (1 - z) ^ 8 := mul_le_mul he hs hB (Real.exp_pos _).le

theorem kV_inv_le (hL : 50 ≤ L) : kV L (1 / L) ≤ 2 * L ^ 8 := by
  have hL0 : 0 < L := by linarith
  unfold kV kP
  have hpi := Real.pi_gt_d2
  have e : 1 / (π * (1 / L)) = L / π := by field_simp
  rw [e, div_pow]
  have h1 : L ^ 8 / π ^ 8 ≤ L ^ 8 := div_le_self (by positivity) (one_le_pow₀ (by linarith))
  have h2 : L ^ 6 ≤ L ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem kE_inv_ge (hL : 50 ≤ L) : 3520 * L ^ 8 ≤ kE L (1 / L) := by
  have hL0 : 0 < L := by linarith
  have hpi := Real.pi_gt_d2
  have e : bt L (1 / L) * L = 2 * π * (L ^ 2 - 4) := by unfold bt; field_simp
  unfold kE; rw [e]
  have hL2 : 2500 ≤ L ^ 2 := by nlinarith
  have h6 : 6 * L ^ 2 ≤ 2 * π * (L ^ 2 - 4) := by
    have := mul_le_mul_of_nonneg_right hpi.le (by linarith : (0:ℝ) ≤ L ^ 2 - 4)
    linarith
  have hf := Real.pow_div_factorial_le_exp (x := 6 * L ^ 2) (by positivity) 5
  have h5 : (6 * L ^ 2) ^ 5 / (Nat.factorial 5 : ℝ) = 64.8 * L ^ 10 := by
    norm_num [Nat.factorial]; ring
  rw [h5] at hf
  have hL8 : 0 ≤ L ^ 8 := by positivity
  have : 3520 * L ^ 8 ≤ 64.8 * L ^ 10 := by
    have e10 : L ^ 10 = L ^ 2 * L ^ 8 := by ring
    rw [e10]; nlinarith [mul_le_mul_of_nonneg_right hL2 hL8]
  linarith [Real.exp_le_exp.2 h6]

theorem hAW_inv (hL : 50 ≤ L) :
    22 * (2 * kV L (1 / L) * π) ≤
      kE L (1 / L) / 2 * ∫ x : ℝ, x ^ 2 * Real.exp (-(gb L (1 / L) * x ^ 2)) := by
  have hb := gb_inv_bounds hL
  have hb0 : 0 < gb L (1 / L) := by linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := pi_pos
  rw [integral_gexp2 hb0]
  have hs : 1 ≤ Real.sqrt (π / gb L (1 / L)) := by
    rw [Real.one_le_sqrt, one_le_div hb0]; exact hb.2
  have hG : 1 / (2 * π) ≤ Real.sqrt (π / gb L (1 / L)) / (2 * gb L (1 / L)) := by
    calc 1 / (2 * π) ≤ 1 / (2 * gb L (1 / L)) := by gcongr; exact hb.2
      _ ≤ _ := by gcongr
  have hV := kV_inv_le hL
  have hE := kE_inv_ge hL
  have hE0 : 0 ≤ kE L (1 / L) := (Real.exp_pos _).le
  have hL8 : 0 ≤ L ^ 8 := by positivity
  calc 22 * (2 * kV L (1 / L) * π) ≤ 22 * (2 * (2 * L ^ 8) * π) := by gcongr
    _ ≤ kE L (1 / L) / 2 * (1 / (2 * π)) := by
        rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
        have : π * π ≤ 10 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hL8]
    _ ≤ _ := mul_le_mul_of_nonneg_left hG (by positivity)

/-- The balancing coefficient `α = m₄/m₂` at `η = 1/L`. -/
def kα (L : ℝ) : ℝ := mom L (1 / L) 4 / mom L (1 / L) 2

/-- **The moment condition.** For `L ≥ 50`, `α = m₄/m₂` gives `∫ H = 0`, with `|α| ≤ 1` and `α ≤ 3/4`. -/
theorem alpha_ok (hL : 50 ≤ L) :
    (∫ x, Hr L (1 / L) (kα L) x = 0) ∧ kα L ≤ 3 / 4 ∧ |kα L| ≤ 1 := by
  have hp := par_inv hL
  have hb := gb_inv_bounds hL
  obtain ⟨h0, h1, h2⟩ := moment_bounds hp (by linarith) hb.1 (c1_inv hL) (hAW_inv hL)
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_Hr_eq hp, kα, div_mul_cancel₀ _ h0.ne', sub_self, ofReal_zero]
  · rw [kα, div_le_iff₀ h0]; exact h1
  · rw [kα, abs_le, le_div_iff₀ h0, div_le_iff₀ h0]; constructor <;> linarith

end Kaiser

#print axioms Kaiser.alpha_ok
