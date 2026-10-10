import Mathlib

/-! # Contour shifts on horizontal strips (round 156, part 1)

* **`strip_shift`.** If `f` is holomorphic on the closed strip `a ≤ Im t ≤ b` and
  `‖f t‖ ≤ C/(1 + (Re t)²)` there, then `∫_ℝ f(r + ia) dr = ∫_ℝ f(r + ib) dr`: Mathlib's Cauchy theorem
  on the rectangles `[−R, R] × [a, b]`, with the vertical sides `O(1/R²)`.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Real FourierTransform

noncomputable section

namespace PilotWeil

/-- The closed horizontal strip `a ≤ Im t ≤ b`. -/
def strip (a b : ℝ) : Set ℂ := {t | a ≤ t.im ∧ t.im ≤ b}

theorem integrable_line {f : ℂ → ℂ} {a b C : ℝ} (hd : DifferentiableOn ℂ f (strip a b))
    (hb : ∀ t ∈ strip a b, ‖f t‖ ≤ C / (1 + t.re ^ 2)) {y : ℝ} (hy : y ∈ Icc a b) :
    Integrable (fun r : ℝ => f (r + y * I)) := by
  have hmem : ∀ r : ℝ, ((r : ℂ) + y * I) ∈ strip a b := fun r => by
    show a ≤ ((r : ℂ) + y * I).im ∧ ((r : ℂ) + y * I).im ≤ b
    simpa using hy
  have hc : Continuous fun r : ℝ => f (r + y * I) :=
    hd.continuousOn.comp_continuous (by fun_prop) hmem
  refine ((integrable_inv_one_add_sq).const_mul C).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := hb _ (hmem r)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero] at this
  simpa [div_eq_mul_inv] using this

theorem integrable_om32 : Integrable fun x : ℝ => (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)
  simpa [Real.norm_eq_abs] using this

/-- **Contour shift across a strip**, for `‖f t‖ ≤ K(1 + |Re t|)^{−3/2}`. -/
theorem strip_shift' {f : ℂ → ℂ} {a b K : ℝ} (hab : a ≤ b) (hd : DifferentiableOn ℂ f (strip a b))
    (hb : ∀ t ∈ strip a b, ‖f t‖ ≤ K * (1 + |t.re|) ^ (-(3 / 2 : ℝ))) :
    ∫ r : ℝ, f (r + a * I) = ∫ r : ℝ, f (r + b * I) := by
  have hline : ∀ y ∈ Icc a b, Integrable (fun r : ℝ => f (r + y * I)) := by
    intro y hy
    have hmem : ∀ r : ℝ, ((r : ℂ) + y * I) ∈ strip a b := fun r => by
      show a ≤ ((r : ℂ) + y * I).im ∧ ((r : ℂ) + y * I).im ≤ b
      simpa using hy
    have hc : Continuous fun r : ℝ => f (r + y * I) :=
      hd.continuousOn.comp_continuous (by fun_prop) hmem
    refine (integrable_om32.const_mul K).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    have := hb _ (hmem r)
    simpa using this
  have Ia := hline a ⟨le_rfl, hab⟩
  have Ib := hline b ⟨hab, le_rfl⟩
  have hrect : ∀ R : ℝ, (∫ x in (-R)..R, f (x + a * I)) - (∫ x in (-R)..R, f (x + b * I))
      + I • (∫ y in a..b, f (R + y * I)) - I • (∫ y in a..b, f ((-R : ℝ) + y * I)) = 0 := by
    intro R
    have := integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-R, a⟩ ⟨R, b⟩ (hd.mono ?_)
    · simpa using this
    intro t ht
    rw [mem_reProdIm] at ht
    simp only at ht
    rw [uIcc_of_le hab] at ht
    exact ht.2
  have hvert : ∀ R : ℝ, ‖∫ y in a..b, f (R + y * I)‖ ≤ K * (1 + |R|) ^ (-(3 / 2 : ℝ)) * |b - a| :=
    fun R => intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => by
      rw [uIoc_of_le hab] at hy
      have := hb (R + y * I) (by simp [strip, hy.1.le, hy.2])
      simpa using this
  have hdecay : Tendsto (fun R : ℝ => K * (1 + |R|) ^ (-(3 / 2 : ℝ)) * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (1 + |R|) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun R : ℝ => 1 + |R|) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop.comp tendsto_id)
      exact (tendsto_rpow_neg_atTop (by norm_num)).comp h2
    simpa using (h1.const_mul K).mul_const |b - a|
  have hv1 : Tendsto (fun R : ℝ => ∫ y in a..b, f (R + y * I)) atTop (𝓝 0) :=
    squeeze_zero_norm hvert hdecay
  have hv2 : Tendsto (fun R : ℝ => ∫ y in a..b, f ((-R : ℝ) + y * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun R => by
      have := hvert (-R); rwa [abs_neg] at this) hdecay
  have hA := intervalIntegral_tendsto_integral Ia tendsto_neg_atTop_atBot tendsto_id
  have hB := intervalIntegral_tendsto_integral Ib tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hA.sub hB).add (hv1.const_smul I)).sub (hv2.const_smul I)
  rw [smul_zero, add_zero, sub_zero] at hlim
  have h0 : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop
      (𝓝 ((∫ r : ℝ, f (r + a * I)) - ∫ r : ℝ, f (r + b * I))) :=
    hlim.congr fun R => hrect R
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h0).symm

/-- **Contour shift across a strip**, for `‖f t‖ ≤ C/(1 + (Re t)²)`: `strip_shift'` with `K = 2C`
(round 335). -/
theorem strip_shift {f : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b) (hd : DifferentiableOn ℂ f (strip a b))
    (hb : ∀ t ∈ strip a b, ‖f t‖ ≤ C / (1 + t.re ^ 2)) :
    ∫ r : ℝ, f (r + a * I) = ∫ r : ℝ, f (r + b * I) := by
  have hC : 0 ≤ C := by
    have := hb (a * I) (by simp [strip, hab])
    have h1 : 0 < 1 + (a * I : ℂ).re ^ 2 := by positivity
    by_contra h; push Not at h
    have : C / (1 + (a * I : ℂ).re ^ 2) < 0 := div_neg_of_neg_of_pos h h1
    linarith [norm_nonneg (f (a * I))]
  refine strip_shift' (K := 2 * C) hab hd fun t ht => (hb t ht).trans ?_
  set x := t.re
  have hx1 : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h2 : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have hpow : (1 + |x|) ^ (-(2 : ℝ)) ≤ (1 + |x|) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have e2 : (1 + |x|) ^ (-(2 : ℝ)) = ((1 + |x|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  calc C / (1 + x ^ 2) ≤ C * (2 * ((1 + |x|) ^ 2)⁻¹) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [inv_le_comm₀ hpos (by positivity), mul_inv, inv_inv]
        nlinarith [inv_mul_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)]
    _ ≤ 2 * C * (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [← e2]; nlinarith [mul_le_mul_of_nonneg_left hpow hC]


theorem strip_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) : strip a' b' ⊆ strip a b :=
  fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩

/-! ## The test class and its Fourier kernel -/

/-- **The test class**: `h` holomorphic on the closed strip `|Im t| ≤ 1` with
`‖h t‖ ≤ C/(1 + (Re t)²)` there. -/
structure StripTest (h : ℂ → ℂ) (C : ℝ) : Prop where
  diff : DifferentiableOn ℂ h (strip (-1) 1)
  bound : ∀ t ∈ strip (-1) 1, ‖h t‖ ≤ C / (1 + t.re ^ 2)

/-- The Fourier kernel `F(x) = ∫_ℝ h(r)e^{−irx} dr`. -/
def FK (h : ℂ → ℂ) (x : ℝ) : ℂ := ∫ r : ℝ, h r * Complex.exp (-(I * r * x))

theorem norm_cexp_neg_I_mul (t : ℂ) (x : ℝ) : ‖Complex.exp (-(I * t * x))‖ = Real.exp (t.im * x) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

theorem StripTest.C_nonneg {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) : 0 ≤ C := by
  have := H.bound 0 (by simp [strip])
  have h1 : (0 : ℝ) < 1 + (0 : ℂ).re ^ 2 := by simp
  by_contra hC; push Not at hC
  linarith [norm_nonneg (h 0), div_neg_of_neg_of_pos hC h1]

/-- `h(t)e^{−itx}` is in the class, with constant `Ce^{|x|}`. -/
theorem StripTest.mul_exp {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (x : ℝ) :
    StripTest (fun t => h t * Complex.exp (-(I * t * x))) (C * Real.exp |x|) := by
  refine ⟨H.diff.mul (Differentiable.differentiableOn (by fun_prop)), fun t ht => ?_⟩
  rw [norm_mul, norm_cexp_neg_I_mul]
  have h1 : Real.exp (t.im * x) ≤ Real.exp |x| := Real.exp_le_exp.2 (by
    have := ht.1; have := ht.2
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; nlinarith
    · rw [abs_of_nonpos hx]; nlinarith)
  calc ‖h t‖ * Real.exp (t.im * x) ≤ C / (1 + t.re ^ 2) * Real.exp |x| :=
        mul_le_mul (H.bound t ht) h1 (Real.exp_pos _).le (div_nonneg H.C_nonneg (by positivity))
    _ = _ := by ring

/-- **The kernel on every line**: `∫_ℝ h(r + iy)e^{−i(r+iy)x} dr = F(x)` for `|y| ≤ 1`. -/
theorem line_eq {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (x : ℝ) :
    ∫ r : ℝ, h (r + y * I) * Complex.exp (-(I * (r + y * I) * x)) = FK h x := by
  have Hx := H.mul_exp x
  have e0 : FK h x = ∫ r : ℝ, (fun t => h t * Complex.exp (-(I * t * x))) (r + (0 : ℝ) * I) := by
    unfold FK; congr 1; funext r; simp
  rw [e0]
  rcases le_total y 0 with hy0 | hy0
  · exact strip_shift hy0 (Hx.diff.mono (strip_mono hy.1 (by norm_num)))
      (fun t ht => Hx.bound t (strip_mono hy.1 (by norm_num) ht))
  · exact (strip_shift hy0 (Hx.diff.mono (strip_mono (by norm_num) hy.2))
      (fun t ht => Hx.bound t (strip_mono (by norm_num) hy.2 ht))).symm

theorem line_bound {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (r : ℝ) :
    ‖h (r + y * I)‖ ≤ C / (1 + r ^ 2) := by
  have := H.bound (r + y * I) (by simpa [strip] using hy)
  simpa using this

/-- **`|F(x)| ≤ πCe^{−|x|}`**. -/
theorem norm_FK_le {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (x : ℝ) :
    ‖FK h x‖ ≤ π * C * Real.exp (-|x|) := by
  set y : ℝ := if 0 ≤ x then -1 else 1
  have hy : y ∈ Icc (-1 : ℝ) 1 := by simp only [y]; split_ifs <;> norm_num
  have hyx : y * x = -|x| := by
    simp only [y]; split_ifs with hx
    · rw [abs_of_nonneg hx]; ring
    · rw [abs_of_neg (not_le.1 hx)]; ring
  rw [← line_eq H hy x]
  have hb : ∀ r : ℝ, ‖h (r + y * I) * Complex.exp (-(I * (r + y * I) * x))‖
      ≤ C * Real.exp (-|x|) * (1 + r ^ 2)⁻¹ := fun r => by
    rw [norm_mul, norm_cexp_neg_I_mul]
    have e : ((r : ℂ) + y * I).im = y := by simp
    rw [e, hyx]
    calc ‖h (r + y * I)‖ * Real.exp (-|x|) ≤ C / (1 + r ^ 2) * Real.exp (-|x|) :=
          mul_le_mul_of_nonneg_right (line_bound H hy r) (Real.exp_pos _).le
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc _ ≤ ∫ r : ℝ, C * Real.exp (-|x|) * (1 + r ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le ((integrable_inv_one_add_sq).const_mul _)
          (Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring


theorem FK_even {h : ℂ → ℂ} (heven : ∀ t, h (-t) = h t) (x : ℝ) : FK h (-x) = FK h x := by
  unfold FK
  rw [← integral_neg_eq_self]
  congr 1; funext r
  push_cast
  rw [heven]; ring_nf

theorem exp_neg_abs_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Real.exp (-(c * |x|)) ≤ max 1 (2 / c ^ 2) * (1 + x ^ 2)⁻¹ := by
  set y := c * |x|
  have hy : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have hK : 1 + x ^ 2 ≤ max 1 (2 / c ^ 2) * Real.exp y := by
    have hx2 : x ^ 2 = y ^ 2 / c ^ 2 := by
      simp only [y]; rw [mul_pow, sq_abs]; field_simp
    have h1 : 1 + x ^ 2 ≤ max 1 (2 / c ^ 2) * (1 + y + y ^ 2 / 2) := by
      rw [hx2]
      have a1 := le_max_left 1 (2 / c ^ 2)
      have a2 := le_max_right 1 (2 / c ^ 2)
      have : y ^ 2 / c ^ 2 = 2 / c ^ 2 * (y ^ 2 / 2) := by ring
      rw [this]
      nlinarith [sq_nonneg y, div_nonneg (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 2)]
    exact h1.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (Real.exp y)⁻¹ * (1 + x ^ 2) ≤ (Real.exp y)⁻¹ * (max 1 (2 / c ^ 2) * Real.exp y) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by field_simp

theorem integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => Real.exp (-(c * |x|)) :=
  ((integrable_inv_one_add_sq).const_mul _).mono' (by fun_prop)
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_abs_le hc x)


/-- The Fourier transform of the line restriction `φ(r) = h(r + iy)`:
`𝓕φ(w) = e^{−2πyw} F(2πw)`. -/
theorem fourier_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1)
    (w : ℝ) :
    𝓕 (fun r : ℝ => h (r + y * I)) w = (Real.exp (-(y * (2 * π * w))) : ℂ) * FK h (2 * π * w) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← line_eq H hy (2 * π * w), ← integral_const_mul]
  congr 1; funext r
  rw [smul_eq_mul, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add,
    mul_comm (Complex.exp _) (h _)]
  congr 2; push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- **Complex Fourier inversion**: `h(τ) = (1/2π)∫_ℝ F(x)e^{iτx} dx` for `|Im τ| < 1`. -/
theorem inversion {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {τ : ℂ} (hτ : |τ.im| < 1) :
    h τ = 1 / (2 * π) * ∫ x : ℝ, FK h x * Complex.exp (I * τ * x) := by
  set y := τ.im
  have hy : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  set φ : ℝ → ℂ := fun r => h (r + y * I)
  have hmem : ∀ r : ℝ, ((r : ℂ) + y * I) ∈ strip (-1) 1 := fun r => by
    show -1 ≤ ((r : ℂ) + y * I).im ∧ ((r : ℂ) + y * I).im ≤ 1
    simpa using hy
  have hφc : Continuous φ := H.diff.continuousOn.comp_continuous (by fun_prop) hmem
  have hφi : Integrable φ := integrable_line H.diff H.bound hy
  have hF := fourier_line H hy
  -- integrability of `𝓕φ`
  set δ := 1 - |y|
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hFc : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφi
  have hFi : Integrable (𝓕 φ) := by
    refine ((integrable_exp_neg_abs (c := δ * (2 * π)) (by positivity)).const_mul (π * C)).mono'
      hFc.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb := norm_FK_le H (2 * π * w)
    have he : Real.exp (-(y * (2 * π * w))) * Real.exp (-|2 * π * w|)
        ≤ Real.exp (-(δ * (2 * π) * |w|)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have h1 := neg_abs_le (y * w)
      rw [abs_mul] at h1
      simp only [δ]
      nlinarith [Real.pi_pos, abs_nonneg w, abs_nonneg y]
    calc Real.exp (-(y * (2 * π * w))) * ‖FK h (2 * π * w)‖
        ≤ Real.exp (-(y * (2 * π * w))) * (π * C * Real.exp (-|2 * π * w|)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = π * C * (Real.exp (-(y * (2 * π * w))) * Real.exp (-|2 * π * w|)) := by ring
      _ ≤ π * C * Real.exp (-(δ * (2 * π) * |w|)) :=
          mul_le_mul_of_nonneg_left he (by have := H.C_nonneg; positivity)
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hφc hφi hFi) τ.re
  rw [Real.fourierInv_eq'] at hinv
  set G : ℝ → ℂ := fun x => FK h x * Complex.exp (I * τ * x)
  have hG : (fun v : ℝ => Complex.exp (↑(2 * π * inner ℝ v τ.re) * I) • 𝓕 φ v)
      = fun v => G (2 * π * v) := by
    funext v
    rw [hF, smul_eq_mul]
    simp only [G, RCLike.inner_apply, conj_trivial]
    rw [mul_comm (FK h _), ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    conv_rhs => rw [← Complex.re_add_im τ]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hG, Measure.integral_comp_mul_left G (2 * π)] at hinv
  have hτ' : h τ = φ τ.re := by
    simp only [φ, y]; rw [Complex.re_add_im]
  rw [hτ', ← hinv, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), Complex.real_smul]
  push_cast; ring


theorem continuous_FK {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) : Continuous (FK h) := by
  have hy : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hφi : Integrable (fun r : ℝ => h (r + (0 : ℝ) * I)) := integrable_line H.diff H.bound hy
  have hc : Continuous (𝓕 (fun r : ℝ => h (r + (0 : ℝ) * I))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφi
  have e : FK h = fun x => 𝓕 (fun r : ℝ => h (r + (0 : ℝ) * I)) (x / (2 * π)) := by
    funext x
    rw [fourier_line H hy]
    simp only [zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
    congr 1; field_simp
  rw [e]; exact hc.comp (continuous_id.div_const _)

theorem norm_FK_mul_exp_le {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (τ : ℂ) (x : ℝ) :
    ‖FK h x * Complex.exp (I * τ * x)‖ ≤ π * C * Real.exp (-((1 - |τ.im|) * |x|)) := by
  rw [norm_mul, Complex.norm_exp]
  have e : (I * τ * (x : ℂ)).re = -(τ.im * x) := by simp [Complex.mul_re]
  rw [e]
  calc ‖FK h x‖ * Real.exp (-(τ.im * x)) ≤ π * C * Real.exp (-|x|) * Real.exp (-(τ.im * x)) :=
        mul_le_mul_of_nonneg_right (norm_FK_le H x) (Real.exp_pos _).le
    _ = π * C * Real.exp (-|x| - τ.im * x) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by have := H.C_nonneg; positivity)
        apply Real.exp_le_exp.2
        have h1 := neg_abs_le (τ.im * x); rw [abs_mul] at h1
        nlinarith [abs_nonneg x]

theorem integrable_FK_mul_exp {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {τ : ℂ} (hτ : |τ.im| < 1) :
    Integrable fun x : ℝ => FK h x * Complex.exp (I * τ * x) :=
  ((integrable_exp_neg_abs (c := 1 - |τ.im|) (by linarith)).const_mul (π * C)).mono'
    ((continuous_FK H).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_FK_mul_exp_le H τ x)

/-- `1/w = i∫_0^∞ e^{−iwx} dx` for `Im w < 0`. -/
theorem inv_eq_integral {w : ℂ} (hw : w.im < 0) :
    1 / w = I * ∫ x in Ioi (0 : ℝ), Complex.exp (-(I * w * x)) := by
  have hre : (-(I * w)).re < 0 := by simp; linarith
  have := integral_exp_mul_complex_Ioi hre 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_mul] at this
  rw [this]
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hw; exact lt_irrefl _ hw
  field_simp

/-- **One pole**: `∫_ℝ h(r − i)/(r − i − c) dr = i∫_0^∞ e^{icx}F(x) dx` for `Im c > −1`. -/
theorem half_pole {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {c : ℂ} (hc : -1 < c.im) :
    ∫ r : ℝ, h (r - I) * (1 / ((r : ℂ) - I - c))
      = I * ∫ x in Ioi (0 : ℝ), Complex.exp (I * c * x) * FK h x := by
  have hmem : ∀ r : ℝ, ((r : ℂ) - I) ∈ strip (-1) 1 := fun r => by
    show -1 ≤ ((r : ℂ) - I).im ∧ ((r : ℂ) - I).im ≤ 1
    simp
  have hhc : Continuous fun r : ℝ => h (r - I) :=
    H.diff.continuousOn.comp_continuous (by fun_prop) hmem
  set G : ℝ → ℝ → ℂ := fun r x => h (r - I) * Complex.exp (-(I * ((r : ℂ) - I - c) * x))
  have hpt : ∀ r : ℝ, h (r - I) * (1 / ((r : ℂ) - I - c)) = I * ∫ x in Ioi (0 : ℝ), G r x := fun r => by
    rw [inv_eq_integral (by simp; linarith), integral_const_mul]
    ring
  have he : IntegrableOn (fun x : ℝ => Real.exp (-((1 + c.im) * x))) (Ioi 0) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 (by linarith : 0 < 1 + c.im)
  have hGi : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi 0))) := by
    have hb : Integrable (fun p : ℝ × ℝ => (C * (1 + p.1 ^ 2)⁻¹) * Real.exp (-((1 + c.im) * p.2)))
        (volume.prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod (f := fun r : ℝ => C * (1 + r ^ 2)⁻¹)
        (g := fun x : ℝ => Real.exp (-((1 + c.im) * x)))
        ((integrable_inv_one_add_sq).const_mul C) he
    refine hb.mono' ((hhc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable ?_
    have hm : volume.prod (volume.restrict (Ioi (0 : ℝ)))
        = ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hm]
    refine (ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)).2
      (Eventually.of_forall fun p hp => ?_)
    have hx : 0 < p.2 := hp.2
    show ‖h (p.1 - I) * Complex.exp (-(I * ((p.1 : ℂ) - I - c) * p.2))‖ ≤ _
    rw [norm_mul, norm_cexp_neg_I_mul]
    have e : ((p.1 : ℂ) - I - c).im = -1 - c.im := by simp
    rw [e]
    have hh := H.bound (p.1 - I) (hmem p.1)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero] at hh
    rw [div_eq_mul_inv] at hh
    calc ‖h (↑p.1 - I)‖ * Real.exp ((-1 - c.im) * p.2)
        ≤ C * (1 + p.1 ^ 2)⁻¹ * Real.exp ((-1 - c.im) * p.2) :=
          mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = _ := by ring_nf
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_integral_swap hGi]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  rw [← line_eq H hy x, ← integral_const_mul]
  congr 1; funext r
  simp only [G]
  push_cast
  rw [show (r : ℂ) + -1 * I = r - I by ring, mul_left_comm, ← Complex.exp_add]
  congr 2; ring

theorem integrable_half_pole {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {c : ℂ} (hc : -1 < c.im) :
    Integrable fun r : ℝ => h (r - I) * (1 / ((r : ℂ) - I - c)) := by
  have hmem : ∀ r : ℝ, ((r : ℂ) - I) ∈ strip (-1) 1 := fun r => by
    show -1 ≤ ((r : ℂ) - I).im ∧ ((r : ℂ) - I).im ≤ 1
    simp
  have hne : ∀ r : ℝ, (r : ℂ) - I - c ≠ 0 := fun r h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  have hhc : Continuous fun r : ℝ => h (r - I) :=
    H.diff.continuousOn.comp_continuous (by fun_prop) hmem
  set δ := 1 + c.im
  have hδ : 0 < δ := by simp only [δ]; linarith
  refine ((integrable_inv_one_add_sq).const_mul (C / δ)).mono'
    (hhc.mul (continuous_const.div (by fun_prop) hne)).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [norm_mul, norm_div, norm_one]
  have hh := H.bound (r - I) (hmem r)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero] at hh
  have hw : δ ≤ ‖(r : ℂ) - I - c‖ := by
    have := Complex.abs_im_le_norm ((r : ℂ) - I - c)
    have e : ((r : ℂ) - I - c).im = -1 - c.im := by simp
    rw [e, abs_of_neg (by linarith)] at this
    simp only [δ]; linarith
  calc ‖h (↑r - I)‖ * (1 / ‖(r : ℂ) - I - c‖) ≤ C / (1 + r ^ 2) * (1 / δ) :=
        mul_le_mul hh (one_div_le_one_div_of_le hδ hw) (by positivity)
          (div_nonneg H.C_nonneg (by positivity))
    _ = _ := by field_simp

theorem integrableOn_exp_FK {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {c : ℂ} (hc : |c.im| < 1) :
    IntegrableOn (fun x : ℝ => Complex.exp (I * c * x) * FK h x) (Ioi 0) :=
  ((integrable_FK_mul_exp H hc).congr (Eventually.of_forall fun _ => mul_comm _ _)).integrableOn

/-- **The pole pair**: for `|Im τ| < 1` and `h` even,
`∫_ℝ h(r − i)(1/(r − i − τ) + 1/(r − i + τ)) dr = 2πi h(τ)`. -/
theorem pole_pair {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) {τ : ℂ}
    (hτ : |τ.im| < 1) :
    ∫ r : ℝ, h (r - I) * (1 / ((r : ℂ) - I - τ) + 1 / ((r : ℂ) - I + τ)) = 2 * π * I * h τ := by
  have h1 : -1 < τ.im := by linarith [neg_abs_le τ.im]
  have h2 : -1 < (-τ).im := by simp; linarith [le_abs_self τ.im]
  have hτ' : |(-τ).im| < 1 := by simpa using hτ
  have e : ∀ r : ℝ, h (r - I) * (1 / ((r : ℂ) - I - τ) + 1 / ((r : ℂ) - I + τ))
      = h (r - I) * (1 / ((r : ℂ) - I - τ)) + h (r - I) * (1 / ((r : ℂ) - I - -τ)) := fun r => by
    rw [sub_neg_eq_add]; ring
  simp_rw [e]
  rw [integral_add (integrable_half_pole H h1) (integrable_half_pole H h2), half_pole H h1,
    half_pole H h2, ← mul_add, ← integral_add (integrableOn_exp_FK H hτ) (integrableOn_exp_FK H hτ')]
  -- `2π h(τ) = ∫_0^∞ (e^{iτx} + e^{−iτx})F(x) dx`
  have hinv := inversion H hτ
  have hsplit : ∫ x : ℝ, FK h x * Complex.exp (I * τ * x)
      = ∫ x in Ioi (0 : ℝ), (Complex.exp (I * τ * x) * FK h x + Complex.exp (I * -τ * x) * FK h x) := by
    have hi := integrable_FK_mul_exp H hτ
    rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn,
      integral_add (integrableOn_exp_FK H hτ) (integrableOn_exp_FK H hτ')]
    rw [add_comm]
    congr 1
    · congr 1; funext x; ring
    · have hn := integral_comp_neg_Ioi 0 (fun x : ℝ => FK h x * Complex.exp (I * τ * x))
      rw [neg_zero] at hn
      rw [← hn]
      congr 1; funext x
      rw [FK_even heven]; push_cast; ring_nf
  rw [← hsplit]
  rw [hinv]
  field_simp


/-! ## The per-zero bound: `∫|h(r − i)(1/(L − τ) + 1/(L + τ))| dr ≤ K(1 + |τ|)^{−7/4}` -/

/-- The weight `ω(x) = (1 + |x|)^{−5/4}`. -/
def om (x : ℝ) : ℝ := (1 + |x|) ^ (-(5 / 4 : ℝ))

theorem integrable_om : Integrable om := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by norm_num)
  show Integrable (fun x : ℝ => (1 + |x|) ^ (-(5 / 4 : ℝ)))
  simpa [Real.norm_eq_abs] using this

theorem om_nonneg (x : ℝ) : 0 ≤ om x := by unfold om; positivity

/-- `X^{−1/4}/a ≤ X^{−5/4} + a^{−5/4}` for `X, a > 0`. -/
theorem split_quarter {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    X ^ (-(1 / 4 : ℝ)) / a ≤ X ^ (-(5 / 4 : ℝ)) + a ^ (-(5 / 4 : ℝ)) := by
  have e1 : X ^ (-(5 / 4 : ℝ)) = X ^ (-(1 / 4 : ℝ)) / X := by
    rw [show -(5 / 4 : ℝ) = -(1 / 4) + -1 by norm_num, Real.rpow_add hX, Real.rpow_neg_one]
    ring
  have e2 : a ^ (-(5 / 4 : ℝ)) = a ^ (-(1 / 4 : ℝ)) / a := by
    rw [show -(5 / 4 : ℝ) = -(1 / 4) + -1 by norm_num, Real.rpow_add ha, Real.rpow_neg_one]
    ring
  rcases le_total X a with h | h
  · have : X ^ (-(1 / 4 : ℝ)) / a ≤ X ^ (-(1 / 4 : ℝ)) / X :=
      div_le_div_of_nonneg_left (by positivity) hX h
    rw [e1]; linarith [(by positivity : (0 : ℝ) ≤ a ^ (-(5 / 4 : ℝ)))]
  · have : X ^ (-(1 / 4 : ℝ)) ≤ a ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_nonpos ha h (by norm_num)
    have : X ^ (-(1 / 4 : ℝ)) / a ≤ a ^ (-(1 / 4 : ℝ)) / a := div_le_div_of_nonneg_right this ha.le
    rw [e2]; linarith [(by positivity : (0 : ℝ) ≤ X ^ (-(5 / 4 : ℝ)))]

/-- `a ≥ (1 + |x|)/4 ⇒ a^{−5/4} ≤ 8ω(x)`. -/
theorem rpow_le_om {a x : ℝ} (ha : (1 + |x|) / 4 ≤ a) : a ^ (-(5 / 4 : ℝ)) ≤ 8 * om x := by
  have h0 : 0 < (1 + |x|) / 4 := by positivity
  calc a ^ (-(5 / 4 : ℝ)) ≤ ((1 + |x|) / 4) ^ (-(5 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos h0 ha (by norm_num)
    _ = 4 ^ (5 / 4 : ℝ) * om x := by
        unfold om
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        field_simp
    _ ≤ 8 * om x := by
        apply mul_le_mul_of_nonneg_right _ (om_nonneg x)
        have : (4 : ℝ) ^ (5 / 4 : ℝ) ≤ 4 ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        have h8 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        linarith

theorem dist_line_ge {r : ℝ} {c : ℂ} (hc : |c.im| ≤ 1 / 2) :
    (1 + |r - c.re|) / 4 ≤ ‖(r : ℂ) - I - c‖ ∧ 1 / 2 ≤ ‖(r : ℂ) - I - c‖ := by
  have hre := Complex.abs_re_le_norm ((r : ℂ) - I - c)
  have him := Complex.abs_im_le_norm ((r : ℂ) - I - c)
  have e1 : ((r : ℂ) - I - c).re = r - c.re := by simp
  have e2 : ((r : ℂ) - I - c).im = -1 - c.im := by simp
  rw [e1] at hre; rw [e2] at him
  have hi : 1 / 2 ≤ |-1 - c.im| := by
    rw [abs_le] at hc
    rw [abs_of_neg (by linarith)]; linarith
  constructor
  · rcases le_total |r - c.re| (1 / 2) with h | h <;> nlinarith
  · linarith


theorem inv_sq_split {X : ℝ} (hX : 0 < X) :
    (X ^ 2)⁻¹ = X ^ (-(7 / 4 : ℝ)) * X ^ (-(1 / 4 : ℝ)) := by
  rw [← Real.rpow_add hX, show -(7 / 4 : ℝ) + -(1 / 4) = -2 by norm_num, Real.rpow_neg hX.le]
  norm_cast

theorem three_rpow_le : (3 : ℝ) ^ (7 / 4 : ℝ) ≤ 9 := by
  have : (3 : ℝ) ^ (7 / 4 : ℝ) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h9 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num
  linarith

theorem two_rpow_le : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 4 := by
  have : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  linarith

/-- **The pointwise bound** on the line `Im t = −1`, for `|Im τ| ≤ ½`. -/
theorem kernel_pointwise {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {τ : ℂ} (hτ : |τ.im| ≤ 1 / 2)
    (r : ℝ) :
    ‖h (r - I) * (1 / ((r : ℂ) - I - τ) + 1 / ((r : ℂ) - I + τ))‖
      ≤ 200 * C * (1 + ‖τ‖) ^ (-(7 / 4 : ℝ)) * (om r + om (r - τ.re) + om (r + τ.re)) := by
  have hC := H.C_nonneg
  set X := 1 + |r|
  set T := ‖τ‖
  set L : ℂ := (r : ℂ) - I
  have hX : 0 < X := by positivity
  have hX1 : 1 ≤ X := by simp only [X]; linarith [abs_nonneg r]
  have hT : 0 ≤ T := norm_nonneg _
  -- the test function
  have hh : ‖h L‖ ≤ 2 * C * (X ^ 2)⁻¹ := by
    have := H.bound L (by show -1 ≤ L.im ∧ L.im ≤ 1; simp [L])
    have e : L.re = r := by simp [L]
    rw [e] at this
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hsq : X ^ 2 ≤ 2 * (1 + r ^ 2) := by
      simp only [X]; nlinarith [sq_abs r, abs_nonneg r, sq_nonneg (|r| - 1)]
    calc C = 2 * C * (X ^ 2)⁻¹ * (X ^ 2 / 2) := by field_simp
      _ ≤ 2 * C * (X ^ 2)⁻¹ * (1 + r ^ 2) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- distances
  obtain ⟨da, da'⟩ := dist_line_ge (r := r) hτ
  obtain ⟨db, db'⟩ := dist_line_ge (r := r) (c := -τ) (by simpa using hτ)
  simp only [Complex.neg_re, sub_neg_eq_add] at db db'
  set a := ‖L - τ‖
  set b := ‖L + τ‖
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hLX : ‖L‖ ≤ X := by
    calc ‖L‖ ≤ ‖(r : ℂ)‖ + ‖I‖ := norm_sub_le _ _
      _ = X := by simp [X, Complex.norm_real]; ring
  have hne1 : L - τ ≠ 0 := norm_pos_iff.1 ha
  have hne2 : L + τ ≠ 0 := norm_pos_iff.1 hb
  have hk1 : ‖1 / (L - τ) + 1 / (L + τ)‖ ≤ 1 / a + 1 / b := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_one]
  have hom : 0 ≤ om r + om (r - τ.re) + om (r + τ.re) := by
    linarith [om_nonneg r, om_nonneg (r - τ.re), om_nonneg (r + τ.re)]
  have hTpow : 0 ≤ (1 + T) ^ (-(7 / 4 : ℝ)) := by positivity
  rw [norm_mul]
  show ‖h L‖ * ‖1 / (L - τ) + 1 / (L + τ)‖ ≤ _
  rcases le_or_gt X (T / 2) with hcase | hcase
  · -- far from the zeros' heights: both distances `≥ T/2`
    have hT2 : 2 ≤ T := by linarith
    have ha2 : T / 2 ≤ a := by
      have h1 := norm_sub_norm_le τ L
      have e : ‖τ - L‖ = a := norm_sub_rev τ L
      rw [e] at h1; linarith
    have hb2 : T / 2 ≤ b := by
      have h1 := norm_sub_norm_le τ (-L)
      have e : ‖τ - -L‖ = b := by rw [sub_neg_eq_add, add_comm τ L]
      rw [e, norm_neg] at h1; linarith
    have hk : ‖1 / (L - τ) + 1 / (L + τ)‖ ≤ 8 * X / T ^ 2 := by
      have e : 1 / (L - τ) + 1 / (L + τ) = 2 * L / ((L - τ) * (L + τ)) := by
        field_simp; ring
      rw [e, norm_div, norm_mul, norm_mul, Complex.norm_two, div_le_div_iff₀ (by positivity)
        (by positivity)]
      have hab : T / 2 * (T / 2) ≤ a * b := mul_le_mul ha2 hb2 (by positivity) ha.le
      nlinarith [norm_nonneg L]
    have hX14 : X ^ (1 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hX.le (by linarith) (by norm_num)
    have hP : (1 + T) ^ (7 / 4 : ℝ) ≤ 4 * T ^ (7 / 4 : ℝ) := by
      calc (1 + T) ^ (7 / 4 : ℝ) ≤ (2 * T) ^ (7 / 4 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ = 2 ^ (7 / 4 : ℝ) * T ^ (7 / 4 : ℝ) := Real.mul_rpow (by norm_num) hT
        _ ≤ 4 * T ^ (7 / 4 : ℝ) := mul_le_mul_of_nonneg_right two_rpow_le (by positivity)
    have hTT : T ^ (7 / 4 : ℝ) * T ^ (1 / 4 : ℝ) = T ^ 2 := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have hom_r : om r = (X * X ^ (1 / 4 : ℝ))⁻¹ := by
      unfold om
      rw [show -(5 / 4 : ℝ) = -(1 + 1 / 4) by norm_num, Real.rpow_neg hX.le,
        Real.rpow_add hX, Real.rpow_one]
    have hTm : (1 + T) ^ (-(7 / 4 : ℝ)) = ((1 + T) ^ (7 / 4 : ℝ))⁻¹ := Real.rpow_neg (by positivity) _
    have hpos1 : 0 < (1 + T) ^ (7 / 4 : ℝ) := by positivity
    have hpos2 : 0 < X ^ (1 / 4 : ℝ) := by positivity
    calc ‖h L‖ * ‖1 / (L - τ) + 1 / (L + τ)‖ ≤ 2 * C * (X ^ 2)⁻¹ * (8 * X / T ^ 2) :=
          mul_le_mul hh hk (norm_nonneg _) (by positivity)
      _ = 16 * C / (X * T ^ 2) := by field_simp; ring
      _ ≤ 200 * C * (1 + T) ^ (-(7 / 4 : ℝ)) * om r := by
          rw [hom_r, hTm]
          rw [div_le_iff₀ (by positivity)]
          have key : (1 + T) ^ (7 / 4 : ℝ) * X ^ (1 / 4 : ℝ) ≤ 4 * T ^ 2 := by
            calc (1 + T) ^ (7 / 4 : ℝ) * X ^ (1 / 4 : ℝ) ≤ (4 * T ^ (7 / 4 : ℝ)) * T ^ (1 / 4 : ℝ) :=
                  mul_le_mul hP hX14 hpos2.le (by positivity)
              _ = 4 * T ^ 2 := by rw [mul_assoc, hTT]
          have e2 : 200 * C * ((1 + T) ^ (7 / 4 : ℝ))⁻¹ * (X * X ^ (1 / 4 : ℝ))⁻¹ * (X * T ^ 2)
              = 200 * C * T ^ 2 / ((1 + T) ^ (7 / 4 : ℝ) * X ^ (1 / 4 : ℝ)) := by
            field_simp
          rw [e2, le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 16 * C)]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [om_nonneg (r - τ.re), om_nonneg (r + τ.re)]
  · -- near the zeros' heights: `X ≥ (1 + T)/3`
    have hX3 : (1 + T) / 3 ≤ X := by
      rcases le_total T 2 with hT2 | hT2
      · linarith
      · linarith
    have hX74 : X ^ (-(7 / 4 : ℝ)) ≤ 9 * (1 + T) ^ (-(7 / 4 : ℝ)) := by
      calc X ^ (-(7 / 4 : ℝ)) ≤ ((1 + T) / 3) ^ (-(7 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hX3 (by norm_num)
        _ = 3 ^ (7 / 4 : ℝ) * (1 + T) ^ (-(7 / 4 : ℝ)) := by
            rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
            field_simp
        _ ≤ 9 * (1 + T) ^ (-(7 / 4 : ℝ)) := mul_le_mul_of_nonneg_right three_rpow_le hTpow
    have hsa := split_quarter hX ha
    have hsb := split_quarter hX hb
    have hoa := rpow_le_om da
    have hob := rpow_le_om db
    have hom_r : X ^ (-(5 / 4 : ℝ)) = om r := rfl
    calc ‖h L‖ * ‖1 / (L - τ) + 1 / (L + τ)‖ ≤ 2 * C * (X ^ 2)⁻¹ * (1 / a + 1 / b) :=
          mul_le_mul hh hk1 (norm_nonneg _) (by positivity)
      _ = 2 * C * X ^ (-(7 / 4 : ℝ)) * (X ^ (-(1 / 4 : ℝ)) / a + X ^ (-(1 / 4 : ℝ)) / b) := by
          rw [inv_sq_split hX]; ring
      _ ≤ 2 * C * (9 * (1 + T) ^ (-(7 / 4 : ℝ))) * (2 * om r + 8 * om (r - τ.re) + 8 * om (r + τ.re)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hX74 (by positivity)) _ (by positivity)
            (by positivity)
          rw [← hom_r]; linarith
      _ ≤ _ := by
          have := om_nonneg r
          have h3 : 2 * om r + 8 * om (r - τ.re) + 8 * om (r + τ.re)
              ≤ 8 * (om r + om (r - τ.re) + om (r + τ.re)) := by linarith
          calc 2 * C * (9 * (1 + T) ^ (-(7 / 4 : ℝ))) * (2 * om r + 8 * om (r - τ.re) + 8 * om (r + τ.re))
              ≤ 2 * C * (9 * (1 + T) ^ (-(7 / 4 : ℝ))) * (8 * (om r + om (r - τ.re) + om (r + τ.re))) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 144 * C * (1 + T) ^ (-(7 / 4 : ℝ)) * (om r + om (r - τ.re) + om (r + τ.re)) := by ring
            _ ≤ _ := by
                apply mul_le_mul_of_nonneg_right _ hom
                apply mul_le_mul_of_nonneg_right _ hTpow
                linarith


theorem integrable_kernel {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {τ : ℂ} (hτ : |τ.im| < 1) :
    Integrable fun r : ℝ => h (r - I) * (1 / ((r : ℂ) - I - τ) + 1 / ((r : ℂ) - I + τ)) := by
  have h1 : -1 < τ.im := by linarith [neg_abs_le τ.im]
  have h2 : -1 < (-τ).im := by simp; linarith [le_abs_self τ.im]
  refine ((integrable_half_pole H h1).add (integrable_half_pole H h2)).congr
    (Eventually.of_forall fun r => ?_)
  show h (r - I) * (1 / ((r : ℂ) - I - τ)) + h (r - I) * (1 / ((r : ℂ) - I - -τ)) = _
  rw [sub_neg_eq_add]; ring

/-- **The per-zero bound**: `∫|h(r − i)(1/(L − τ) + 1/(L + τ))| dr ≤ 600C(∫ω)(1 + |τ|)^{−7/4}`. -/
theorem kernel_integral_le {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {τ : ℂ} (hτ : |τ.im| ≤ 1 / 2) :
    ∫ r : ℝ, ‖h (r - I) * (1 / ((r : ℂ) - I - τ) + 1 / ((r : ℂ) - I + τ))‖
      ≤ 600 * C * (∫ x, om x) * (1 + ‖τ‖) ^ (-(7 / 4 : ℝ)) := by
  have hi := (integrable_kernel H (by linarith : |τ.im| < 1)).norm
  have hw : Integrable fun r : ℝ => om r + om (r - τ.re) + om (r + τ.re) :=
    (integrable_om.add (integrable_om.comp_sub_right τ.re)).add (integrable_om.comp_add_right τ.re)
  refine (integral_mono hi (hw.const_mul (200 * C * (1 + ‖τ‖) ^ (-(7 / 4 : ℝ))))
    fun r => kernel_pointwise H hτ r).trans_eq ?_
  have hA : Integrable fun r : ℝ => om r + om (r - τ.re) :=
    integrable_om.add (integrable_om.comp_sub_right τ.re)
  have e1 : ∫ r : ℝ, (om r + om (r - τ.re) + om (r + τ.re))
      = (∫ r : ℝ, (om r + om (r - τ.re))) + ∫ r : ℝ, om (r + τ.re) :=
    integral_add hA (integrable_om.comp_add_right τ.re)
  have e2 : ∫ r : ℝ, (om r + om (r - τ.re)) = (∫ r : ℝ, om r) + ∫ r : ℝ, om (r - τ.re) :=
    integral_add integrable_om (integrable_om.comp_sub_right τ.re)
  have e3 : ∫ r : ℝ, om (r - τ.re) = ∫ r : ℝ, om r := integral_sub_right_eq_self om τ.re
  have e4 : ∫ r : ℝ, om (r + τ.re) = ∫ r : ℝ, om r := integral_add_right_eq_self om τ.re
  rw [integral_const_mul, e1, e2, e3, e4]
  ring


end PilotWeil

#print axioms PilotWeil.strip_shift
#print axioms PilotWeil.inversion
#print axioms PilotWeil.pole_pair
#print axioms PilotWeil.strip_shift'
#print axioms PilotWeil.kernel_integral_le
