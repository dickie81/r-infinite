import Mathlib
import KaiserZero

/-! # Derivatives of the Kaiser factors on the real line (round 163, part 6)

* `hasDerivAt_kc`: `kc′ = ks/2` (from `kc(s²) = cosh s`, `s·ks(s²) = sinh s`).
* `hasDerivAt_sincE`: `ζ·sincE′(ζ) = cos ζ − sincE ζ`.
* Real-line bounds: `|ks(−r²)| ≤ 1`, and `|sincE′(x)| ≤ 2/|x|` for `|x| ≥ 1`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

theorem hasDerivAt_kc_sq (s : ℂ) :
    HasDerivAt (fun s : ℂ => kc (s ^ 2)) (deriv kc (s ^ 2) * (2 * s)) s := by
  have h1 : HasDerivAt (fun s : ℂ => s ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  exact (differentiable_kc (s ^ 2)).hasDerivAt.comp s h1

/-- `kc′(w) = ks(w)/2` for `w ≠ 0`. -/
theorem deriv_kc {w : ℂ} (hw : w ≠ 0) : deriv kc w = ks w / 2 := by
  obtain ⟨s, rfl⟩ := exists_sq_eq w
  have hs : s ≠ 0 := by rintro rfl; simp at hw
  have hA := hasDerivAt_kc_sq s
  have hB : HasDerivAt (fun s : ℂ => kc (s ^ 2)) (Complex.sinh s) s := by
    have : (fun s : ℂ => kc (s ^ 2)) = Complex.cosh := funext kc_sq
    rw [this]; exact Complex.hasDerivAt_cosh s
  have := hA.unique hB
  rw [← ks_sq s] at this
  rw [eq_div_iff two_ne_zero]
  apply mul_left_cancel₀ hs
  linear_combination this

/-- `ks(−r²) = sin r / r` for real `r ≠ 0`, so `|ks(−r²)| ≤ 1`. -/
theorem norm_ks_neg_sq_le (r : ℝ) : ‖ks (-(r : ℂ) ^ 2)‖ ≤ 1 := by
  have h := norm_sincE_real_le_one r
  simpa [sincE] using h

/-- Derivative of `sincE`. -/
theorem hasDerivAt_sincE_mul (ζ : ℂ) :
    ζ * deriv sincE ζ + sincE ζ = Complex.cos ζ := by
  have hA : HasDerivAt (fun ζ : ℂ => ζ * sincE ζ) (1 * sincE ζ + ζ * deriv sincE ζ) ζ :=
    (hasDerivAt_id ζ).mul (differentiable_sincE ζ).hasDerivAt
  have hB : HasDerivAt (fun ζ : ℂ => ζ * sincE ζ) (Complex.cos ζ) ζ := by
    have : (fun ζ : ℂ => ζ * sincE ζ) = Complex.sin := funext mul_sincE
    rw [this]; exact Complex.hasDerivAt_sin ζ
  have := hA.unique hB
  linear_combination this

/-- On the real line, `|sincE′(x)| ≤ 2/|x|` for `x ≠ 0`. -/
theorem norm_deriv_sincE_real_le {x : ℝ} (hx : x ≠ 0) : ‖deriv sincE x‖ ≤ 2 / |x| := by
  have h := hasDerivAt_sincE_mul (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hd : deriv sincE x = (Complex.cos x - sincE x) / x := by
    rw [eq_div_iff hx']; linear_combination h
  rw [hd, norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_div_iff_of_pos_right (abs_pos.2 hx)]
  calc ‖Complex.cos ↑x - sincE ↑x‖ ≤ ‖Complex.cos ↑x‖ + ‖sincE ↑x‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one x
      · exact norm_sincE_real_le_one x
    _ = 2 := by norm_num


/-! ## The derivative of `H` -/

/-- The argument of `kc` inside `K`. -/
def kw (β L : ℝ) (z : ℂ) : ℂ := -(β : ℂ) ^ 2 * (z ^ 2 - (L : ℂ) ^ 2)

/-- Explicit derivative of `H = P·K·S`. -/
def kHd (L η α : ℝ) (z : ℂ) : ℂ :=
  let β := 2 * π * (L - 4 * η)
  (4 * z ^ 3 - 2 * α * z) * kK β L z * sincE (π * η * z) ^ 8
    + z ^ 2 * (z ^ 2 - α) * (deriv kc (kw β L z) * (-2 * (β : ℂ) ^ 2 * z)) * sincE (π * η * z) ^ 8
    + z ^ 2 * (z ^ 2 - α) * kK β L z *
        (8 * sincE (π * η * z) ^ 7 * (deriv sincE (π * η * z) * (π * η)))

theorem hasDerivAt_kH (L η α : ℝ) (z : ℂ) : HasDerivAt (kH L η α) (kHd L η α z) z := by
  set β := 2 * π * (L - 4 * η)
  have hP : HasDerivAt (fun z : ℂ => z ^ 2 * (z ^ 2 - α)) (4 * z ^ 3 - 2 * α * z) z := by
    have h1 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    have h2 : HasDerivAt (fun z : ℂ => z ^ 2 - α) (2 * z) z := h1.sub_const _
    convert h1.mul h2 using 1; ring
  have hw : HasDerivAt (kw β L) (-2 * (β : ℂ) ^ 2 * z) z := by
    unfold kw
    have h1 : HasDerivAt (fun z : ℂ => z ^ 2 - (L : ℂ) ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z).sub_const ((L : ℂ) ^ 2)
    convert h1.const_mul (-(β : ℂ) ^ 2) using 1; ring
  have hK : HasDerivAt (kK β L) (deriv kc (kw β L z) * (-2 * (β : ℂ) ^ 2 * z)) z :=
    (differentiable_kc _).hasDerivAt.comp z hw
  have hlin : HasDerivAt (fun z : ℂ => (π : ℂ) * η * z) ((π : ℂ) * η) z := by
    simpa using (hasDerivAt_id z).const_mul ((π : ℂ) * η)
  have hS1 : HasDerivAt (fun z : ℂ => sincE (π * η * z)) (deriv sincE (π * η * z) * (π * η)) z :=
    (differentiable_sincE _).hasDerivAt.comp z hlin
  have hS : HasDerivAt (fun z : ℂ => sincE (π * η * z) ^ 8)
      (8 * sincE (π * η * z) ^ 7 * (deriv sincE (π * η * z) * (π * η))) z := by
    convert hS1.pow 8 using 1
  have := (hP.mul hK).mul hS
  unfold kH kHd
  convert this using 1
  simp only [Pi.mul_apply, β]; ring

theorem continuous_kHd (L η α : ℝ) : Continuous (kHd L η α) := by
  have hkc : Continuous (deriv kc) :=
    (differentiable_kc.contDiff (n := 1)).continuous_deriv le_rfl
  have hsc : Continuous (deriv sincE) :=
    (differentiable_sincE.contDiff (n := 1)).continuous_deriv le_rfl
  have hK := (differentiable_kK (2 * π * (L - 4 * η)) L).continuous
  have hS := differentiable_sincE.continuous
  unfold kHd kw
  fun_prop

/-- On the real line beyond `L`, `|K′(y)| ≤ β² |y|`: `kc′(w) = ks(w)/2` with `|ks(w)| ≤ 1`. -/
theorem norm_Kd_real_ge {β L y : ℝ} (hy : L ^ 2 < y ^ 2) :
    ‖deriv kc (kw β L y) * (-2 * (β : ℂ) ^ 2 * y)‖ ≤ β ^ 2 * |y| := by
  set r := β * Real.sqrt (y ^ 2 - L ^ 2)
  have hr : (r : ℂ) ^ 2 = (β : ℂ) ^ 2 * ((y : ℂ) ^ 2 - (L : ℂ) ^ 2) := by
    have h := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ y ^ 2 - L ^ 2)
    have hc : ((Real.sqrt (y ^ 2 - L ^ 2) : ℝ) : ℂ) ^ 2 = (y : ℂ) ^ 2 - (L : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, h]; push_cast; ring
    simp only [r]; push_cast; rw [mul_pow, hc]
  have hwr : kw β L y = -(r : ℂ) ^ 2 := by rw [kw, hr]; ring
  by_cases hβ : β = 0
  · subst hβ; simp
  have hw0 : kw β L y ≠ 0 := by
    rw [hwr, neg_ne_zero, pow_ne_zero_iff two_ne_zero, Complex.ofReal_ne_zero]
    exact mul_ne_zero hβ (Real.sqrt_ne_zero'.2 (by linarith))
  rw [deriv_kc hw0, hwr, norm_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_pow]
  have h1 := norm_ks_neg_sq_le r
  simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have : ‖ks (-(r : ℂ) ^ 2)‖ / 2 * (2 * β ^ 2 * |y|) ≤ 1 / 2 * (2 * β ^ 2 * |y|) := by
    gcongr
  linarith


/-! ## Stronger decay, and the global derivative bound (Cauchy estimate) -/

theorem envelope2 {r q A : ℝ} (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) (hA : 0 ≤ A) :
    r ^ 2 * (r ^ 2 + A) * (1 + r ^ 2) ^ 2 ≤ (1 + A) * (1 / q) ^ 8 * (1 + q * r) ^ 8 := by
  have h1 : r ^ 2 * (r ^ 2 + A) ≤ (1 + A) * (1 + r ^ 2) ^ 2 := by
    nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have h2 : (1 + r ^ 2) ^ 4 ≤ (1 + r) ^ 8 := by
    have : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith
    calc (1 + r ^ 2) ^ 4 ≤ ((1 + r) ^ 2) ^ 4 := by gcongr
      _ = (1 + r) ^ 8 := by ring
  have h3 : 1 + r ≤ (1 / q) * (1 + q * r) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hq]; nlinarith
  have h4 : (1 + r) ^ 8 ≤ (1 / q) ^ 8 * (1 + q * r) ^ 8 := by rw [← mul_pow]; gcongr
  calc r ^ 2 * (r ^ 2 + A) * (1 + r ^ 2) ^ 2 ≤ (1 + A) * (1 + r ^ 2) ^ 2 * (1 + r ^ 2) ^ 2 := by gcongr
    _ = (1 + A) * (1 + r ^ 2) ^ 4 := by ring
    _ ≤ (1 + A) * ((1 / q) ^ 8 * (1 + q * r) ^ 8) := by gcongr; linarith
    _ = (1 + A) * (1 / q) ^ 8 * (1 + q * r) ^ 8 := by ring

def kA2 (L η α : ℝ) : ℝ := 6 ^ 8 * (1 + |α|) * (1 / (π * η)) ^ 8 * Real.exp (2 * π * (L - 4 * η) * L)

theorem kA2_nonneg (L η α : ℝ) : 0 ≤ kA2 L η α := by unfold kA2; positivity

/-- `‖H(z)‖ ≤ A₂ e^{2πL|Im z|}/(1 + (Re z)²)²`. -/
theorem norm_kH_le2 {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) (z : ℂ) :
    ‖kH L η α z‖ ≤ kA2 L η α * Real.exp (2 * π * L * |z.im|) / (1 + z.re ^ 2) ^ 2 := by
  set β := 2 * π * (L - 4 * η)
  set q := π * η
  have hq : 0 < q := by positivity
  have hβ : 0 ≤ β := by have := pi_pos; positivity
  have hL0 : 0 ≤ L := by linarith
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have hre : z.re ^ 2 ≤ r ^ 2 := by
    have := Complex.abs_re_le_norm z
    nlinarith [abs_nonneg z.re, sq_abs z.re]
  have hden : 0 < 1 + q * r := by positivity
  have hmain : ‖kH L η α z‖ ≤ r ^ 2 * (r ^ 2 + |α|) * Real.exp (β * (|z.im| + L)) *
      (6 * Real.exp (q * |z.im|) / (1 + q * r)) ^ 8 :=
    norm_kH_core hη hL z
  have hexp : Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8
      = Real.exp (β * L) * Real.exp (2 * π * L * |z.im|) :=
    kH_exp_eq L η |z.im|
  have henv := envelope2 hr hq hη1 (abs_nonneg α)
  have hre2 : (1 + z.re ^ 2) ^ 2 ≤ (1 + r ^ 2) ^ 2 := by gcongr
  rw [le_div_iff₀ (by positivity)]
  calc ‖kH L η α z‖ * (1 + z.re ^ 2) ^ 2
      ≤ r ^ 2 * (r ^ 2 + |α|) * Real.exp (β * (|z.im| + L)) *
          (6 * Real.exp (q * |z.im|) / (1 + q * r)) ^ 8 * (1 + r ^ 2) ^ 2 := by
        gcongr
    _ = 6 ^ 8 * (r ^ 2 * (r ^ 2 + |α|) * (1 + r ^ 2) ^ 2) / (1 + q * r) ^ 8 *
          (Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8) := by
        rw [div_pow, mul_pow]; field_simp
    _ ≤ 6 ^ 8 * ((1 + |α|) * (1 / q) ^ 8 * (1 + q * r) ^ 8) / (1 + q * r) ^ 8 *
          (Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8) := by
        gcongr
    _ = kA2 L η α * Real.exp (2 * π * L * |z.im|) := by
        rw [hexp, kA2]; simp only [β, q]; field_simp

/-- For `0 ≤ ρ ≤ 1`, `1 + (|y| − ρ)² ≥ (1 + y²)/8`. -/
theorem shift_sq_ge {y ρ : ℝ} (h1 : ρ ≤ 1) {x : ℝ} (hx : |x - y| ≤ ρ) :
    (1 + y ^ 2) / 8 ≤ 1 + x ^ 2 := by
  have := abs_le.1 hx
  rcases le_total 0 y with hy | hy
  · nlinarith [sq_nonneg (x - y), sq_nonneg (y - 1), sq_nonneg x]
  · nlinarith [sq_nonneg (x - y), sq_nonneg (y + 1), sq_nonneg x]

/-- **Global derivative bound** by the Cauchy estimate on the unit circle. -/
theorem norm_kHd_glob {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) (y : ℝ) :
    ‖kHd L η α y‖ ≤ 64 * kA2 L η α * Real.exp (2 * π * L) / (1 + y ^ 2) ^ 2 := by
  have hd : deriv (kH L η α) y = kHd L η α y := (hasDerivAt_kH L η α y).deriv
  rw [← hd]
  have hL0 : 0 ≤ L := by linarith
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos
    (differentiable_kH L η α).diffContOnCl fun z hz => ?_).trans (le_of_eq (div_one _))
  have hz' : ‖z - y‖ = 1 := by simpa [dist_eq_norm] using hz
  have him : |z.im| ≤ 1 := by
    have := Complex.abs_im_le_norm (z - y); simpa [hz'] using this
  have hre : |z.re - y| ≤ 1 := by
    have := Complex.abs_re_le_norm (z - y); simpa [hz'] using this
  have hs := shift_sq_ge (ρ := 1) le_rfl hre
  have hk := norm_kH_le2 hη hη1 hL z (α := α)
  have hA := kA2_nonneg L η α
  have he : Real.exp (2 * π * L * |z.im|) ≤ Real.exp (2 * π * L) := by
    apply Real.exp_le_exp.2; have := pi_pos; nlinarith [mul_le_mul_of_nonneg_left him (by positivity : (0:ℝ) ≤ 2 * π * L)]
  have hden : ((1 + (y : ℝ) ^ 2) / 8) ^ 2 ≤ (1 + z.re ^ 2) ^ 2 := by gcongr
  refine hk.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : kA2 L η α * Real.exp (2 * π * L * |z.im|) ≤ kA2 L η α * Real.exp (2 * π * L) := by gcongr
  nlinarith [mul_le_mul this hden (by positivity) (by positivity), Real.exp_pos (2 * π * L),
    mul_nonneg hA (Real.exp_pos (2 * π * L)).le]


/-! ## Sharp real-line bounds beyond `L` (polynomial in `L`) -/

theorem cast_pey (η y : ℝ) : ((π : ℂ) * η * y) = ((π * η * y : ℝ) : ℂ) := by push_cast; ring

theorem norm_S_real {η y : ℝ} (hx : π * η * y ≠ 0) :
    ‖sincE (π * η * y)‖ ≤ 1 / |π * η * y| := by
  rw [cast_pey]; exact norm_sincE_real_le_inv hx

/-- `|H(y)| ≤ 2 y⁴ |πηy|^{−8}` for `y² ≥ L²`, `y² ≥ 1`, `|α| ≤ 1`. -/
theorem norm_Hr_tail {L η α y : ℝ} (hα : |α| ≤ 1) (hy1 : 1 ≤ y ^ 2) (hyL : L ^ 2 ≤ y ^ 2)
    (hx : π * η * y ≠ 0) :
    ‖kH L η α y‖ ≤ 2 * y ^ 4 * (1 / |π * η * y|) ^ 8 := by
  unfold kH
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  have hK := norm_kK_real_ge (β := 2 * π * (L - 4 * η)) hyL
  have hS := norm_S_real hx
  have hP : ‖(y : ℂ) ^ 2 - α‖ ≤ 2 * y ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
    linarith
  have hy : ‖(y : ℂ)‖ ^ 2 = y ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hy]
  calc y ^ 2 * ‖(y : ℂ) ^ 2 - α‖ * ‖kK (2 * π * (L - 4 * η)) L y‖ * ‖sincE (π * η * y)‖ ^ 8
      ≤ y ^ 2 * (2 * y ^ 2) * 1 * (1 / |π * η * y|) ^ 8 := by gcongr
    _ = 2 * y ^ 4 * (1 / |π * η * y|) ^ 8 := by ring

/-- `|H′(y)| ≤ (6y³ + 2β²y⁵ + 32πη y⁴)|πηy|^{−8}` for `y² > L²`, `y ≥ 1`, `|α| ≤ 1`, `η > 0`. -/
theorem norm_kHd_tail {L η α y : ℝ} (hη : 0 < η) (hα : |α| ≤ 1) (hy1 : 1 ≤ y) (hyL : L ^ 2 < y ^ 2) :
    ‖kHd L η α y‖ ≤ (6 * y ^ 3 + 2 * (2 * π * (L - 4 * η)) ^ 2 * y ^ 5 + 32 * π * η * y ^ 4)
      * (1 / (π * η * y)) ^ 8 := by
  have hx0 : 0 < π * η * y := by have := pi_pos; positivity
  have hK := norm_kK_real_ge (β := 2 * π * (L - 4 * η)) (L := L) hyL.le
  have hKd := norm_Kd_real_ge (β := 2 * π * (L - 4 * η)) hyL
  have hyab : |y| = y := abs_of_pos (by linarith)
  rw [hyab] at hKd
  have hS := norm_S_real (η := η) (y := y) hx0.ne'
  rw [abs_of_pos hx0] at hS
  have hSd : ‖deriv sincE (π * η * y)‖ ≤ 2 / (π * η * y) := by
    rw [cast_pey]; have := norm_deriv_sincE_real_le hx0.ne'; rwa [abs_of_pos hx0] at this
  have hP : ‖(y : ℂ) ^ 2 * ((y : ℂ) ^ 2 - α)‖ ≤ 2 * y ^ 4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hyab]
    have : ‖(y : ℂ) ^ 2 - α‖ ≤ 2 * y ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hyab]
      nlinarith
    calc y ^ 2 * ‖(y : ℂ) ^ 2 - α‖ ≤ y ^ 2 * (2 * y ^ 2) := by gcongr
      _ = 2 * y ^ 4 := by ring
  have hP' : ‖4 * (y : ℂ) ^ 3 - 2 * α * y‖ ≤ 6 * y ^ 3 := by
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hyab, RCLike.norm_ofNat]
    nlinarith [abs_nonneg α, sq_nonneg y]
  have hpe : ‖((π : ℂ) * η)‖ = π * η := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold kHd
  simp only
  generalize kK (2 * π * (L - 4 * η)) L (y : ℂ) = K at hK ⊢
  generalize deriv kc (kw (2 * π * (L - 4 * η)) L y) * (-2 * ((2 * π * (L - 4 * η) : ℝ) : ℂ) ^ 2 * y) = Kd at hKd ⊢
  generalize sincE (π * η * y) = Sv at hS ⊢
  generalize deriv sincE (π * η * y) = Sd at hSd ⊢
  generalize (y : ℂ) ^ 2 * ((y : ℂ) ^ 2 - α) = P at hP ⊢
  generalize 4 * (y : ℂ) ^ 3 - 2 * α * y = P' at hP' ⊢
  set x := π * η * y
  have hS8 : ‖Sv‖ ^ 8 ≤ (1 / x) ^ 8 := by gcongr
  have hS7 : ‖Sv‖ ^ 7 ≤ (1 / x) ^ 7 := by gcongr
  have t1 : ‖P' * K * Sv ^ 8‖ ≤ 6 * y ^ 3 * (1 / x) ^ 8 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖P'‖ * ‖K‖ * ‖Sv‖ ^ 8 ≤ 6 * y ^ 3 * 1 * (1 / x) ^ 8 := by gcongr
      _ = _ := by ring
  have t2 : ‖P * Kd * Sv ^ 8‖ ≤ 2 * (2 * π * (L - 4 * η)) ^ 2 * y ^ 5 * (1 / x) ^ 8 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖P‖ * ‖Kd‖ * ‖Sv‖ ^ 8 ≤ 2 * y ^ 4 * ((2 * π * (L - 4 * η)) ^ 2 * y) * (1 / x) ^ 8 := by gcongr
      _ = _ := by ring
  have t3 : ‖P * K * (8 * Sv ^ 7 * (Sd * (π * η)))‖ ≤ 32 * π * η * y ^ 4 * (1 / x) ^ 8 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, hpe, RCLike.norm_ofNat]
    calc ‖P‖ * ‖K‖ * (8 * ‖Sv‖ ^ 7 * (‖Sd‖ * (π * η)))
        ≤ 2 * y ^ 4 * 1 * (8 * (1 / x) ^ 7 * (2 / x * (π * η))) := by gcongr
      _ = 32 * π * η * y ^ 4 * (1 / x) ^ 8 := by ring
  calc ‖P' * K * Sv ^ 8 + P * Kd * Sv ^ 8 + P * K * (8 * Sv ^ 7 * (Sd * (π * η)))‖
      ≤ ‖P' * K * Sv ^ 8‖ + ‖P * Kd * Sv ^ 8‖ + ‖P * K * (8 * Sv ^ 7 * (Sd * (π * η)))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [t1, t2, t3]

end Kaiser

#print axioms Kaiser.norm_Hr_tail
#print axioms Kaiser.norm_kHd_tail

#print axioms Kaiser.norm_kH_le2
#print axioms Kaiser.norm_kHd_glob

#print axioms Kaiser.hasDerivAt_kH
#print axioms Kaiser.norm_Kd_real_ge

#print axioms Kaiser.deriv_kc
#print axioms Kaiser.norm_deriv_sincE_real_le
