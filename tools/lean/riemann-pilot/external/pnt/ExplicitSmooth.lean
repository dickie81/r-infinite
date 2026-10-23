/-
# Round 484: an explicit smoothing and its Mellin constants

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. `ν₀(x) = c₀·max(0, (x − 1/2)(2 − x))²` with `c₀ = 1/(2 log 2 − 75/64)` is `C¹`, nonnegative,
supported in `[1/2, 2]`, and has `∫_0^∞ ν₀(x)/x dx = 1` (`contDiff_ν₀`, `ν₀_nonneg`, `support_ν₀`, `mass_ν₀`): the
properties that `SmoothPerron`, `ChiPNT` and `ChiUniform` ask of a smoothing, for which PNT+'s `SmoothExistence`
gives a smooth `ν` with no formula. Since `|ν₀| ≤ 2` and `|ν₀′| ≤ 9`, `|𝓜(Smooth1 ν₀ ε)(s)| ≤ 25/|s|` and
`≤ 54/(ε|s|²)`, and on a line `Re s = σ ∈ (0, 1]`,
`|𝓜(Smooth1 ν₀ ε)(σ + it)| ≤ 25^{1−κ}54^κ(σ/2)^{−1−κ}ε^{−κ}(1 + |t|)^{−1−κ}` for `κ ∈ [0, 1]`
(`mellin_ν₀_le_geom`).

* `hasDerivAt_bump`, `contDiff_bump`: `g = max(0, h)²` with `h(x) = (x − 1/2)(2 − x)` has the continuous
  derivative `2 max(0, h)h′`; at a zero `x` of `h`, `0 ≤ g(y) ≤ h(y)² = o(y − x)`.
* `integral_bump_div`: `∫_{1/2}^{2} h(x)²/x dx = 2 log 2 − 75/64`, which is at least `1/5`, so `c₀ ≤ 5`.
* `norm_mellin_le_of_deriv`, `norm_mellin_le_of_norm`: PNT+'s `MellinOfPsi` and round 338's
  `MediumPNTW.MellinOfPsi_bdd` with their constants: `|𝓜ν(s)| ≤ 6S₁/|s|` if `|ν′| ≤ S₁`, and
  `|𝓜ν(w)| ≤ 12S₀ + 1` if `|ν| ≤ S₀`, on `0 < Re s ≤ 2` and `0 ≤ Re w ≤ 2`.
* `norm_mellin_smooth1_le_d`, `norm_mellin_smooth1_le_b`: the same for `Smooth1 ν ε`, through PNT+'s
  `MellinOfSmooth1a`, `𝓜(Smooth1 ν ε)(s) = 𝓜ν(εs)/s`.
* `mellin_ν₀_le_geom`: `SmoothPerron.mellin_le_geom_of` with `B = 25` and `C = 54`.
-/
import SmoothPerron

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform6) "𝓜" => mellin

namespace ExplicitSmooth

/-! ### An explicit `C¹` bump -/

/-- `h(x) = (x − 1/2)(2 − x)`. -/
noncomputable def hq (x : ℝ) : ℝ := (x - 1 / 2) * (2 - x)

/-- `g(x) = max(0, h(x))²`. -/
noncomputable def bump (x : ℝ) : ℝ := max 0 (hq x) ^ 2

/-- `g′(x) = 2 max(0, h(x))(5/2 − 2x)`. -/
noncomputable def bump' (x : ℝ) : ℝ := 2 * max 0 (hq x) * (5 / 2 - 2 * x)

lemma continuous_hq : Continuous hq := by
  unfold hq
  fun_prop

lemma hasDerivAt_hq (x : ℝ) : HasDerivAt hq (5 / 2 - 2 * x) x := by
  have h := ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).mul ((hasDerivAt_id x).const_sub (2 : ℝ))
  have e : ((fun y : ℝ ↦ id y - 1 / 2) * fun y ↦ 2 - id y) = hq := by
    funext y
    simp [hq]
  rw [e] at h
  convert h using 1
  simp only [id]
  ring

lemma hq_le (x : ℝ) : hq x ≤ 9 / 16 := by
  unfold hq
  nlinarith [sq_nonneg (x - 5 / 4)]

/-- `h(x) > 0` only on `(1/2, 2)`. -/
lemma mem_Ioo_of_hq_pos {x : ℝ} (h : 0 < hq x) : x ∈ Ioo (1 / 2 : ℝ) 2 := by
  unfold hq at h
  constructor
  · by_contra hx
    push Not at hx
    have : (x - 1 / 2) * (2 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · by_contra hx
    push Not at hx
    have : (x - 1 / 2) * (2 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

lemma hq_nonneg {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) : 0 ≤ hq x := by
  unfold hq
  exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])

lemma hasDerivAt_bump (x : ℝ) : HasDerivAt bump (bump' x) x := by
  rcases lt_trichotomy (hq x) 0 with hneg | hzero | hpos
  · have hev : bump =ᶠ[𝓝 x] fun _ ↦ 0 := by
      have : ∀ᶠ y in 𝓝 x, hq y < 0 :=
        (hasDerivAt_hq x).continuousAt.eventually (gt_mem_nhds hneg)
      filter_upwards [this] with y hy
      simp [bump, max_eq_left hy.le]
    have h0 : bump' x = 0 := by simp [bump', max_eq_left hneg.le]
    rw [h0]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · have h0 : bump' x = 0 := by simp [bump', hzero]
    have hb0 : bump x = 0 := by simp [bump, hzero]
    rw [h0, hasDerivAt_iff_isLittleO]
    have hO : (fun y ↦ hq y) =O[𝓝 x] fun y ↦ y - x := by
      have := (hasDerivAt_hq x).isBigO_sub
      simpa [hzero] using this
    have ho : (fun y ↦ hq y) =o[𝓝 x] fun _ ↦ (1 : ℝ) := by
      rw [isLittleO_one_iff]
      have := (hasDerivAt_hq x).continuousAt.tendsto
      rwa [hzero] at this
    have hprod : (fun y ↦ hq y * hq y) =o[𝓝 x] fun y ↦ (y - x) * 1 := hO.mul_isLittleO ho
    simp only [mul_one] at hprod
    have hle : (fun y ↦ bump y) =O[𝓝 x] fun y ↦ hq y * hq y := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun y ↦ ?_)
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by unfold bump; positivity),
        abs_mul_self]
      unfold bump
      have h1 : 0 ≤ max 0 (hq y) := le_max_left _ _
      have h2 : max 0 (hq y) ≤ |hq y| := max_le (abs_nonneg _) (le_abs_self _)
      calc max 0 (hq y) ^ 2 ≤ |hq y| ^ 2 := pow_le_pow_left₀ h1 h2 2
        _ = hq y * hq y := by rw [sq_abs]; ring
    refine (hle.trans_isLittleO hprod).congr_left fun y ↦ ?_
    simp [hb0]
  · have hev : bump =ᶠ[𝓝 x] fun y ↦ hq y ^ 2 := by
      have : ∀ᶠ y in 𝓝 x, 0 < hq y :=
        (hasDerivAt_hq x).continuousAt.eventually (lt_mem_nhds hpos)
      filter_upwards [this] with y hy
      simp [bump, max_eq_right hy.le]
    have hd := (hasDerivAt_hq x).pow 2
    have e : bump' x = ((2 : ℕ) : ℝ) * hq x ^ (2 - 1) * (5 / 2 - 2 * x) := by
      simp [bump', max_eq_right hpos.le]
    rw [e]
    exact hd.congr_of_eventuallyEq hev

lemma deriv_bump : deriv bump = bump' := funext fun x ↦ (hasDerivAt_bump x).deriv

lemma continuous_bump' : Continuous bump' := by
  unfold bump'
  exact (continuous_const.mul (continuous_const.max continuous_hq)).mul (by fun_prop)

lemma contDiff_bump : ContDiff ℝ 1 bump :=
  contDiff_one_iff_deriv.2 ⟨fun x ↦ (hasDerivAt_bump x).differentiableAt,
    deriv_bump ▸ continuous_bump'⟩

lemma bump_nonneg (x : ℝ) : 0 ≤ bump x := by
  unfold bump
  positivity

lemma support_bump : bump.support ⊆ Icc (1 / 2) 2 := by
  intro x hx
  rw [Function.mem_support] at hx
  have hpos : 0 < hq x := by
    by_contra h
    push Not at h
    exact hx (by simp [bump, max_eq_left h])
  exact Ioo_subset_Icc_self (mem_Ioo_of_hq_pos hpos)

lemma bump_le (x : ℝ) : bump x ≤ 81 / 256 := by
  unfold bump
  have h1 : 0 ≤ max 0 (hq x) := le_max_left _ _
  have h2 : max 0 (hq x) ≤ 9 / 16 := max_le (by norm_num) (hq_le x)
  calc max 0 (hq x) ^ 2 ≤ (9 / 16) ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = 81 / 256 := by norm_num

lemma abs_bump'_le (x : ℝ) : |bump' x| ≤ 27 / 16 := by
  unfold bump'
  rcases le_or_gt (hq x) 0 with h | h
  · rw [max_eq_left h, mul_zero, zero_mul, abs_zero]
    norm_num
  · rw [max_eq_right h.le]
    have hx := mem_Ioo_of_hq_pos h
    have h1 : |5 / 2 - 2 * x| ≤ 3 / 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rw [abs_mul, abs_mul, abs_of_pos h, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h2 := hq_le x
    calc 2 * hq x * |5 / 2 - 2 * x| ≤ 2 * (9 / 16) * (3 / 2) := by
          apply mul_le_mul (by linarith) h1 (abs_nonneg _) (by norm_num)
      _ = 27 / 16 := by norm_num

/-! ### The normalization -/

/-- `∫_{1/2}^{2} g(x)/x dx = 2 log 2 − 75/64`. -/
lemma integral_bump_div : ∫ x in Ioi 0, bump x / x = 2 * Real.log 2 - 75 / 64 := by
  have hsupp : (fun x ↦ bump x / x).support ⊆ Icc (1 / 2) 2 := by
    intro x hx
    apply support_bump
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hsupp
    ((Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hcongr : ∫ x in (1 / 2 : ℝ)..2, bump x / x =
      ∫ x in (1 / 2 : ℝ)..2, (x ^ 3 - 5 * x ^ 2 + 33 / 4 * x - 5 + x⁻¹) := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    rw [bump, max_eq_right (hq_nonneg hx)]
    simp only [hq]
    field_simp
    ring
  rw [hcongr]
  have i3 : IntervalIntegrable (fun x : ℝ ↦ x ^ 3) volume (1 / 2) 2 :=
    (continuous_pow 3).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ ↦ 5 * x ^ 2) volume (1 / 2) 2 :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun x : ℝ ↦ 33 / 4 * x) volume (1 / 2) 2 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have i0 : IntervalIntegrable (fun _ : ℝ ↦ (5 : ℝ)) volume (1 / 2) 2 :=
    continuous_const.intervalIntegrable _ _
  have iinv : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume (1 / 2) 2 :=
    intervalIntegral.intervalIntegrable_inv (fun x hx ↦ by
      rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]) continuousOn_id
  rw [intervalIntegral.integral_add ((i3.sub i2).add i1 |>.sub i0) iinv,
    intervalIntegral.integral_sub ((i3.sub i2).add i1) i0,
    intervalIntegral.integral_add (i3.sub i2) i1, intervalIntegral.integral_sub i3 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
    integral_pow, integral_id, intervalIntegral.integral_const, integral_inv_of_pos (by norm_num)
    (by norm_num)]
  rw [show (2 : ℝ) / (1 / 2) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  ring

lemma log_two_bound : (1 / 5 : ℝ) ≤ 2 * Real.log 2 - 75 / 64 := by
  have := Real.log_two_gt_d9
  linarith

/-- The normalizing constant `c₀ = 1/(2 log 2 − 75/64)`. -/
noncomputable def c₀ : ℝ := (2 * Real.log 2 - 75 / 64)⁻¹

lemma c₀_pos : 0 < c₀ := inv_pos.2 (by linarith [log_two_bound])

lemma c₀_le : c₀ ≤ 5 := by
  unfold c₀
  rw [inv_le_comm₀ (by linarith [log_two_bound]) (by norm_num)]
  linarith [log_two_bound]

/-- **The explicit smoothing** `ν₀ = c₀ g`. -/
noncomputable def ν₀ (x : ℝ) : ℝ := c₀ * bump x

lemma contDiff_ν₀ : ContDiff ℝ 1 ν₀ := contDiff_const.mul contDiff_bump

lemma ν₀_nonneg (x : ℝ) : 0 ≤ ν₀ x := mul_nonneg c₀_pos.le (bump_nonneg x)

lemma support_ν₀ : ν₀.support ⊆ Icc (1 / 2) 2 := by
  intro x hx
  apply support_bump
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [ν₀, h])

lemma mass_ν₀ : ∫ x in Ioi 0, ν₀ x / x = 1 := by
  have h : (fun x ↦ ν₀ x / x) = fun x ↦ c₀ * (bump x / x) := by
    funext x
    simp only [ν₀]
    ring
  rw [h, integral_const_mul, integral_bump_div, c₀, inv_mul_cancel₀ (by linarith [log_two_bound])]

lemma norm_ν₀_le (x : ℝ) : ‖ν₀ x‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (ν₀_nonneg x)]
  unfold ν₀
  calc c₀ * bump x ≤ 5 * (81 / 256) :=
        mul_le_mul c₀_le (bump_le x) (bump_nonneg x) (by norm_num)
    _ ≤ 2 := by norm_num

lemma norm_deriv_ν₀_le (x : ℝ) : ‖deriv ν₀ x‖ ≤ 9 := by
  have hd : deriv ν₀ x = c₀ * bump' x := by
    have := (hasDerivAt_bump x).const_mul c₀
    exact this.deriv
  rw [hd, Real.norm_eq_abs, abs_mul, abs_of_pos c₀_pos]
  calc c₀ * |bump' x| ≤ 5 * (27 / 16) :=
        mul_le_mul c₀_le (abs_bump'_le x) (abs_nonneg _) (by norm_num)
    _ ≤ 9 := by norm_num

/-! ### Mellin bounds with their constants -/

/-- PNT+'s `MellinOfPsi` with its constant: if `|ν′| ≤ S₁`, then `|𝓜ν(s)| ≤ 6S₁/|s|` for `0 < Re s ≤ 2`. -/
lemma norm_mellin_le_of_deriv {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {S₁ : ℝ} (hS₁ : ∀ x, ‖deriv ν x‖ ≤ S₁) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re ≤ 2) :
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ 6 * S₁ * ‖s‖⁻¹ := by
  have s_ne_zero : s ≠ 0 := fun h ↦ by rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  have hS₁0 : 0 ≤ S₁ := (norm_nonneg _).trans (hS₁ 0)
  have hsupp : (fun x : ℝ ↦ ((deriv ν x : ℝ) : ℂ) * (x : ℂ) ^ s).support ⊆ Icc (1 / 2) 2 := by
    intro x hx
    rw [Function.mem_support] at hx
    apply Function.support_deriv_subset_Icc suppν
    rw [Function.mem_support]
    intro h
    exact hx (by simp [h])
  simp only [mellin, smul_eq_mul]
  have hmul : ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * (ν x : ℂ) =
      ∫ x : ℝ in Ioi 0, (ν x : ℂ) * (x : ℂ) ^ (s - 1) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [hmul, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, norm_neg, one_div, norm_inv, mul_comm,
    SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hsupp
      ((Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num))]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
  refine (norm_setIntegral_le_of_norm_le_const (C := S₁ * 4) measure_Icc_lt_top ?_).trans ?_
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real]
    refine mul_le_mul (hS₁ x) ?_ (by positivity) hS₁0
    calc x ^ s.re ≤ 2 ^ s.re := Real.rpow_le_rpow hx0.le hx.2 hs0.le
      _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
      _ = 4 := by norm_num
  · rw [Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
    linarith

/-- Round 338's `MediumPNTW.MellinOfPsi_bdd` with its constant: if `|ν| ≤ S₀`, then `|𝓜ν(w)| ≤ 12S₀ + 1` for
`0 ≤ Re w ≤ 2`. -/
lemma norm_mellin_le_of_norm {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) {S₀ : ℝ}
    (hS₀ : ∀ x, ‖ν x‖ ≤ S₀) {w : ℂ} (hw0 : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ 12 * S₀ + 1 := by
  have hS₀0 : 0 ≤ S₀ := (norm_nonneg _).trans (hS₀ 0)
  have hsupp : (fun x : ℝ ↦ (x : ℂ) ^ (w - 1) • (ν x : ℂ)).support ⊆ Icc (1 / 2) 2 := by
    intro x hx
    apply suppν
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  rw [mellin, SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hsupp
    ((Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num))]
  refine (norm_setIntegral_le_of_norm_le_const (C := S₀ * 8) measure_Icc_lt_top ?_).trans ?_
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, mul_comm]
    refine mul_le_mul (hS₀ x) ?_ (by positivity) hS₀0
    rw [sub_re, one_re, Real.rpow_sub hx0, Real.rpow_one, div_le_iff₀ hx0]
    calc x ^ w.re ≤ 2 ^ w.re := Real.rpow_le_rpow hx0.le hx.2 hw0
      _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hw2
      _ = 4 := by norm_num
      _ ≤ 8 * x := by linarith [hx.1]
  · rw [Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
    linarith

/-- `|𝓜(Smooth1 ν ε)(s)| ≤ (12S₀ + 1)/|s|` (round 338's `MediumPNTW.MellinOfSmooth1d`, with its constant). -/
lemma norm_mellin_smooth1_le_d {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {S₀ : ℝ} (hS₀ : ∀ x, ‖ν x‖ ≤ S₀) :
    ∀ s : ℂ, 0 < s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ (12 * S₀ + 1) * ‖s‖⁻¹ := by
  intro s hs0 hs2 ε hε0 hε1
  rw [MellinOfSmooth1a diffν suppν hε0 hs0, norm_mul, norm_inv, mul_comm]
  have hre : ((ε : ℂ) * s).re = ε * s.re := by simp
  exact mul_le_mul_of_nonneg_right (norm_mellin_le_of_norm suppν hS₀ (by rw [hre]; positivity)
    (by rw [hre]; nlinarith)) (by positivity)

/-- `|𝓜(Smooth1 ν ε)(s)| ≤ 6S₁/(ε|s|²)` (PNT+'s `MellinOfSmooth1b`, with its constant). -/
lemma norm_mellin_smooth1_le_b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {S₁ : ℝ} (hS₁ : ∀ x, ‖deriv ν x‖ ≤ S₁) :
    ∀ σ₁ : ℝ, 0 < σ₁ → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ 6 * S₁ * (ε * ‖s‖ ^ 2)⁻¹ := by
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  have hs0 : 0 < s.re := lt_of_lt_of_le σ₁pos hs1
  rw [MellinOfSmooth1a diffν suppν εpos hs0]
  have hre : ((ε : ℂ) * s).re = ε * s.re := by simp
  have h := norm_mellin_le_of_deriv diffν suppν hS₁ (s := (ε : ℂ) * s) (by rw [hre]; positivity)
    (by rw [hre]; nlinarith)
  calc ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ = ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by
        simp
    _ ≤ ‖s⁻¹‖ * (6 * S₁ * ‖(ε : ℂ) * s‖⁻¹) := by gcongr
    _ = 6 * S₁ * (ε * ‖s‖ ^ 2)⁻¹ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg εpos.le, norm_inv]
        field_simp

/-- **The Mellin transform of `Smooth1 ν₀ ε` on a line, with its constant**: for `κ ∈ [0, 1]` and
`0 < σ ≤ 1`, `|𝓜(Smooth1 ν₀ ε)(σ + it)| ≤ 25^{1−κ}54^κ(σ/2)^{−1−κ}ε^{−κ}(1 + |t|)^{−1−κ}`. -/
lemma mellin_ν₀_le_geom {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      ‖𝓜 (fun x ↦ (Smooth1 ν₀ ε x : ℂ)) (σ + t * I)‖ ≤
        25 ^ (1 - κ) * 54 ^ κ * (σ / 2) ^ (-(1 + κ)) * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ)) := by
  have hB : ∀ s : ℂ, 0 < s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 ν₀ ε x : ℂ)) s‖ ≤ 25 * ‖s‖⁻¹ := by
    intro s h1 h2 ε h3 h4
    calc _ ≤ (12 * 2 + 1) * ‖s‖⁻¹ :=
          norm_mellin_smooth1_le_d contDiff_ν₀ support_ν₀ norm_ν₀_le s h1 h2 ε h3 h4
      _ = 25 * ‖s‖⁻¹ := by norm_num
  have hC : ∀ σ₁ : ℝ, 0 < σ₁ → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 ν₀ ε x : ℂ)) s‖ ≤ 54 * (ε * ‖s‖ ^ 2)⁻¹ := by
    intro σ₁ h0 s h1 h2 ε h3 h4
    calc _ ≤ 6 * 9 * (ε * ‖s‖ ^ 2)⁻¹ :=
          norm_mellin_smooth1_le_b contDiff_ν₀ support_ν₀ norm_deriv_ν₀_le σ₁ h0 s h1 h2 ε h3 h4
      _ = 54 * (ε * ‖s‖ ^ 2)⁻¹ := by norm_num
  exact SmoothPerron.mellin_le_geom_of (by norm_num) (by norm_num) hB hC hκ0 hκ1 hσ0 hσ1

end ExplicitSmooth
