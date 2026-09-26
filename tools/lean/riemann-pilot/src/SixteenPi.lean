import Mathlib
import Curvature

/-! # The constant `1/(16π)`: the formal content of the strip note's §3.4

The owner's working note (`riemann-strip-target-note.md` §3.4) derives the pilot's Gaussian-multiplier
time `τ_a = e^{−δ}/(16π)` (README rounds 70–73) within the paper's reduced balayage problem. This file
proves that derivation in full, including the balayage identity (round 75, §G below).

* **The closed-form integrals (iv).** `∫_X^∞ x⁻² ln x dx = (1 + ln X)/X` (`integral_log_div_sq_Ioi`),
  `P = ∫₀¹ (1 − √(1 − s²))/s² ds = π/2 − 1` (`P_eq`), `Q = ∫₀¹ ln s · (1 − √(1 − s²))/s² ds
  = π/2 − 1 − (π/2) ln 2` (`Q_eq`), by the substitution `s = sin θ` and Mathlib's
  `∫₀^{π/2} ln sin = −(π/2) ln 2`; the rescaling `∫₀^X (−ln t) h_X(t) dt = (−P ln X − Q)/X`
  (`balayageSide_eq`), and hence `J(X) = (π/(2X))(1 + ln(X/2))` (`J_eq`, `exteriorMoment_eq`).
* **The wall (v).** `(1 + ln(X/2))/X ≤ 1/2` with equality only at `X = 2` (`wall_le`, `wall_eq_iff`),
  quadratically (`wall_quadratic`); at the wall `τ = 1/(8T₀) = e^{−δ}/(16π)` (`tau_at_wall`).
* **The exterior form under D (ii), and its stability.** Matched zeros cancel exactly
  (`defect_eq_tail_of_D`); displaced ones by at most `Δ(2γ + Δ)/(γ²(γ − Δ)²) ≤ 10Δ/γ³` each
  (`inv_sq_sub_le`, `defect_sub_tail_le`), the note's "at most `2Δ/γ³(1 + O(Δ/γ))`".

* **The balayage identity, proved (round 75).** With the paper's explicit density
  `τ(x) = −I(x)/(π√(x² − X²))`, `I(x) = ∫_{−X}^{X} √(X² − t²) ln|t|/(x − t) dt`,
  `∫_X^∞ x⁻² τ = ∫₀^X (−ln t) h_X(t) dt` (`balayage_identity`), by Fubini and two arctan integrals —
  no harmonic measure. Hence the reduced problem's `1/(16π)` holds with no hypothesis
  (`exteriorMoment_reduced`, `sixteenPi_reduced`), and its exponent `2πX(1 + ln 2 − ln X)` is maximal
  exactly at `X = 2` (`fBalExp_le`).

**Not formalised:** the link from the reduced problem to ζ's ground state — the note's inputs
(vii)(a)–(d): Hypothesis D at the wall (RH-strength), the reduction's five lemmas, that the ground
state's wall is the reduced problem's maximiser, the continuum limit. Nothing here bears on RH.

* **The density in closed form (round 76).** `τ_X(x) = ln(Xx/(x + s)) − x ln(X/2)/s`, `s = √(x² − X²)`
  (`tauBal_closed`, from `Ibal_closed`): `ln|t| = ½∫₀^∞ (1/(1 + v) − 1/(t² + v)) dv`, Fubini, the
  elementary `t`-integrals `π(x − s)` and `π(√(X² + v) − √v)/√v` (arcsin antiderivatives), and an
  explicit logarithmic antiderivative in `v`. At the wall `τ = ln(2x/(x + √(x² − 4))) > 0`
  (`tauBal_two`): the balayage's admissibility, which the paper records as checked, not proved.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral
open scoped Interval

noncomputable section

namespace Pilot1ca

/-! ## A. The wall -/

/-- The note's (3.5): the defect time for a wall at `X·T₀`. -/
def tauWall (T₀ X : ℝ) : ℝ := (1 + log (X / 2)) / (4 * X * T₀)

/-- The wall law is at most `1/2`: `1 + ln y ≤ y`. -/
theorem wall_le {X : ℝ} (hX : 0 < X) : (1 + log (X / 2)) / X ≤ 1 / 2 := by
  have := Real.log_le_sub_one_of_pos (show 0 < X / 2 by positivity)
  rw [div_le_iff₀ hX]; linarith

/-- The maximum is attained only at `X = 2`. -/
theorem wall_eq_iff {X : ℝ} (hX : 0 < X) : (1 + log (X / 2)) / X = 1 / 2 ↔ X = 2 := by
  constructor
  · intro h
    have h' : log (X / 2) = X / 2 - 1 := by
      field_simp at h; linarith
    by_contra hne
    have := Real.log_lt_sub_one_of_pos (show 0 < X / 2 by positivity)
      (fun h2 => hne (by linarith))
    linarith
  · rintro rfl; norm_num

/-- **Quadratic stationarity at the wall.** With `y = X/2`,
`0 ≤ 1/2 − (1 + ln(X/2))/X ≤ (y − 1)²/(2y²)`: a relative displacement `η` of the wall moves `τ` by
`O(η²)`. -/
theorem wall_quadratic {X : ℝ} (hX : 0 < X) :
    0 ≤ 1 / 2 - (1 + log (X / 2)) / X ∧
      1 / 2 - (1 + log (X / 2)) / X ≤ (X / 2 - 1) ^ 2 / (2 * (X / 2) ^ 2) := by
  refine ⟨by linarith [wall_le hX], ?_⟩
  set y := X / 2 with hy
  have hy0 : 0 < y := by positivity
  have hX' : X = 2 * y := by rw [hy]; ring
  have hl := Real.one_sub_inv_le_log_of_pos hy0
  have key : y - 1 ≤ y * log y := by
    have := mul_le_mul_of_nonneg_left hl hy0.le
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hy0.ne'] at this
  rw [hX']
  have e : 1 / 2 - (1 + log y) / (2 * y) - (y - 1) ^ 2 / (2 * y ^ 2)
      = (y - 1 - y * log y) / (2 * y ^ 2) := by field_simp; ring
  have : (y - 1 - y * log y) / (2 * y ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **The constant (3.6).** At the wall `X = 2`, with `T₀ = 2πe^δ`: `τ = e^{−δ}/(16π)`. -/
theorem tau_at_wall (δ : ℝ) : tauWall (2 * π * exp δ) 2 = exp (-δ) / (16 * π) := by
  unfold tauWall
  rw [show (2 : ℝ) / 2 = 1 by norm_num, log_one, exp_neg]
  field_simp; ring

/-- With `δ = 2a`, the same constant is `1/(16πe^{2a})`, the pilot's form (README round 70). -/
theorem tau_at_wall' (a : ℝ) : tauWall (2 * π * exp (2 * a)) 2 = 1 / (16 * π * exp (2 * a)) := by
  rw [tau_at_wall, exp_neg]; field_simp

/-! ## B. `∫_X^∞ x⁻² ln x dx = (1 + ln X)/X` -/

theorem hasDerivAt_logTail {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => -(1 + log x) / x) (log x / x ^ 2) x := by
  have h1 : HasDerivAt (fun x => -(1 + log x)) (-x⁻¹) x :=
    ((hasDerivAt_log hx.ne').const_add 1).neg
  convert h1.div (hasDerivAt_id' x) hx.ne' using 1
  field_simp; ring

theorem tendsto_logTail : Tendsto (fun x : ℝ => -(1 + log x) / x) atTop (𝓝 0) := by
  have h1 := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at h1
  have h2 := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have := (h2.add h1).neg
  simp only [add_zero, neg_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-- `∫_X^∞ x⁻² ln x dx = (1 + ln X)/X` (for `X ≥ 1`, where the integrand is non-negative). -/
theorem integral_log_div_sq_Ioi {X : ℝ} (hX : 1 ≤ X) :
    ∫ x in Ioi X, log x / x ^ 2 = (1 + log X) / X := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_logTail (by
      linarith [hx.out])) (fun x hx => div_nonneg (log_nonneg (by linarith [hx.out]))
      (sq_nonneg _)) tendsto_logTail]
  ring

theorem integrableOn_log_div_sq_Ioi {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn (fun x => log x / x ^ 2) (Ioi X) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x hx => hasDerivAt_logTail (by linarith [hx.out]))
    (fun x hx => div_nonneg (log_nonneg (by linarith [hx.out])) (sq_nonneg _)) tendsto_logTail

/-! ## C. `P` and `Q`, by `s = sin θ` -/

/-- The note's kernel `(1 − √(1 − s²))/s²`, the restriction of its `h₁` to the slit. -/
def kerN (s : ℝ) : ℝ := (1 - √(1 - s ^ 2)) / s ^ 2

/-- On `0 < |s| ≤ 1` the kernel is `1/(1 + √(1 − s²))`: bounded and continuous. -/
theorem kerN_eq {s : ℝ} (hs : s ≠ 0) (h1 : s ^ 2 ≤ 1) : kerN s = 1 / (1 + √(1 - s ^ 2)) := by
  unfold kerN
  have hw := Real.sq_sqrt (show 0 ≤ 1 - s ^ 2 by linarith)
  have hpos : 0 < 1 + √(1 - s ^ 2) := by positivity
  rw [div_eq_div_iff (pow_ne_zero 2 hs) hpos.ne']
  linear_combination (-1 : ℝ) * hw

/-- The note's `P := ∫₀¹ (1 − √(1 − s²))/s² ds`. -/
def P : ℝ := ∫ s in (0 : ℝ)..1, kerN s

/-- The note's `Q := ∫₀¹ ln s · (1 − √(1 − s²))/s² ds`. -/
def Q : ℝ := ∫ s in (0 : ℝ)..1, log s * kerN s

theorem sin_image_Ioo_half_pi : sin '' Ioo 0 (π / 2) = Ioo 0 1 := by
  ext y; constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos]), ?_⟩
    have := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) le_rfl h1
    rwa [sin_pi_div_two] at this
  · rintro ⟨h0, h1⟩
    exact ⟨arcsin y, ⟨arcsin_pos.2 h0, arcsin_lt_pi_div_two.2 h1⟩,
      sin_arcsin (by linarith) h1.le⟩

/-- The substitution `s = sin θ`, for any `g` (no integrability needed). -/
theorem integral_subst_sin (g : ℝ → ℝ) :
    ∫ s in (0 : ℝ)..1, g s = ∫ θ in Ioo 0 (π / 2), g (sin θ) * cos θ := by
  have hinj : InjOn sin (Ioo 0 (π / 2)) := injOn_sin.mono fun θ (hθ : θ ∈ Ioo 0 (π / 2)) =>
    (⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩ : θ ∈ Icc (-(π / 2)) (π / 2))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← sin_image_Ioo_half_pi,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun θ _ => (hasDerivAt_sin θ).hasDerivWithinAt) hinj]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  rw [abs_of_pos (cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩), smul_eq_mul, mul_comm]

theorem setIntegral_Ioo_eq {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ θ in Ioo a b, f θ = ∫ θ in a..b, f θ := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem kerN_sin {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) : kerN (sin θ) = 1 / (1 + cos θ) := by
  have hs : sin θ ≠ 0 := (sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos])).ne'
  rw [kerN_eq hs (by nlinarith [sin_sq_add_cos_sq θ]),
    ← cos_eq_sqrt_one_sub_sin_sq (by linarith [hθ.1, pi_pos]) hθ.2.le]

theorem one_add_cos_pos {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) : 0 < 1 + cos θ := by
  have := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩; linarith

theorem hasDerivAt_Pprim {θ : ℝ} (h : 0 < 1 + cos θ) :
    HasDerivAt (fun θ => θ - sin θ / (1 + cos θ)) (cos θ / (1 + cos θ)) θ := by
  have := (hasDerivAt_id' θ).sub ((hasDerivAt_sin θ).div ((hasDerivAt_cos θ).const_add 1) h.ne')
  convert this using 1
  field_simp
  linear_combination sin_sq_add_cos_sq θ

/-- `∫₀^{π/2} cos θ/(1 + cos θ) dθ = π/2 − 1`. -/
theorem integral_cos_div : ∫ θ in (0 : ℝ)..(π / 2), cos θ / (1 + cos θ) = π / 2 - 1 := by
  have hI : ∀ θ ∈ uIcc 0 (π / 2), 0 < 1 + cos θ := fun θ hθ =>
    one_add_cos_pos (by rwa [uIcc_of_le (by positivity)] at hθ)
  rw [integral_eq_sub_of_hasDerivAt (fun θ hθ => hasDerivAt_Pprim (hI θ hθ))
    (ContinuousOn.intervalIntegrable (continuous_cos.continuousOn.div
      (continuous_const.add continuous_cos).continuousOn fun θ hθ => (hI θ hθ).ne'))]
  simp [sin_pi_div_two, cos_pi_div_two]

theorem P_eq : P = π / 2 - 1 := by
  rw [P, integral_subst_sin, ← integral_cos_div, ← setIntegral_Ioo_eq (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  rw [kerN_sin hθ]; ring

/-- The antiderivative of `ln sin θ/(1 + cos θ)`: `sin θ ln sin θ/(1 + cos θ) − θ + tan(θ/2)`. -/
def Hprim (θ : ℝ) : ℝ := sin θ * log (sin θ) / (1 + cos θ) - θ + sin θ / (1 + cos θ)

theorem hasDerivAt_Hprim {θ : ℝ} (hs : 0 < sin θ) (h : 0 < 1 + cos θ) :
    HasDerivAt Hprim (log (sin θ) / (1 + cos θ)) θ := by
  have hc := (hasDerivAt_cos θ).const_add 1
  have hsl := (hasDerivAt_sin θ).mul ((hasDerivAt_sin θ).log hs.ne')
  have := ((hsl.div hc h.ne').sub (hasDerivAt_id' θ)).add ((hasDerivAt_sin θ).div hc h.ne')
  convert this using 1
  · ext x; simp [Hprim]
  · simp only [Pi.mul_apply]
    rw [mul_div_cancel₀ _ hs.ne']
    set L := log (sin θ)
    field_simp
    linear_combination (-(L + 1)) * sin_sq_add_cos_sq θ

theorem continuousOn_Hprim : ContinuousOn Hprim (Icc 0 (π / 2)) := by
  have hne : ∀ θ ∈ Icc 0 (π / 2), 1 + cos θ ≠ 0 := fun θ hθ => (one_add_cos_pos hθ).ne'
  unfold Hprim
  refine ((ContinuousOn.div ?_ ?_ hne).sub continuousOn_id).add
    (continuous_sin.continuousOn.div (continuous_const.add continuous_cos).continuousOn hne)
  · exact (continuous_mul_log.comp continuous_sin).continuousOn
  · exact (continuous_const.add continuous_cos).continuousOn

/-- `∫₀^{π/2} ln sin θ/(1 + cos θ) dθ = 1 − π/2`. -/
theorem integral_log_sin_div : ∫ θ in (0 : ℝ)..(π / 2), log (sin θ) / (1 + cos θ) = 1 - π / 2 := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  rw [integral_eq_sub_of_hasDerivAt_of_le hpi continuousOn_Hprim
    (fun θ hθ => hasDerivAt_Hprim (sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos]))
      (one_add_cos_pos ⟨hθ.1.le, hθ.2.le⟩))]
  · simp [Hprim, sin_pi_div_two, cos_pi_div_two]; ring
  · refine (intervalIntegrable_log_sin (a := 0) (b := π / 2)).mul_continuousOn
      (g := fun θ => 1 / (1 + cos θ)) ?_ |>.congr_ae ?_
    · refine continuousOn_const.div (continuous_const.add continuous_cos).continuousOn ?_
      intro θ hθ; rw [uIcc_of_le hpi] at hθ; exact (one_add_cos_pos hθ).ne'
    · exact Eventually.of_forall fun θ => by simp [div_eq_mul_inv]

theorem Q_eq : Q = π / 2 - 1 - π / 2 * log 2 := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hne : ∀ θ ∈ uIcc 0 (π / 2), 1 + cos θ ≠ 0 := fun θ hθ =>
    (one_add_cos_pos (by rwa [uIcc_of_le hpi] at hθ)).ne'
  have i1 : IntervalIntegrable (fun θ => log (sin θ)) volume 0 (π / 2) := intervalIntegrable_log_sin
  have i2 : IntervalIntegrable (fun θ => log (sin θ) / (1 + cos θ)) volume 0 (π / 2) := by
    refine (i1.mul_continuousOn (g := fun θ => 1 / (1 + cos θ))
      (continuousOn_const.div (continuous_const.add continuous_cos).continuousOn hne)).congr_ae ?_
    exact Eventually.of_forall fun θ => by simp [div_eq_mul_inv]
  have key : ∫ θ in (0 : ℝ)..(π / 2), log (sin θ) * (cos θ / (1 + cos θ))
      = (∫ θ in (0 : ℝ)..(π / 2), log (sin θ)) - ∫ θ in (0 : ℝ)..(π / 2), log (sin θ) / (1 + cos θ) := by
    rw [← intervalIntegral.integral_sub i1 i2]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    field_simp [hne θ hθ]; ring
  rw [Q, integral_subst_sin, setIntegral_congr_fun measurableSet_Ioo
    (g := fun θ => log (sin θ) * (cos θ / (1 + cos θ))) (fun θ hθ => by
      simp only; rw [kerN_sin hθ]; ring), setIntegral_Ioo_eq hpi, key,
    integral_log_sin_zero_pi_div_two, integral_log_sin_div]
  ring

/-! ## D. The rescaling, `J(X)`, and the time -/

/-- The note's `h_X` on the slit `(−X, X)`: `(1 − √(1 − t²/X²))/t²`. -/
def hBal (X t : ℝ) : ℝ := (1 - √(1 - t ^ 2 / X ^ 2)) / t ^ 2

/-- The balayage side of the note's (iv): `∫₀^X (−ln t) h_X(t) dt`. -/
def balayageSide (X : ℝ) : ℝ := ∫ t in (0 : ℝ)..X, -log t * hBal X t

theorem hBal_eq {X : ℝ} (hX : X ≠ 0) (t : ℝ) : hBal X t = kerN (t / X) / X ^ 2 := by
  unfold hBal kerN
  rw [div_pow, div_div, div_mul_cancel₀ _ (pow_ne_zero 2 hX)]

theorem continuous_kerC : Continuous fun s : ℝ => 1 / (1 + √(1 - s ^ 2)) :=
  continuous_const.div (continuous_const.add (continuous_const.sub (continuous_pow 2)).sqrt)
    fun s => by positivity

theorem kerN_ae : ∀ᵐ s ∂(volume.restrict (Ι (0 : ℝ) 1)), 1 / (1 + √(1 - s ^ 2)) = kerN s := by
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  exact (kerN_eq hs.1.ne' (by nlinarith [hs.1, hs.2])).symm

theorem kerN_intervalIntegrable : IntervalIntegrable kerN volume 0 1 :=
  continuous_kerC.intervalIntegrable 0 1 |>.congr_ae kerN_ae

theorem logKerN_intervalIntegrable : IntervalIntegrable (fun s => log s * kerN s) volume 0 1 := by
  refine (intervalIntegrable_log'.mul_continuousOn continuous_kerC.continuousOn).congr_ae ?_
  filter_upwards [kerN_ae] with s hs
  rw [hs]

/-- **The rescaling `t = Xs`**: `∫₀^X (−ln t) h_X(t) dt = (−P ln X − Q)/X`. -/
theorem balayageSide_eq {X : ℝ} (hX : 0 < X) : balayageSide X = (-P * log X - Q) / X := by
  have e : EqOn (fun t => -log t * hBal X t)
      (fun t => (fun s => (-log X * kerN s - log s * kerN s) / X ^ 2) (t / X)) (uIcc 0 X) := by
    intro t _
    simp only
    rw [hBal_eq hX.ne']
    rcases eq_or_ne t 0 with rfl | ht
    · simp [kerN]
    · rw [log_div ht hX.ne']; ring
  have hP : ∫ s in (0 : ℝ)..1, kerN s = P := rfl
  have hQ : ∫ s in (0 : ℝ)..1, log s * kerN s = Q := rfl
  rw [balayageSide, intervalIntegral.integral_congr e, intervalIntegral.integral_comp_div
      (f := fun s => (-log X * kerN s - log s * kerN s) / X ^ 2) (a := 0) (b := X) hX.ne',
    zero_div, div_self hX.ne', smul_eq_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (kerN_intervalIntegrable.const_mul _) logKerN_intervalIntegrable,
    intervalIntegral.integral_const_mul, hP, hQ]
  field_simp

/-- The note's `J(X)` given the balayage identity: `∫_X^∞ x⁻² ln x dx − ∫₀^X (−ln t) h_X(t) dt`. -/
def J (X : ℝ) : ℝ := (1 + log X) / X - balayageSide X

/-- **The note's (3.4)**: `J(X) = (π/(2X))(1 + ln(X/2))`. -/
theorem J_eq {X : ℝ} (hX : 0 < X) : J X = π / (2 * X) * (1 + log (X / 2)) := by
  rw [J, balayageSide_eq hX, P_eq, Q_eq, log_div hX.ne' two_ne_zero]
  field_simp; ring

theorem J_two : J 2 = π / 4 := by
  rw [J_eq two_pos]; norm_num

/-- **The exterior moment, given the balayage identity.** If the probe's exterior zero density `τ`
satisfies the balayage identity `∫_X^∞ x⁻² τ = ∫₀^X (−ln t) h_X(t) dt` (proved for the paper's density
in `balayage_identity` below), then `∫_X^∞ x⁻²[ln x − τ(x)] dx = (π/(2X))(1 + ln(X/2))`. -/
theorem exteriorMoment_eq {X : ℝ} (hX : 1 ≤ X) {τ : ℝ → ℝ}
    (hτ : IntegrableOn (fun x => τ x / x ^ 2) (Ioi X))
    (hbal : ∫ x in Ioi X, τ x / x ^ 2 = balayageSide X) :
    ∫ x in Ioi X, (log x - τ x) / x ^ 2 = π / (2 * X) * (1 + log (X / 2)) := by
  simp_rw [sub_div]
  rw [integral_sub (integrableOn_log_div_sq_Ioi hX) hτ, integral_log_div_sq_Ioi hX, hbal]
  exact J_eq (by linarith)

/-- The note's (3.3) → (3.5): `J(X)/(2πT₀) = (1 + ln(X/2))/(4XT₀)`. -/
theorem J_div_eq_tauWall {T₀ X : ℝ} (hT : 0 < T₀) (hX : 0 < X) :
    J X / (2 * π * T₀) = tauWall T₀ X := by
  rw [J_eq hX, tauWall]; field_simp; ring

/-- **The chain of §3.4 (iii)–(v), assembled.** Given the balayage identity at the wall `X = 2`, the
exterior moment divided by `2πT₀`, `T₀ = 2πe^δ`, is `e^{−δ}/(16π)`. -/
theorem sixteenPi_of_balayage (δ : ℝ) {τ : ℝ → ℝ}
    (hτ : IntegrableOn (fun x => τ x / x ^ 2) (Ioi 2))
    (hbal : ∫ x in Ioi (2 : ℝ), τ x / x ^ 2 = balayageSide 2) :
    (∫ x in Ioi (2 : ℝ), (log x - τ x) / x ^ 2) / (2 * π * (2 * π * exp δ))
      = exp (-δ) / (16 * π) := by
  rw [exteriorMoment_eq one_le_two hτ hbal, ← J_eq two_pos,
    J_div_eq_tauWall (by positivity) two_pos, tau_at_wall]

/-! ## E. The exterior form under D, and its stability -/

/-- **One displaced zero.** If `|t − γ| ≤ Δ < γ`, then
`|γ⁻² − t⁻²| ≤ Δ(2γ + Δ)/(γ²(γ − Δ)²)`, the note's `2Δ/γ³(1 + O(Δ/γ))`. -/
theorem inv_sq_sub_le {γ t Δ : ℝ} (hγ : 0 < γ) (hΔ : |t - γ| ≤ Δ) (hΔγ : Δ < γ) :
    |1 / γ ^ 2 - 1 / t ^ 2| ≤ Δ * (2 * γ + Δ) / (γ ^ 2 * (γ - Δ) ^ 2) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hΔ
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hΔ
  have ht : 0 < t := by linarith
  have htd : γ - Δ ≤ t := by linarith
  have hd0 : 0 < γ - Δ := by linarith
  have e : 1 / γ ^ 2 - 1 / t ^ 2 = (t - γ) * (t + γ) / (γ ^ 2 * t ^ 2) := by field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos (by positivity : 0 < t + γ),
    abs_of_pos (by positivity : 0 < γ ^ 2 * t ^ 2)]
  have hnum : |t - γ| * (t + γ) ≤ Δ * (2 * γ + Δ) :=
    mul_le_mul hΔ (by linarith) (by positivity) hΔ0
  have hden : γ ^ 2 * (γ - Δ) ^ 2 ≤ γ ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0.le htd 2) (by positivity)
  calc |t - γ| * (t + γ) / (γ ^ 2 * t ^ 2) ≤ Δ * (2 * γ + Δ) / (γ ^ 2 * t ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ Δ * (2 * γ + Δ) / (γ ^ 2 * (γ - Δ) ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hΔ0 (by linarith)) (by positivity) hden

/-- The same, in the form `≤ 10Δ/γ³` once `Δ ≤ γ/2`. -/
theorem inv_sq_sub_le_ten {γ t Δ : ℝ} (hγ : 0 < γ) (hΔ : |t - γ| ≤ Δ) (hΔγ : Δ ≤ γ / 2) :
    |1 / γ ^ 2 - 1 / t ^ 2| ≤ 10 * Δ / γ ^ 3 := by
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hΔ
  refine (inv_sq_sub_le hγ hΔ (by linarith)).trans ?_
  have hd0 : 0 < γ - Δ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have A : (2 * γ + Δ) * γ ≤ 10 * (γ - Δ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ γ - 2 * Δ by linarith) (show 0 ≤ 8 * γ - 5 * Δ by linarith)]
  have B := mul_le_mul_of_nonneg_left A (show 0 ≤ Δ * γ ^ 2 by positivity)
  nlinarith [B]

/-- **(3.2): matched zeros cancel.** Enumerate the positive zeros of `Ξ` and of `ĝ_a` with
multiplicity, `γ` and `t`. The curvature defect `Σγ⁻² − Σt⁻²` minus the defect of the tails beyond
the first `N` is the finite sum of the first `N` differences. -/
theorem defect_sub_tail {γ t : ℕ → ℝ} (hγ : Summable fun n => 1 / γ n ^ 2)
    (ht : Summable fun n => 1 / t n ^ 2) (N : ℕ) :
    ((∑' n, 1 / γ n ^ 2) - ∑' n, 1 / t n ^ 2)
        - ((∑' n, 1 / γ (n + N) ^ 2) - ∑' n, 1 / t (n + N) ^ 2)
      = ∑ n ∈ Finset.range N, (1 / γ n ^ 2 - 1 / t n ^ 2) := by
  rw [← hγ.sum_add_tsum_nat_add N, ← ht.sum_add_tsum_nat_add N, Finset.sum_sub_distrib]; ring

/-- **Exact D ⇒ the exterior form (3.2).** If the first `N` zeros coincide (D at a horizon between the
`N`th and `(N+1)`st), the defect is exactly the tails' defect. -/
theorem defect_eq_tail_of_D {γ t : ℕ → ℝ} (hγ : Summable fun n => 1 / γ n ^ 2)
    (ht : Summable fun n => 1 / t n ^ 2) (N : ℕ) (hD : ∀ n < N, t n = γ n) :
    (∑' n, 1 / γ n ^ 2) - ∑' n, 1 / t n ^ 2
      = (∑' n, 1 / γ (n + N) ^ 2) - ∑' n, 1 / t (n + N) ^ 2 := by
  have := defect_sub_tail hγ ht N
  rw [Finset.sum_eq_zero (fun n hn => by rw [hD n (Finset.mem_range.1 hn), sub_self])] at this
  linarith

/-- **D within tolerance (the paper's census).** If the first `N` zeros are matched within `Δ_n ≤ γ_n/2`,
the defect differs from the tails' defect by at most `Σ_{n<N} 10Δ_n/γ_n³`. -/
theorem defect_sub_tail_le {γ t Δ : ℕ → ℝ} (hγ : Summable fun n => 1 / γ n ^ 2)
    (ht : Summable fun n => 1 / t n ^ 2) (N : ℕ) (hpos : ∀ n < N, 0 < γ n)
    (hD : ∀ n < N, |t n - γ n| ≤ Δ n) (hΔ : ∀ n < N, Δ n ≤ γ n / 2) :
    |((∑' n, 1 / γ n ^ 2) - ∑' n, 1 / t n ^ 2)
        - ((∑' n, 1 / γ (n + N) ^ 2) - ∑' n, 1 / t (n + N) ^ 2)|
      ≤ ∑ n ∈ Finset.range N, 10 * Δ n / γ n ^ 3 := by
  rw [defect_sub_tail hγ ht N]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn := Finset.mem_range.1 hn
  exact inv_sq_sub_le_ten (hpos n hn) (hD n hn) (hΔ n hn)

/-! ## F. (3.1): the time is the multiplier's `z²` coefficient -/

/-- **(3.1), exactly.** For Hadamard products `f(z)/f(0) = Π(1 − z²w_i)` (the ground state's transform,
`w = τ⁻²`) and `F(z)/F(0) = Π(1 − z²v_k)` (Riemann's `Ξ`, `v = γ⁻²`),
`f(z)/f(0) = (F(z)/F(0))·(1 + τ z² ) + O(‖z‖⁴)` with `τ = Σv − Σw = Σγ⁻² − Στ⁻²`, the curvature
defect `κ_Ξ − κ(a)`; explicitly the error is at most `3‖z‖⁴(Σ‖w‖ + Σ‖v‖)²` once
`‖z‖²(Σ‖w‖ + Σ‖v‖) ≤ 1`. So the pilot's multiplier time is the note's defect, whatever its value. -/
theorem multiplier_expansion {ι κ : Type*} {f F : ℂ → ℂ} {w : ι → ℂ} {v : κ → ℂ}
    (hf : HadamardW f w) (hF : HadamardW F v) (z : ℂ)
    (hz : ‖z‖ ^ 2 * ((∑' i, ‖w i‖) + ∑' k, ‖v k‖) ≤ 1) :
    ‖f z / f 0 - F z / F 0 * (1 + z ^ 2 * ((∑' k, v k) - ∑' i, w i))‖
      ≤ 3 * ‖z‖ ^ 4 * ((∑' i, ‖w i‖) + ∑' k, ‖v k‖) ^ 2 := by
  set A := ∑' i, ‖w i‖ with hAdef
  set B := ∑' k, ‖v k‖ with hBdef
  set W := ∑' i, w i with hWdef
  set V := ∑' k, v k with hVdef
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  set r := ‖z‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have e1 := hf.expansion z (by nlinarith)
  have e2 := hF.expansion z (by nlinarith)
  have hW : ‖W‖ ≤ A := norm_tsum_le_tsum_norm hf.summ
  have hV : ‖V‖ ≤ B := norm_tsum_le_tsum_norm hF.summ
  have hz2 : ‖z ^ 2‖ = r := by rw [norm_pow]
  have hz4 : ‖z‖ ^ 4 = r ^ 2 := by rw [hr]; ring
  have hVW : ‖V - W‖ ≤ A + B := (norm_sub_le _ _).trans (by linarith)
  have hm : ‖1 + z ^ 2 * (V - W)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, hz2]
    nlinarith [mul_le_mul_of_nonneg_left hVW hr0]
  have key : f z / f 0 - F z / F 0 * (1 + z ^ 2 * (V - W))
      = (f z / f 0 - (1 - z ^ 2 * W)) - (F z / F 0 - (1 - z ^ 2 * V)) * (1 + z ^ 2 * (V - W))
        + z ^ 2 * z ^ 2 * (V * (V - W)) := by ring
  rw [key, hz4]
  have t3 : ‖z ^ 2 * z ^ 2 * (V * (V - W))‖ ≤ r ^ 2 * (B * (A + B)) := by
    rw [norm_mul, norm_mul, norm_mul, hz2]
    have := mul_le_mul hV hVW (norm_nonneg _) hB
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg r)]
  have t2 : ‖(F z / F 0 - (1 - z ^ 2 * V)) * (1 + z ^ 2 * (V - W))‖ ≤ (r * B) ^ 2 * 2 := by
    rw [norm_mul]; exact mul_le_mul e2 hm (norm_nonneg _) (sq_nonneg _)
  calc _ ≤ ‖f z / f 0 - (1 - z ^ 2 * W)‖
          + ‖(F z / F 0 - (1 - z ^ 2 * V)) * (1 + z ^ 2 * (V - W))‖
          + ‖z ^ 2 * z ^ 2 * (V * (V - W))‖ := (norm_add_le _ _).trans
            (by gcongr; exact norm_sub_le _ _)
    _ ≤ (r * A) ^ 2 + (r * B) ^ 2 * 2 + r ^ 2 * (B * (A + B)) := by linarith
    _ ≤ 3 * r ^ 2 * (A + B) ^ 2 := by nlinarith [mul_nonneg hA hB, sq_nonneg r]


/-! ## G. The balayage identity, proved from the paper's explicit density -/

/-- The paper's Cauchy integral (Theorem 1bm(iv)): `I(x) = ∫_{−X}^{X} √(X² − t²) ln|t|/(x − t) dt`. -/
def Ibal (X x : ℝ) : ℝ := ∫ t in (-X)..X, √(X ^ 2 - t ^ 2) * log |t| / (x - t)

/-- The paper's balayage density on the exterior: `τ(x) = −I(x)/(π√(x² − X²))`. -/
def tauBal (X x : ℝ) : ℝ := -Ibal X x / (π * √(x ^ 2 - X ^ 2))

/-- The kernel: harmonic measure of the doubly slit plane seen from `t`, divided by `x²`. -/
def kBal (X t x : ℝ) : ℝ := √(X ^ 2 - t ^ 2) / (π * x ^ 2 * √(x ^ 2 - X ^ 2) * (x - t))

/-- The arctan kernel `x/((x² − X² + c²)√(x² − X²))`. -/
def gAt (X c x : ℝ) : ℝ := x / ((x ^ 2 - X ^ 2 + c ^ 2) * √(x ^ 2 - X ^ 2))

theorem hasDerivAt_arctanPrim {X c x : ℝ} (hc : 0 < c) (hx : X ^ 2 < x ^ 2) :
    HasDerivAt (fun x => arctan (√(x ^ 2 - X ^ 2) / c) / c) (gAt X c x) x := by
  have hu : 0 < x ^ 2 - X ^ 2 := by linarith
  have h1 : HasDerivAt (fun x => x ^ 2 - X ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const (X ^ 2)
  have h2 := ((h1.sqrt hu.ne').div_const c).arctan.div_const c
  convert h2 using 1
  have hs := Real.sq_sqrt hu.le
  have hs0 : 0 < √(x ^ 2 - X ^ 2) := Real.sqrt_pos.2 hu
  unfold gAt
  rw [div_pow, hs]
  field_simp
  ring

theorem tendsto_arctanPrim {X c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => arctan (√(x ^ 2 - X ^ 2) / c) / c) atTop (𝓝 (π / (2 * c))) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 2 - X ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 := ((Real.tendsto_sqrt_atTop.comp h1).atTop_div_const hc)
  have h3 := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h2
  have := h3.div_const c
  rw [show π / (2 * c) = π / 2 / c by ring]
  exact this

theorem gAt_nonneg {X c x : ℝ} (hX : 0 ≤ X) (hx : X < x) : 0 ≤ gAt X c x := by
  unfold gAt
  have : 0 ≤ x ^ 2 - X ^ 2 := by nlinarith
  exact div_nonneg (by linarith) (mul_nonneg (by nlinarith [sq_nonneg c]) (Real.sqrt_nonneg _))

/-- `∫_X^∞ x dx/((x² − X² + c²)√(x² − X²)) = π/(2c)`, with integrability. -/
theorem integral_gAt {X c : ℝ} (hX : 0 ≤ X) (hc : 0 < c) :
    IntegrableOn (gAt X c) (Ioi X) ∧ ∫ x in Ioi X, gAt X c x = π / (2 * c) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => arctan (√(x ^ 2 - X ^ 2) / c) / c) (Ici X) X :=
    (by fun_prop : Continuous fun x : ℝ => arctan (√(x ^ 2 - X ^ 2) / c) / c).continuousWithinAt
  have hder : ∀ x ∈ Ioi X, HasDerivAt (fun x : ℝ => arctan (√(x ^ 2 - X ^ 2) / c) / c)
      (gAt X c x) x := fun x hx => hasDerivAt_arctanPrim hc (by nlinarith [hx.out])
  have hpos : ∀ x ∈ Ioi X, 0 ≤ gAt X c x := fun x hx => gAt_nonneg hX hx
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hder hpos (tendsto_arctanPrim hc), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos (tendsto_arctanPrim hc)]
  simp

theorem kBal_nonneg {X t x : ℝ} (ht : |t| < X) (hx : X < x) : 0 ≤ kBal X t x := by
  unfold kBal
  have := abs_lt.1 ht
  refine div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
    (Real.sqrt_nonneg _)) (by linarith))

/-- **The pair kernel.** For `0 < |t| < X` and `x > X`, `k(t, x) + k(−t, x)` is a combination of two
arctan kernels, with `c = √(X² − t²)` and `c = X`. -/
theorem kBal_pair {X t x : ℝ} (hX : 0 < X) (ht0 : t ≠ 0) (ht : |t| < X) (hx : X < x) :
    kBal X t x + kBal X (-t) x
      = 2 * √(X ^ 2 - t ^ 2) / (π * t ^ 2) * (gAt X (√(X ^ 2 - t ^ 2)) x - gAt X X x) := by
  have htX := abs_lt.1 ht
  have hc2 : √(X ^ 2 - t ^ 2) ^ 2 = X ^ 2 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hu : 0 < x ^ 2 - X ^ 2 := by nlinarith
  have hs0 : 0 < √(x ^ 2 - X ^ 2) := Real.sqrt_pos.2 hu
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x - t := by linarith
  have h2 : 0 < x + t := by linarith
  unfold kBal gAt
  rw [hc2, neg_sq, sub_neg_eq_add]
  have e1 : x ^ 2 - X ^ 2 + (X ^ 2 - t ^ 2) = (x - t) * (x + t) := by ring
  have e2 : x ^ 2 - X ^ 2 + X ^ 2 = x ^ 2 := by ring
  rw [e1, e2]
  field_simp
  ring

theorem hBal_eq' {X : ℝ} (hX : 0 < X) (t : ℝ) :
    hBal X t = (1 - √(X ^ 2 - t ^ 2) / X) / t ^ 2 := by
  unfold hBal
  congr 2
  rw [show 1 - t ^ 2 / X ^ 2 = (X ^ 2 - t ^ 2) / X ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg X),
    Real.sqrt_sq hX.le]

/-- The pair integral: `∫_X^∞ [k(t, x) + k(−t, x)] dx = h_X(t)`, with both one-sided kernels
integrable. -/
theorem kBal_integrals {X t : ℝ} (hX : 0 < X) (ht0 : t ≠ 0) (ht : |t| < X) :
    IntegrableOn (kBal X t) (Ioi X) ∧ IntegrableOn (kBal X (-t)) (Ioi X) ∧
      (∫ x in Ioi X, kBal X t x) + (∫ x in Ioi X, kBal X (-t) x) = hBal X t := by
  have htX := abs_lt.1 ht
  have hc : 0 < √(X ^ 2 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  obtain ⟨i1, e1⟩ := integral_gAt hX.le hc
  obtain ⟨i2, e2⟩ := integral_gAt hX.le hX
  have ipair : IntegrableOn (fun x => 2 * √(X ^ 2 - t ^ 2) / (π * t ^ 2) *
      (gAt X (√(X ^ 2 - t ^ 2)) x - gAt X X x)) (Ioi X) := (i1.sub i2).const_mul _
  have hpair : EqOn (fun x => kBal X t x + kBal X (-t) x) (fun x => 2 * √(X ^ 2 - t ^ 2) /
      (π * t ^ 2) * (gAt X (√(X ^ 2 - t ^ 2)) x - gAt X X x)) (Ioi X) :=
    fun x hx => kBal_pair hX ht0 ht hx
  have ht' : |-t| < X := by rwa [abs_neg]
  have meas : ∀ s : ℝ, AEStronglyMeasurable (kBal X s) (volume.restrict (Ioi X)) :=
    fun s => (by unfold kBal; fun_prop : Measurable (kBal X s)).aestronglyMeasurable
  have one : ∀ s : ℝ, |s| < X → (∀ x ∈ Ioi X, kBal X s x ≤ kBal X t x + kBal X (-t) x) →
      IntegrableOn (kBal X s) (Ioi X) := by
    intro s hs hle
    refine Integrable.mono' (ipair.congr_fun hpair.symm measurableSet_Ioi) (meas s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (kBal_nonneg hs hx)]
    exact hle x hx
  have I1 := one t ht fun x hx => le_add_of_nonneg_right (kBal_nonneg ht' hx)
  have I2 := one (-t) ht' fun x hx => le_add_of_nonneg_left (kBal_nonneg ht hx)
  refine ⟨I1, I2, ?_⟩
  rw [← integral_add I1 I2, setIntegral_congr_fun measurableSet_Ioi hpair, MeasureTheory.integral_const_mul,
    integral_sub i1 i2, e1, e2, hBal_eq' hX t]
  field_simp


/-- The one-sided kernel mass `A(t) = ∫_X^∞ k(t, x) dx`. -/
def Abal (X t : ℝ) : ℝ := ∫ x in Ioi X, kBal X t x

theorem kerN_le_one {s : ℝ} (hs : s ≠ 0) (h1 : s ^ 2 ≤ 1) : kerN s ≤ 1 := by
  rw [kerN_eq hs h1, div_le_one (by positivity)]
  linarith [Real.sqrt_nonneg (1 - s ^ 2)]

theorem Abal_bounds {X t : ℝ} (hX : 0 < X) (ht0 : t ≠ 0) (ht : |t| < X) :
    0 ≤ Abal X t ∧ Abal X t ≤ 1 / X ^ 2 := by
  have ht' : |-t| < X := by rwa [abs_neg]
  have h0 : ∀ s, |s| < X → 0 ≤ Abal X s := fun s hs =>
    setIntegral_nonneg measurableSet_Ioi fun x hx => kBal_nonneg hs hx
  obtain ⟨-, -, e⟩ := kBal_integrals hX ht0 ht
  refine ⟨h0 t ht, ?_⟩
  have hh : hBal X t ≤ 1 / X ^ 2 := by
    rw [hBal_eq hX.ne', div_le_div_iff_of_pos_right (by positivity)]
    refine kerN_le_one (div_ne_zero ht0 hX.ne') ?_
    rw [div_pow, div_le_one (by positivity)]
    exact sq_le_sq' (by linarith [(abs_lt.1 ht).1]) (by linarith [(abs_lt.1 ht).2]) |>.trans_eq rfl
  have := h0 (-t) ht'
  unfold Abal at *
  linarith

/-- **The balayage identity, proved.** With the paper's explicit density
`τ(x) = −I(x)/(π√(x² − X²))`, `I(x) = ∫_{−X}^{X} √(X² − t²) ln|t|/(x − t) dt`,
`∫_X^∞ x⁻² τ(x) dx = ∫₀^X (−ln t) h_X(t) dt`, and `x⁻²τ` is integrable on `(X, ∞)`. The proof exchanges
the two integrals (Fubini) and evaluates the kernel's mass in closed form (`kBal_integrals`); no
harmonic measure is needed. -/
theorem balayage_identity {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun x => tauBal X x / x ^ 2) (Ioi X) ∧
      ∫ x in Ioi X, tauBal X x / x ^ 2 = balayageSide X := by
  set ν : Measure ℝ := volume.restrict (Ioo (-X) X)
  set μ : Measure ℝ := volume.restrict (Ioi X)
  set F : ℝ → ℝ → ℝ := fun t x => -log |t| * kBal X t x with hF
  have hne0 : ∀ᵐ t ∂ν, t ≠ 0 := ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hmem : ∀ᵐ t ∂ν, t ∈ Ioo (-X) X := ae_restrict_mem measurableSet_Ioo
  have meas : Measurable (Function.uncurry F) := by
    change Measurable fun p : ℝ × ℝ => -log |p.1| * kBal X p.1 p.2
    unfold kBal; fun_prop
  -- the bound on `ν`
  have hbound : IntegrableOn (fun t => |log t| / X ^ 2) (Ioo (-X) X) := by
    have h1 : IntegrableOn (fun t => ‖log t‖) (Ioo (-X) X) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1
        (intervalIntegrable_log' (a := -X) (b := X)).norm
    have h2 : IntegrableOn (fun t => ‖log t‖ / X ^ 2) (Ioo (-X) X) := h1.div_const _
    simpa only [Real.norm_eq_abs] using h2
  have inner : ∀ t, ∫ x, F t x ∂μ = -log |t| * Abal X t := fun t => by
    simp only [hF, Abal, μ]; exact MeasureTheory.integral_const_mul _ _
  have innerNorm : ∀ t, |t| < X → ∫ x, ‖F t x‖ ∂μ = abs (log |t|) * Abal X t := fun t ht => by
    simp only [hF, Abal, μ]
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (kBal_nonneg ht hx)]
  have hint : Integrable (Function.uncurry F) (ν.prod μ) := by
    refine (integrable_prod_iff meas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hmem, hne0] with t ht ht0
      show Integrable (fun x => -log |t| * kBal X t x) μ
      exact ((kBal_integrals hX ht0 (abs_lt.2 ht)).1).const_mul _
    · refine Integrable.mono' hbound meas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hmem, hne0] with t ht ht0
      have ht' : |t| < X := abs_lt.2 ht
      obtain ⟨hA0, hA1⟩ := Abal_bounds hX ht0 ht'
      simp only [Function.uncurry_apply_pair]
      rw [innerNorm t ht', Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hA0),
        log_abs, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hA1 (abs_nonneg _)
  -- the left side is the `x`-outer iterated integral
  have hL : EqOn (fun x => tauBal X x / x ^ 2) (fun x => ∫ t, F t x ∂ν) (Ioi X) := by
    intro x hx
    simp only [tauBal, Ibal, hF, ν]
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have e : ∀ t, -log |t| * kBal X t x = (-1 / (π * √(x ^ 2 - X ^ 2) * x ^ 2)) *
        (√(X ^ 2 - t ^ 2) * log |t| / (x - t)) := fun t => by
      simp only [kBal, div_eq_mul_inv, mul_inv]; ring
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hLint := hint.integral_prod_right
  have hLint' : IntegrableOn (fun x => tauBal X x / x ^ 2) (Ioi X) :=
    hLint.congr ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun x hx => (hL hx).symm))
  refine ⟨hLint', ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hL]
  change ∫ x, ∫ t, F t x ∂ν ∂μ = _
  rw [← integral_integral_swap hint]
  simp only [inner]
  -- the right side: fold `t < 0` onto `t > 0`
  set g : ℝ → ℝ := fun t => -log |t| * Abal X t with hg
  have gint : IntegrableOn g (Ioo (-X) X) := by
    have := hint.integral_prod_left
    simp only [Function.uncurry_apply_pair, inner] at this
    exact this
  have hX' : -X ≤ X := by linarith
  change ∫ t in Ioo (-X) X, g t = _
  rw [setIntegral_Ioo_eq hX']
  have gneg : IntervalIntegrable g volume (-X) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2
      (gint.mono_set (Ioo_subset_Ioo le_rfl hX.le))
  have gpos : IntervalIntegrable g volume 0 X :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hX.le).2
      (gint.mono_set (Ioo_subset_Ioo (by linarith) le_rfl))
  have gneg' : IntervalIntegrable (fun t => g (-t)) volume 0 X := by
    have := (IntervalIntegrable.iff_comp_neg (f := g) (a := -X) (b := 0)).1 gneg
    simpa using this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals gneg gpos]
  have e1 : ∫ t in (-X)..0, g t = ∫ t in (0 : ℝ)..X, g (-t) := by
    rw [intervalIntegral.integral_comp_neg]; simp
  rw [e1, ← intervalIntegral.integral_add gneg' gpos, balayageSide]
  refine intervalIntegral.integral_congr_ae ?_
  have hneX : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ X := by simp [ae_iff, measure_singleton]
  filter_upwards [hneX] with t htX ht
  rw [uIoc_of_le hX.le] at ht
  have ht' : |t| < X := abs_lt.2 ⟨by linarith [ht.1], lt_of_le_of_ne ht.2 htX⟩
  obtain ⟨-, -, e⟩ := kBal_integrals hX ht.1.ne' ht'
  simp only [hg, Abal, abs_neg, abs_of_pos ht.1] at e ⊢
  rw [← e]; ring


/-! ## H. The reduced problem, unconditionally -/

/-- **The exterior moment of the reduced problem, with no hypothesis.** For every wall `X ≥ 1`, with
the paper's balayage density `τ = −I/(π√(x² − X²))`:
`∫_X^∞ x⁻²[ln x − τ(x)] dx = (π/(2X))(1 + ln(X/2))`. -/
theorem exteriorMoment_reduced {X : ℝ} (hX : 1 ≤ X) :
    ∫ x in Ioi X, (log x - tauBal X x) / x ^ 2 = π / (2 * X) * (1 + log (X / 2)) :=
  let h := balayage_identity (by linarith : (0 : ℝ) < X)
  exteriorMoment_eq hX h.1 h.2

/-- **`1/(16π)` in the reduced problem, with no hypothesis.** At the wall `X = 2`, with `T₀ = 2πe^δ`,
the exterior moment of the paper's balayage density divided by `2πT₀` is exactly `e^{−δ}/(16π)`. -/
theorem sixteenPi_reduced (δ : ℝ) :
    (∫ x in Ioi (2 : ℝ), (log x - tauBal 2 x) / x ^ 2) / (2 * π * (2 * π * exp δ))
      = exp (-δ) / (16 * π) :=
  let h := balayage_identity (two_pos : (0 : ℝ) < 2)
  sixteenPi_of_balayage δ h.1 h.2

/-- The paper's reduced exponent `f(X) = 2πX(1 + ln 2 − ln X)` (Theorem 1bm(iv)). -/
def fBalExp (X : ℝ) : ℝ := 2 * π * X * (1 + log 2 - log X)

/-- **The wall.** `f(X) ≤ 4π` for `X > 0`, with equality only at `X = 2`: the paper's maximiser
`X* = 2`, `f_∞ = 4π`. -/
theorem fBalExp_le {X : ℝ} (hX : 0 < X) : fBalExp X ≤ 4 * π ∧ (fBalExp X = 4 * π ↔ X = 2) := by
  set y := X / 2 with hy
  have hy0 : 0 < y := by positivity
  have hl : log X - log 2 = log y := (log_div hX.ne' two_ne_zero).symm
  have key : fBalExp X = 4 * π - 4 * π * (1 - y + y * log y) := by
    unfold fBalExp
    rw [show 1 + log 2 - log X = 1 - log y by rw [← hl]; ring, hy]; ring
  -- `y ln y ≥ y − 1`, strictly unless `y = 1`
  have weak : y - 1 ≤ y * log y := by
    have := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hy0) hy0.le
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hy0.ne'] at this
  refine ⟨by rw [key]; nlinarith [pi_pos], ⟨fun h => ?_, fun h => by subst h; unfold fBalExp; ring⟩⟩
  rw [key] at h
  have h0 : 1 - y + y * log y = 0 := by
    have := pi_pos
    have : 4 * π * (1 - y + y * log y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  by_contra hne
  have hy1 : y ≠ 1 := fun h1 => hne (by rw [hy] at h1; linarith)
  have hs := Real.log_lt_sub_one_of_pos (inv_pos.2 hy0) (fun h1 => hy1 (inv_eq_one.1 h1))
  rw [Real.log_inv] at hs
  have := mul_lt_mul_of_pos_left hs hy0
  rw [mul_sub, mul_inv_cancel₀ hy0.ne', mul_one] at this
  linarith


/-! ## I. The balayage density in closed form, and its positivity at the wall -/

theorem hasDerivAt_arcsin_comp {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t)
    (h1 : f t ≠ -1) (h2 : f t ≠ 1) :
    HasDerivAt (fun y => arcsin (f y)) (1 / √(1 - f t ^ 2) * f') t :=
  (hasDerivAt_arcsin h1 h2).comp t hf

theorem sqrt_eq_of_sq {a E : ℝ} (hE : 0 ≤ E) (h : a = E ^ 2) : √a = E := by
  rw [h, Real.sqrt_sq hE]

/-- `∫_{−X}^{X} √(X² − t²)/(x − t) dt = π(x − √(x² − X²))` for `x > X > 0`. -/
theorem integral_C0 {X x : ℝ} (hX : 0 < X) (hx : X < x) :
    ∫ t in (-X)..X, √(X ^ 2 - t ^ 2) / (x - t) = π * (x - √(x ^ 2 - X ^ 2)) := by
  set s := √(x ^ 2 - X ^ 2) with hs
  have hs2 : s ^ 2 = x ^ 2 - X ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  set H : ℝ → ℝ := fun t => x * arcsin (t / X) - √(X ^ 2 - t ^ 2)
    + s * arcsin ((X ^ 2 - x * t) / (X * (x - t))) with hH
  have hcont : ContinuousOn H (Icc (-X) X) := by
    refine ContinuousOn.add (by fun_prop) (continuousOn_const.mul
      (continuous_arcsin.comp_continuousOn (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)))
    intro t ht; exact mul_ne_zero hX.ne' (by linarith [ht.2])
  have hder : ∀ t ∈ Ioo (-X) X, HasDerivAt H (√(X ^ 2 - t ^ 2) / (x - t)) t := by
    intro t ⟨h1, h2⟩
    have hxt : 0 < x - t := by linarith
    have hw : 0 < X ^ 2 - t ^ 2 := by nlinarith
    have hw0 : 0 < √(X ^ 2 - t ^ 2) := Real.sqrt_pos.2 hw
    have hw2 : √(X ^ 2 - t ^ 2) ^ 2 = X ^ 2 - t ^ 2 := Real.sq_sqrt hw.le
    have hXxt : X * (x - t) ≠ 0 := mul_ne_zero hX.ne' hxt.ne'
    have d1 := hasDerivAt_arcsin_comp ((hasDerivAt_id t).div_const X)
      (by simp only [id]; rw [Ne, div_eq_iff hX.ne']; linarith)
      (by simp only [id]; rw [Ne, div_eq_iff hX.ne']; linarith)
    have d2 : HasDerivAt (fun y => √(X ^ 2 - y ^ 2)) (-(2 * t) / (2 * √(X ^ 2 - t ^ 2))) t := by
      convert ((hasDerivAt_pow 2 t).const_sub (X ^ 2)).sqrt hw.ne' using 1; norm_num
    have du : HasDerivAt (fun t => (X ^ 2 - x * t) / (X * (x - t)))
        (((0 - x * 1) * (X * (x - t)) - (X ^ 2 - x * t) * (X * (0 - 1))) / (X * (x - t)) ^ 2) t :=
      ((hasDerivAt_const t (X ^ 2)).sub ((hasDerivAt_id t).const_mul x)).div
        ((hasDerivAt_const t x).sub (hasDerivAt_id t) |>.const_mul X) hXxt
    have hu1 : (X ^ 2 - x * t) / (X * (x - t)) ≠ -1 := by
      rw [Ne, div_eq_iff hXxt]; intro h; nlinarith
    have hu2 : (X ^ 2 - x * t) / (X * (x - t)) ≠ 1 := by
      rw [Ne, div_eq_iff hXxt]; intro h; nlinarith
    have d3 := hasDerivAt_arcsin_comp du hu1 hu2
    have e1 : √(1 - (id t / X) ^ 2) = √(X ^ 2 - t ^ 2) / X :=
      sqrt_eq_of_sq (by positivity) (by simp only [id]; rw [div_pow, div_pow, hw2]; field_simp)
    have e2 : √(1 - ((X ^ 2 - x * t) / (X * (x - t))) ^ 2) = s * √(X ^ 2 - t ^ 2) / (X * (x - t)) :=
      sqrt_eq_of_sq (by positivity) (by
        have q : (s * √(X ^ 2 - t ^ 2) / (X * (x - t))) ^ 2 = (x ^ 2 - X ^ 2) * (X ^ 2 - t ^ 2) /
            (X * (x - t)) ^ 2 := by rw [div_pow, mul_pow, hw2, hs2]
        rw [q]; field_simp; ring)
    rw [e1] at d1
    rw [e2] at d3
    have := (d1.const_mul x).sub d2 |>.add (d3.const_mul s)
    convert this using 1
    · funext y; simp only [hH, Pi.add_apply, Pi.sub_apply, id]
    · field_simp
      linear_combination hw2
  rw [integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hder
    ((ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by
      rw [uIcc_of_le (by linarith)] at ht
      exact sub_ne_zero.2 (by linarith [ht.2] : t < x).ne').intervalIntegrable)]
  have a1 : (X ^ 2 - x * X) / (X * (x - X)) = -1 := by
    rw [div_eq_iff (mul_ne_zero hX.ne' (by linarith))]; ring
  have a2 : (X ^ 2 - x * -X) / (X * (x - -X)) = 1 := by
    rw [div_eq_iff (mul_ne_zero hX.ne' (by linarith))]; ring
  simp only [hH, a1, a2, div_self hX.ne', neg_div, arcsin_one, arcsin_neg, sub_self,
    Real.sqrt_zero, neg_sq]
  ring

/-- `∫_{−X}^{X} √(X² − t²)/(t² + v) dt = π(√(X² + v) − √v)/√v` for `v > 0`. -/
theorem integral_Dv {X v : ℝ} (hX : 0 < X) (hv : 0 < v) :
    ∫ t in (-X)..X, √(X ^ 2 - t ^ 2) / (t ^ 2 + v) = π * (√(X ^ 2 + v) - √v) / √v := by
  set R := √(X ^ 2 + v) with hR
  set r := √v with hr
  have hR2 : R ^ 2 = X ^ 2 + v := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = v := Real.sq_sqrt hv.le
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.2 hv
  set G : ℝ → ℝ := fun t => R / r * arcsin (t * R / (X * √(t ^ 2 + v))) - arcsin (t / X) with hG
  have hq : ∀ t : ℝ, 0 < √(t ^ 2 + v) := fun t => Real.sqrt_pos.2 (by positivity)
  have hcont : ContinuousOn G (Icc (-X) X) := by
    refine ContinuousOn.sub (continuousOn_const.mul (continuous_arcsin.comp_continuousOn
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun t _ => ?_))) (by fun_prop)
    exact mul_ne_zero hX.ne' (hq t).ne'
  have hder : ∀ t ∈ Ioo (-X) X, HasDerivAt G (√(X ^ 2 - t ^ 2) / (t ^ 2 + v)) t := by
    intro t ⟨h1, h2⟩
    have hw : 0 < X ^ 2 - t ^ 2 := by nlinarith
    have hw0 : 0 < √(X ^ 2 - t ^ 2) := Real.sqrt_pos.2 hw
    have hw2 : √(X ^ 2 - t ^ 2) ^ 2 = X ^ 2 - t ^ 2 := Real.sq_sqrt hw.le
    set q := √(t ^ 2 + v) with hqdef
    have hq0 : 0 < q := hq t
    have hq2 : q ^ 2 = t ^ 2 + v := Real.sq_sqrt (by positivity)
    have dq : HasDerivAt (fun y => √(y ^ 2 + v)) (2 * t / (2 * q)) t := by
      convert ((hasDerivAt_pow 2 t).add_const v).sqrt (by positivity : t ^ 2 + v ≠ 0) using 1; norm_num; rfl
    have du : HasDerivAt (fun y => y * R / (X * √(y ^ 2 + v)))
        ((1 * R * (X * q) - t * R * (X * (2 * t / (2 * q)))) / (X * q) ^ 2) t :=
      (((hasDerivAt_id t).mul_const R).div (dq.const_mul X) (mul_ne_zero hX.ne' hq0.ne'))
    have hlt : (t * R / (X * q)) ^ 2 < 1 := by
      rw [div_pow, mul_pow, mul_pow, hR2, hq2, div_lt_one (by positivity)]
      nlinarith
    have hu1 : t * R / (X * q) ≠ -1 := fun h => by rw [h] at hlt; norm_num at hlt
    have hu2 : t * R / (X * q) ≠ 1 := fun h => by rw [h] at hlt; norm_num at hlt
    have d3 := hasDerivAt_arcsin_comp du hu1 hu2
    have d1 := hasDerivAt_arcsin_comp ((hasDerivAt_id t).div_const X)
      (by simp only [id]; rw [Ne, div_eq_iff hX.ne']; linarith)
      (by simp only [id]; rw [Ne, div_eq_iff hX.ne']; linarith)
    have e1 : √(1 - (id t / X) ^ 2) = √(X ^ 2 - t ^ 2) / X :=
      sqrt_eq_of_sq (by positivity) (by simp only [id]; rw [div_pow, div_pow, hw2]; field_simp)
    have e3 : √(1 - (t * R / (X * q)) ^ 2) = r * √(X ^ 2 - t ^ 2) / (X * q) :=
      sqrt_eq_of_sq (by positivity) (by
        have e : (r * √(X ^ 2 - t ^ 2) / (X * q)) ^ 2 = v * (X ^ 2 - t ^ 2) / (X * q) ^ 2 := by
          rw [div_pow, mul_pow, hw2, hr2]
        rw [e, div_pow, mul_pow, mul_pow, hR2, hq2]; field_simp; ring)
    rw [e1] at d1
    rw [e3] at d3
    have := (d3.const_mul (R / r)).sub d1
    convert this using 1
    · funext y; simp only [hG, Pi.sub_apply, id]
    · field_simp
      simp only [hw2, hr2, hq2, hR2]
      ring
  rw [integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hder
    ((ContinuousOn.div (by fun_prop) (by fun_prop) fun t _ => by positivity).intervalIntegrable)]
  have a1 : X * R / (X * √(X ^ 2 + v)) = 1 := by rw [← hR]; field_simp
  have a2 : -X * R / (X * √((-X) ^ 2 + v)) = -1 := by rw [neg_sq, ← hR]; field_simp
  simp only [hG, a1, a2, div_self hX.ne', neg_div, arcsin_one, arcsin_neg]
  field_simp
  ring

/-- The odd part vanishes: `∫_{−X}^{X} t√(X² − t²)/(t² + v) dt = 0`. -/
theorem integral_Ev (X v : ℝ) : ∫ t in (-X)..X, t * √(X ^ 2 - t ^ 2) / (t ^ 2 + v) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -X) (b := X)
    (fun t => t * √(X ^ 2 - t ^ 2) / (t ^ 2 + v))
  simp only [neg_neg, neg_sq, neg_mul, neg_div, intervalIntegral.integral_neg] at h
  linarith

/-- For fixed `v > 0`: `∫_{−X}^{X} √(X² − t²)/(x − t)·(1/(1 + v) − 1/(t² + v)) dt`
`= C₀/(1 + v) − (C₀ + x·D(v))/(x² + v)`, with `C₀ = π(x − s)` and `D(v) = π(√(X² + v) − √v)/√v`. -/
theorem integral_Cv {X x v : ℝ} (hX : 0 < X) (hx : X < x) (hv : 0 < v) :
    ∫ t in (-X)..X, √(X ^ 2 - t ^ 2) / (x - t) * (1 / (1 + v) - 1 / (t ^ 2 + v))
      = (1 / (1 + v) - 1 / (x ^ 2 + v)) * (π * (x - √(x ^ 2 - X ^ 2)))
        - x / (x ^ 2 + v) * (π * (√(X ^ 2 + v) - √v) / √v) := by
  have hXX : -X ≤ X := by linarith
  have hne : ∀ t ∈ uIcc (-X) X, x - t ≠ 0 := fun t ht => by
    rw [uIcc_of_le hXX] at ht; exact sub_ne_zero.2 (by linarith [ht.2] : t < x).ne'
  have i1 : IntervalIntegrable (fun t => √(X ^ 2 - t ^ 2) / (x - t)) volume (-X) X :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) hne).intervalIntegrable
  have i2 : IntervalIntegrable (fun t => √(X ^ 2 - t ^ 2) / (t ^ 2 + v)) volume (-X) X :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun t _ => by positivity).intervalIntegrable
  have i3 : IntervalIntegrable (fun t => t * √(X ^ 2 - t ^ 2) / (t ^ 2 + v)) volume (-X) X :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun t _ => by positivity).intervalIntegrable
  have e : ∀ t ∈ uIcc (-X) X, √(X ^ 2 - t ^ 2) / (x - t) * (1 / (1 + v) - 1 / (t ^ 2 + v))
      = (1 / (1 + v) - 1 / (x ^ 2 + v)) * (√(X ^ 2 - t ^ 2) / (x - t))
        - x / (x ^ 2 + v) * (√(X ^ 2 - t ^ 2) / (t ^ 2 + v))
        - 1 / (x ^ 2 + v) * (t * √(X ^ 2 - t ^ 2) / (t ^ 2 + v)) := fun t ht => by
    have := hne t ht
    have : t ^ 2 + v ≠ 0 := by positivity
    field_simp; ring
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub
    ((i1.const_mul _).sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_C0 hX hx, integral_Dv hX hv, integral_Ev]
  ring

/-- **The logarithm as an integral**: for `c > 0`, `∫₀^∞ (1/(1 + v) − 1/(c + v)) dv = ln c`, the
integrand is integrable, and `∫₀^∞ |1/(1 + v) − 1/(c + v)| dv = |ln c|`. -/
theorem integral_logRep {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v => 1 / (1 + v) - 1 / (c + v)) (Ioi 0) ∧
      ∫ v in Ioi 0, (1 / (1 + v) - 1 / (c + v)) = log c ∧
      ∫ v in Ioi 0, |1 / (1 + v) - 1 / (c + v)| = |log c| := by
  set g : ℝ → ℝ := fun v => 1 / (1 + v) - 1 / (c + v) with hg
  have hder : ∀ v ∈ Ici (0 : ℝ), HasDerivAt (fun v => log (1 + v) - log (c + v)) (g v) v := by
    intro v hv
    have h1 : 0 < 1 + v := by linarith [hv.out]
    have h2 : 0 < c + v := by linarith [hv.out]
    have := (((hasDerivAt_id v).const_add 1).log h1.ne').sub (((hasDerivAt_id v).const_add c).log h2.ne')
    convert this using 1
    · funext y; simp only [Pi.sub_apply, id]
    · simp [hg]
  have hlim : Tendsto (fun v => log (1 + v) - log (c + v)) atTop (𝓝 0) := by
    have hr : Tendsto (fun v : ℝ => 1 - (c - 1) / (c + v)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := c - 1)).div_atTop (tendsto_atTop_add_const_left _ c tendsto_id)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    have hl := ((continuousAt_log one_ne_zero).tendsto.comp hr)
    rw [log_one] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    simp only [Function.comp]
    rw [← log_div (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hval : ∀ (hint : IntegrableOn g (Ioi 0)), ∫ v in Ioi 0, g v = log c := fun hint => by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hder hint hlim]; simp
  rcases le_total 1 c with h1 | h1
  · have hpos : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ g v := fun v hv => by
      simp only [hg]; rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by linarith [hv.out]) (by linarith)
    have hint := integrableOn_Ioi_deriv_of_nonneg' hder hpos hlim
    refine ⟨hint, hval hint, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => abs_of_nonneg (hpos v hv)), hval hint,
      abs_of_nonneg (log_nonneg h1)]
  · have hneg : ∀ v ∈ Ioi (0 : ℝ), g v ≤ 0 := fun v hv => by
      simp only [hg]; rw [sub_nonpos]
      exact one_div_le_one_div_of_le (by linarith [hv.out]) (by linarith)
    have hint : IntegrableOn g (Ioi 0) := by
      have := integrableOn_Ioi_deriv_of_nonneg' (g := fun v => -(log (1 + v) - log (c + v)))
        (fun v hv => (hder v hv).neg) (fun v hv => neg_nonneg.2 (hneg v hv))
        (by simpa using hlim.neg)
      simpa using this.neg
    refine ⟨hint, hval hint, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => abs_of_nonpos (hneg v hv)),
      MeasureTheory.integral_neg, hval hint, abs_of_nonpos (log_nonpos hc.le h1)]
/-- The antiderivative of `π(√(X² + v) − √v)/(√v(x² + v))`. -/
def Qprim (X x v : ℝ) : ℝ :=
  2 * π * (log (√v + √(X ^ 2 + v)) - log (x ^ 2 + v) / 2
    - √(x ^ 2 - X ^ 2) / (2 * x) * (log (x * √(X ^ 2 + v) + √(x ^ 2 - X ^ 2) * √v)
      - log (x * √(X ^ 2 + v) - √(x ^ 2 - X ^ 2) * √v)))

theorem Qarg_pos {X x v : ℝ} (hX : 0 < X) (hx : X < x) (hv : 0 ≤ v) :
    0 < x * √(X ^ 2 + v) - √(x ^ 2 - X ^ 2) * √v := by
  have hs2 : √(x ^ 2 - X ^ 2) ^ 2 = x ^ 2 - X ^ 2 := Real.sq_sqrt (by nlinarith)
  have hR2 : √(X ^ 2 + v) ^ 2 = X ^ 2 + v := Real.sq_sqrt (by positivity)
  have hr2 : √v ^ 2 = v := Real.sq_sqrt hv
  have hx0 : 0 < x := by linarith
  have hlt : (√(x ^ 2 - X ^ 2) * √v) ^ 2 < (x * √(X ^ 2 + v)) ^ 2 := by
    rw [mul_pow, mul_pow, hs2, hR2, hr2]; nlinarith [mul_pos hX hX]
  have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt
  linarith

theorem hasDerivAt_Qprim {X x v : ℝ} (hX : 0 < X) (hx : X < x) (hv : 0 < v) :
    HasDerivAt (Qprim X x) (π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v)) v := by
  set s := √(x ^ 2 - X ^ 2) with hs
  set R := √(X ^ 2 + v) with hR
  set r := √v with hr
  have hs2 : s ^ 2 = x ^ 2 - X ^ 2 := Real.sq_sqrt (by nlinarith)
  have hR2 : R ^ 2 = X ^ 2 + v := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = v := Real.sq_sqrt hv.le
  have hr0 : 0 < r := Real.sqrt_pos.2 hv
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hx0 : 0 < x := by linarith
  have hA : 0 < x * R - s * r := Qarg_pos hX hx hv.le
  have hB : 0 < x * R + s * r := by
    have : 0 ≤ s * r := mul_nonneg (Real.sqrt_nonneg _) hr0.le
    nlinarith
  have dr : HasDerivAt (fun v => √v) (1 / (2 * r)) v := by
    simpa using Real.hasDerivAt_sqrt hv.ne'
  have dR : HasDerivAt (fun v => √(X ^ 2 + v)) (1 / (2 * R)) v := by
    convert ((hasDerivAt_id v).const_add (X ^ 2)).sqrt (by positivity : X ^ 2 + v ≠ 0) using 1
    simp only [id]; rfl
  have d1 := (dr.add dR).log (by positivity : r + R ≠ 0)
  have d2 := ((hasDerivAt_id v).const_add (x ^ 2)).log (by positivity : x ^ 2 + v ≠ 0)
  have d3 := ((dR.const_mul x).add (dr.const_mul s)).log hB.ne'
  have d4 := ((dR.const_mul x).sub (dr.const_mul s)).log hA.ne'
  have := (((d1.sub (d2.div_const 2)).sub ((d3.sub d4).const_mul (s / (2 * x)))).const_mul (2 * π))
  convert this using 1
  · funext w; rfl
  · simp only [id, Pi.add_apply, Pi.sub_apply, ← hr, ← hR]
    have n1 : r + R ≠ 0 := by positivity
    have n2 := hA.ne'
    have n3 := hB.ne'
    have n2' : R * x - r * s ≠ 0 := by rw [mul_comm R, mul_comm r]; exact n2
    have n3' : R * x + r * s ≠ 0 := by rw [mul_comm R, mul_comm r]; exact n3
    field_simp
    have hsR : s ^ 2 = x ^ 2 - R ^ 2 + r ^ 2 := by rw [hs2, hR2, hr2]; ring
    rw [← hr2]
    linear_combination 2 * R ^ 2 * x ^ 3 * (R + r) * hsR

theorem continuousAt_Qprim {X x : ℝ} (hX : 0 < X) (hx : X < x) : ContinuousAt (Qprim X x) 0 := by
  have hx0 : 0 < x := by linarith
  unfold Qprim
  have h1 : ContinuousAt (fun v : ℝ => log (√v + √(X ^ 2 + v))) 0 :=
    ContinuousAt.log (by fun_prop) (by simp [Real.sqrt_sq hX.le, hX.ne'])
  have h2 : ContinuousAt (fun v : ℝ => log (x ^ 2 + v)) 0 :=
    ContinuousAt.log (by fun_prop) (by simp [hx0.ne'])
  have h3 : ContinuousAt (fun v : ℝ => log (x * √(X ^ 2 + v) + √(x ^ 2 - X ^ 2) * √v)) 0 :=
    ContinuousAt.log (by fun_prop) (by simp [Real.sqrt_sq hX.le, hX.ne', hx0.ne'])
  have h4 : ContinuousAt (fun v : ℝ => log (x * √(X ^ 2 + v) - √(x ^ 2 - X ^ 2) * √v)) 0 :=
    ContinuousAt.log (by fun_prop) (Qarg_pos hX hx le_rfl).ne'
  exact continuousAt_const.mul ((h1.sub (h2.div_const 2)).sub (continuousAt_const.mul (h3.sub h4)))

/-- The rescaled antiderivative `Ψ(ε)`, `Qprim(v) = 2πΨ(1/v)`. -/
def Psi (X x ε : ℝ) : ℝ :=
  log (1 + √(X ^ 2 * ε + 1)) - log (x ^ 2 * ε + 1) / 2
    - √(x ^ 2 - X ^ 2) / (2 * x) * (log (x * √(X ^ 2 * ε + 1) + √(x ^ 2 - X ^ 2))
      - log (x * √(X ^ 2 * ε + 1) - √(x ^ 2 - X ^ 2)))

theorem s_lt_x {X x : ℝ} (hX : 0 < X) (hx : X < x) : √(x ^ 2 - X ^ 2) < x := by
  rw [Real.sqrt_lt' (by linarith)]; nlinarith

theorem Qprim_eq_Psi {X x v : ℝ} (hX : 0 < X) (hx : X < x) (hv : 0 < v) :
    Qprim X x v = 2 * π * Psi X x v⁻¹ := by
  set s := √(x ^ 2 - X ^ 2) with hs
  have hx0 : 0 < x := by linarith
  have hsx := s_lt_x hX hx
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set a := √(X ^ 2 * v⁻¹ + 1) with ha
  have ha1 : 1 ≤ a := Real.one_le_sqrt.2 (by have := inv_pos.2 hv; nlinarith [sq_nonneg X])
  have hr0 : 0 < √v := Real.sqrt_pos.2 hv
  have hR : √(X ^ 2 + v) = √v * a := by
    rw [ha, ← Real.sqrt_mul hv.le]; congr 1; field_simp
  have hxv : x ^ 2 + v = v * (x ^ 2 * v⁻¹ + 1) := by field_simp
  have hlr : log √v = log v / 2 := Real.log_sqrt hv.le
  have p1 : 0 < x * a - s := by nlinarith
  unfold Qprim Psi
  rw [← hs, ← ha, hR, hxv,
    show √v + √v * a = √v * (1 + a) by ring,
    show x * (√v * a) + s * √v = √v * (x * a + s) by ring,
    show x * (√v * a) - s * √v = √v * (x * a - s) by ring,
    log_mul hr0.ne' (by positivity), log_mul hv.ne' (by positivity),
    log_mul hr0.ne' (by positivity), log_mul hr0.ne' p1.ne', hlr]
  ring

theorem tendsto_Qprim {X x : ℝ} (hX : 0 < X) (hx : X < x) :
    Tendsto (Qprim X x) atTop (𝓝 (2 * π * (log 2 - √(x ^ 2 - X ^ 2) / (2 * x) *
      (log (x + √(x ^ 2 - X ^ 2)) - log (x - √(x ^ 2 - X ^ 2)))))) := by
  have hx0 : 0 < x := by linarith
  have hsx := s_lt_x hX hx
  have hPsi : ContinuousAt (Psi X x) 0 := by
    unfold Psi
    have h1 : ContinuousAt (fun ε : ℝ => log (1 + √(X ^ 2 * ε + 1))) 0 :=
      ContinuousAt.log (by fun_prop) (by norm_num)
    have h2 : ContinuousAt (fun ε : ℝ => log (x ^ 2 * ε + 1)) 0 :=
      ContinuousAt.log (by fun_prop) (by norm_num)
    have h3 : ContinuousAt (fun ε : ℝ => log (x * √(X ^ 2 * ε + 1) + √(x ^ 2 - X ^ 2))) 0 :=
      ContinuousAt.log (by fun_prop) (by simp; positivity)
    have h4 : ContinuousAt (fun ε : ℝ => log (x * √(X ^ 2 * ε + 1) - √(x ^ 2 - X ^ 2))) 0 :=
      ContinuousAt.log (by fun_prop) (by simp; linarith)
    exact (h1.sub (h2.div_const 2)).sub (continuousAt_const.mul (h3.sub h4))
  have hv0 : Psi X x 0 = log 2 - √(x ^ 2 - X ^ 2) / (2 * x) *
      (log (x + √(x ^ 2 - X ^ 2)) - log (x - √(x ^ 2 - X ^ 2))) := by
    unfold Psi; norm_num
  rw [← hv0]
  have := (hPsi.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))).const_mul (2 * π)
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with v hv
  simp only [Function.comp]; rw [Qprim_eq_Psi hX hx hv]

/-- **The `v`-integral**: `∫₀^∞ π(√(X² + v) − √v)/(√v(x² + v)) dv`
`= 2π[ln 2 − ln X + ln x − (s/(2x))(ln(x + s) − ln(x − s))]`, with integrability. -/
theorem integral_Qv {X x : ℝ} (hX : 0 < X) (hx : X < x) :
    IntegrableOn (fun v => π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v)) (Ioi 0) ∧
      ∫ v in Ioi 0, π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v)
        = 2 * π * (log 2 - log X + log x - √(x ^ 2 - X ^ 2) / (2 * x) *
          (log (x + √(x ^ 2 - X ^ 2)) - log (x - √(x ^ 2 - X ^ 2)))) := by
  have hx0 : 0 < x := by linarith
  have hcont := (continuousAt_Qprim hX hx).continuousWithinAt (s := Ici 0)
  have hder : ∀ v ∈ Ioi (0 : ℝ), HasDerivAt (Qprim X x)
      (π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v)) v := fun v hv => hasDerivAt_Qprim hX hx hv
  have hpos : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v) := fun v hv => by
    have : √v ≤ √(X ^ 2 + v) := Real.sqrt_le_sqrt (by nlinarith)
    have := hv.out
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hder hpos (tendsto_Qprim hX hx), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos (tendsto_Qprim hX hx)]
  have q0 : Qprim X x 0 = 2 * π * (log X - log x) := by
    unfold Qprim
    simp only [Real.sqrt_zero, add_zero, zero_add, mul_zero, sub_zero, Real.sqrt_sq hX.le,
      sub_self, mul_zero, Real.log_pow]
    push_cast; ring
  rw [q0]; ring


/-- **The Cauchy integral in closed form.** For `x > X > 0`, with `s = √(x² − X²)`:
`I(x) = πx ln X − πx ln 2 − πs ln x + (πs/2)(ln(x + s) − ln(x − s))`. -/
theorem Ibal_closed {X x : ℝ} (hX : 0 < X) (hx : X < x) :
    Ibal X x = π * x * log X - π * x * log 2 - π * √(x ^ 2 - X ^ 2) * log x
      + π * √(x ^ 2 - X ^ 2) / 2 * (log (x + √(x ^ 2 - X ^ 2)) - log (x - √(x ^ 2 - X ^ 2))) := by
  set s := √(x ^ 2 - X ^ 2) with hs
  have hx0 : 0 < x := by linarith
  set ν : Measure ℝ := volume.restrict (Ioo (-X) X)
  set μ : Measure ℝ := volume.restrict (Ioi 0)
  set F : ℝ → ℝ → ℝ := fun t v => √(X ^ 2 - t ^ 2) / (x - t) * (1 / (1 + v) - 1 / (t ^ 2 + v))
    with hF
  have hne0 : ∀ᵐ t ∂ν, t ≠ 0 := ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hmem : ∀ᵐ t ∂ν, t ∈ Ioo (-X) X := ae_restrict_mem measurableSet_Ioo
  have meas : Measurable (Function.uncurry F) := by
    change Measurable fun p : ℝ × ℝ =>
      √(X ^ 2 - p.1 ^ 2) / (x - p.1) * (1 / (1 + p.2) - 1 / (p.1 ^ 2 + p.2))
    fun_prop
  have kpos : ∀ t ∈ Ioo (-X) X, 0 ≤ √(X ^ 2 - t ^ 2) / (x - t) := fun t ht =>
    div_nonneg (Real.sqrt_nonneg _) (by linarith [ht.2])
  have kle : ∀ t ∈ Ioo (-X) X, √(X ^ 2 - t ^ 2) / (x - t) ≤ X / (x - X) := fun t ht => by
    have h1 : √(X ^ 2 - t ^ 2) ≤ X := by
      rw [Real.sqrt_le_left (by nlinarith [ht.1, ht.2])]; nlinarith
    exact div_le_div₀ hX.le h1 (by linarith) (by linarith [ht.2])
  have inner : ∀ t, t ≠ 0 → ∫ v, F t v ∂μ = √(X ^ 2 - t ^ 2) / (x - t) * log (t ^ 2) := fun t ht => by
    simp only [hF, μ]
    rw [MeasureTheory.integral_const_mul, (integral_logRep (by positivity : 0 < t ^ 2)).2.1]
  have hbound : IntegrableOn (fun t => X / (x - X) * (2 * |log t|)) (Ioo (-X) X) := by
    have h1 : IntegrableOn (fun t => ‖log t‖) (Ioo (-X) X) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1
        (intervalIntegrable_log' (a := -X) (b := X)).norm
    have h2 : IntegrableOn (fun t => X / (x - X) * (2 * ‖log t‖)) (Ioo (-X) X) :=
      (h1.const_mul 2).const_mul _
    simpa only [Real.norm_eq_abs] using h2
  have hint : Integrable (Function.uncurry F) (ν.prod μ) := by
    refine (integrable_prod_iff meas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hne0] with t ht0
      show Integrable (fun v => √(X ^ 2 - t ^ 2) / (x - t) * (1 / (1 + v) - 1 / (t ^ 2 + v))) μ
      exact (integral_logRep (by positivity : 0 < t ^ 2)).1.const_mul _
    · refine Integrable.mono' hbound meas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hmem, hne0] with t ht ht0
      have hn : ∫ v, ‖F t v‖ ∂μ = √(X ^ 2 - t ^ 2) / (x - t) * (2 * |log t|) := by
        simp only [hF, norm_mul, Real.norm_eq_abs, abs_of_nonneg (kpos t ht)]
        rw [MeasureTheory.integral_const_mul, (integral_logRep (by positivity : 0 < t ^ 2)).2.2,
          Real.log_pow, abs_mul]
        norm_num
      simp only [Function.uncurry_apply_pair]
      rw [hn, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kpos t ht) (by positivity))]
      exact mul_le_mul_of_nonneg_right (kle t ht) (by positivity)
  have swap := integral_integral_swap hint
  -- left: `2·I(x)`
  have hXX : -X ≤ X := by linarith
  have hL : ∫ t, ∫ v, F t v ∂μ ∂ν = 2 * Ibal X x := by
    rw [MeasureTheory.integral_congr_ae (g := fun t => 2 * (√(X ^ 2 - t ^ 2) * log |t| / (x - t))) (by
      filter_upwards [hne0] with t ht0
      rw [inner t ht0, Real.log_pow, ← Real.log_abs t]; push_cast; ring),
      MeasureTheory.integral_const_mul, Ibal, intervalIntegral.integral_of_le hXX,
      integral_Ioc_eq_integral_Ioo]
  -- right: the `v`-integral of `C(v)`
  obtain ⟨iQ, eQ⟩ := integral_Qv hX hx
  obtain ⟨iL, eL, -⟩ := integral_logRep (by positivity : 0 < x ^ 2)
  have hR : ∫ v, ∫ t, F t v ∂ν ∂μ
      = π * (x - s) * log (x ^ 2) - x * (2 * π * (log 2 - log X + log x - s / (2 * x) *
          (log (x + s) - log (x - s)))) := by
    have e : ∀ v ∈ Ioi (0 : ℝ), ∫ t, F t v ∂ν
        = π * (x - s) * (1 / (1 + v) - 1 / (x ^ 2 + v))
          - x * (π * (√(X ^ 2 + v) - √v) / √v / (x ^ 2 + v)) := fun v hv => by
      simp only [hF, ν]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hXX,
        integral_Cv hX hx hv.out]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub (iL.const_mul _) (iQ.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, eL, eQ]
  rw [hL] at swap
  rw [hR] at swap
  rw [Real.log_pow] at swap
  push_cast at swap
  have h2 : Ibal X x = (π * (x - s) * (2 * log x) - x * (2 * π * (log 2 - log X + log x - s / (2 * x) *
          (log (x + s) - log (x - s))))) / 2 := by linarith
  rw [h2]; field_simp; ring

/-- **The balayage density in closed form.** For `x > X > 0`, with `s = √(x² − X²)`:
`τ(x) = ln(Xx/(x + s)) − x ln(X/2)/s`. -/
theorem tauBal_closed {X x : ℝ} (hX : 0 < X) (hx : X < x) :
    tauBal X x = log (X * x / (x + √(x ^ 2 - X ^ 2))) - x * log (X / 2) / √(x ^ 2 - X ^ 2) := by
  set s := √(x ^ 2 - X ^ 2) with hs
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  have hs2 : s ^ 2 = x ^ 2 - X ^ 2 := Real.sq_sqrt (by nlinarith)
  have hsx : s < x := s_lt_x hX hx
  have hprod : log (x + s) + log (x - s) = 2 * log X := by
    rw [← log_mul (by positivity) (by linarith), show (x + s) * (x - s) = X ^ 2 by nlinarith,
      Real.log_pow]; push_cast; ring
  unfold tauBal
  rw [Ibal_closed hX hx, ← hs, log_div (by positivity) (by positivity), log_mul hX.ne' hx0.ne',
    log_div hX.ne' two_ne_zero]
  have hL : log (x - s) = 2 * log X - log (x + s) := by linarith
  rw [hL]
  field_simp
  ring

/-- **Admissibility at the wall, proved.** At `X = 2`, `τ(x) = ln(2x/(x + √(x² − 4))) > 0` for every
`x > 2`: the balayage is a positive density on the whole exterior. -/
theorem tauBal_two {x : ℝ} (hx : 2 < x) :
    tauBal 2 x = log (2 * x / (x + √(x ^ 2 - 4))) ∧ 0 < tauBal 2 x := by
  have h := tauBal_closed two_pos hx
  norm_num at h
  refine ⟨h, ?_⟩
  rw [h]
  have hsx := s_lt_x two_pos hx
  norm_num at hsx
  exact log_pos (by rw [one_lt_div (by positivity)]; linarith)

end Pilot1ca

#print axioms Pilot1ca.wall_eq_iff
#print axioms Pilot1ca.wall_quadratic
#print axioms Pilot1ca.tau_at_wall
#print axioms Pilot1ca.integral_log_div_sq_Ioi
#print axioms Pilot1ca.P_eq
#print axioms Pilot1ca.Q_eq
#print axioms Pilot1ca.balayageSide_eq
#print axioms Pilot1ca.J_eq
#print axioms Pilot1ca.sixteenPi_of_balayage
#print axioms Pilot1ca.inv_sq_sub_le
#print axioms Pilot1ca.defect_eq_tail_of_D
#print axioms Pilot1ca.defect_sub_tail_le
#print axioms Pilot1ca.multiplier_expansion
#print axioms Pilot1ca.kBal_integrals
#print axioms Pilot1ca.balayage_identity
#print axioms Pilot1ca.exteriorMoment_reduced
#print axioms Pilot1ca.sixteenPi_reduced
#print axioms Pilot1ca.fBalExp_le
#print axioms Pilot1ca.integral_C0
#print axioms Pilot1ca.integral_Dv
#print axioms Pilot1ca.integral_logRep
#print axioms Pilot1ca.integral_Qv
#print axioms Pilot1ca.Ibal_closed
#print axioms Pilot1ca.tauBal_closed
#print axioms Pilot1ca.tauBal_two
