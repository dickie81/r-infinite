import Mathlib
import Curvature

/-! # The constant `1/(16π)`: the formal content of the strip note's §3.4

The owner's working note (`riemann-strip-target-note.md` §3.4) derives the pilot's Gaussian-multiplier
time `τ_a = e^{−δ}/(16π)` (README rounds 70–73) within the paper's reduced balayage problem. This file
proves everything in that derivation except the balayage identity itself.

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

**Not formalised:** the balayage identity `∫_X^∞ x⁻² τ(x) dx = ∫₀^X (−ln t) h_X(t) dt` — harmonic
measure of the doubly slit plane, `exteriorMoment_eq`'s hypothesis `hbal` — and everything the note
lists as its inputs (vii)(a)–(d): Hypothesis D at the wall, the reduction's five lemmas, the wall at
the maximiser, the continuum limit. Nothing here bears on RH.
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

theorem sin_image_Ioo : sin '' Ioo 0 (π / 2) = Ioo 0 1 := by
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
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← sin_image_Ioo,
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
satisfies the balayage identity `∫_X^∞ x⁻² τ = ∫₀^X (−ln t) h_X(t) dt` (harmonic measure; not
formalised here), then `∫_X^∞ x⁻²[ln x − τ(x)] dx = (π/(2X))(1 + ln(X/2))`. -/
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
