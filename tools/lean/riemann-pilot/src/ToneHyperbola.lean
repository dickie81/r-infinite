import ResponseKernel

/-!
# The tone law as hyperbolic geometry (rounds 114–116)

Unconditional: no hypothesis about ζ, RH or any `L`-function appears anywhere below.

Round 114 derived the kernel phase `K̃(r) = r log 2r − r + √(r² − 1) − r arcosh r` beyond the wall `r > 1`.
Round 113's `ToneCalc` reduced a tone to the stationarity condition `K'(r) = log(2qr/p)` and the Legendre form
`4π[r(1 + log(p/2qr)) + K(r)]`. Here, for the conductor-`q` kernel `K_q(r) = K̃(qr)/q`:

* `hasDerivAt_Kt`: `K̃'(r) = log 2r − arcosh r`;
* `stationary_iff`: stationarity holds iff `qr = cosh(log p)`, i.e. the prime acts at rapidity `log p`;
* `tone_law`: the tone at that point is exactly `2π(p − 1/p)/q`;
* `on_hyperbola`: `(qr*)² − (qω/4π)² = 1`, i.e. every tone lies on the unit hyperbola (the window's wall at `ρ = 1`);
* `boost_mul`, `tone_mul`, `tone_div`: products and ratios compose by adding and subtracting rapidities
  (a Lorentz boost), not by adding frequencies;
* `tone_mul_gt`: the product line is strictly above the sum of the tones, so the two readings are distinguishable;
* `stirling_scaling`, `stirling_deriv`: the leading Stirling phase `(γ/2) log(qγ/2πe)` equals the `q = 1` phase at
  `qγ`, divided by `q`. Its derivative is exactly `ToneCalc`'s hypothesis `log(qγ/2π)/2`. The Γ-shift
  (¼ even, ¾ odd) does not occur in it.
* `multiplier_deriv`: the inside-wall multiplier `w arcsin w + √(1 − w²) − 1` has derivative `arcsin w`.

Not formalised here (these remain numerical findings or classical inputs):
* that the chain's first-order response has this phase;
* the Stirling error term for `Im log Γ(a + iγ/2)`;
* the round-77 integral identity for the multiplier;
* the lemma that the `L` kernel is `K̃(qr)/q`, as opposed to that form being assumed.
-/

open Real

namespace ToneHyperbola

/-- The round-114 kernel phase. -/
noncomputable def Kt (r : ℝ) : ℝ := r * log (2 * r) - r + √(r ^ 2 - 1) - r * arcosh r

theorem hasDerivAt_Kt {r : ℝ} (hr : 1 < r) : HasDerivAt Kt (log (2 * r) - arcosh r) r := by
  have r0 : 0 < r := by linarith
  have hs : 0 < r ^ 2 - 1 := by nlinarith
  have hsq : 0 < √(r ^ 2 - 1) := sqrt_pos.mpr hs
  have h1 : HasDerivAt (fun y => y * log (2 * y)) (1 * log (2 * r) + r * ((2 * 1) / (2 * r))) r := by
    have hl : HasDerivAt (fun y => log (2 * y)) ((2 * 1) / (2 * r)) r :=
      ((hasDerivAt_id r).const_mul 2).log (by simp; positivity)
    exact (hasDerivAt_id r).mul hl
  have h2 : HasDerivAt (fun y => √(y ^ 2 - 1)) ((2 * r ^ 1 * 1 - 0) / (2 * √(r ^ 2 - 1))) r := by
    have hp : HasDerivAt (fun y => y ^ 2 - 1) (2 * r ^ 1 * 1 - 0) r :=
      ((hasDerivAt_id r).pow 2).sub (hasDerivAt_const r 1)
    exact hp.sqrt hs.ne'
  have h3 : HasDerivAt (fun y => y * arcosh y) (1 * arcosh r + r * (√(r ^ 2 - 1))⁻¹) r :=
    (hasDerivAt_id r).mul (hasDerivAt_arcosh hr)
  have := ((h1.sub (hasDerivAt_id r)).add h2).sub h3
  convert this using 1
  · funext y; rfl
  · field_simp; ring

/-- Stationarity (in `ToneCalc.stationary_iff`'s form) for `K_q(r) = K̃(qr)/q`, whose derivative is `K̃'(qr)`:
it holds exactly at `qr = cosh(log p)`. -/
theorem stationary_iff {p q r : ℝ} (hp : 1 < p) (hq : 0 < q) (hρ : 1 < q * r) :
    log (2 * (q * r)) - arcosh (q * r) = log (2 * q * r / p) ↔ q * r = cosh (log p) := by
  have r0 : 0 < r := by
    by_contra h; push Not at h; nlinarith
  rw [log_div (by positivity) (by linarith), show 2 * q * r = 2 * (q * r) by ring]
  constructor
  · intro h
    have : arcosh (q * r) = log p := by linarith
    rw [← this, cosh_arcosh hρ.le]
  · intro h
    rw [h, arcosh_cosh (log_nonneg hp.le)]

/-- The tone law: at the stationary point, the Legendre form of `K_q` equals `2π(p − 1/p)/q`. -/
theorem tone_eq {p q r : ℝ} (hp : 1 < p) (hq : 0 < q) (hρ : q * r = cosh (log p)) :
    4 * π * (r * (1 + log (p / (2 * q * r))) + Kt (q * r) / q) = 2 * π * (p - p⁻¹) / q := by
  have p0 : 0 < p := by linarith
  set η := log p with hη
  have hη0 : 0 ≤ η := log_nonneg hp.le
  have hsinh : 0 ≤ sinh η := sinh_nonneg_iff.mpr hη0
  have hc : 1 ≤ cosh η := one_le_cosh η
  have hsq : √((q * r) ^ 2 - 1) = sinh η := by
    rw [hρ, show cosh η ^ 2 - 1 = sinh η ^ 2 by rw [cosh_sq]; ring, sqrt_sq hsinh]
  have hac : arcosh (q * r) = η := by rw [hρ, arcosh_cosh hη0]
  have hr : r = cosh η / q := by field_simp; linarith
  have hlog : log (p / (2 * q * r)) = η - log (2 * (q * r)) := by
    rw [log_div p0.ne' (by rw [show 2 * q * r = 2 * (q * r) by ring, hρ]; positivity),
      show 2 * q * r = 2 * (q * r) by ring]
  have hsl : sinh η = (p - p⁻¹) / 2 := by rw [hη, sinh_log p0]
  unfold Kt
  rw [hlog, hsq, hac]
  rw [show 4 * π * (r * (1 + (η - log (2 * (q * r)))) +
      (q * r * log (2 * (q * r)) - q * r + sinh η - q * r * η) / q) = 4 * π * sinh η / q by
    field_simp; ring]
  rw [hsl]; field_simp; ring

/-- `K_q(r) = K̃(qr)/q` has derivative `K̃'(qr)` beyond its wall `qr > 1`. -/
theorem hasDerivAt_Kq {q r : ℝ} (hq : 0 < q) (hρ : 1 < q * r) :
    HasDerivAt (fun y => Kt (q * y) / q) (log (2 * (q * r)) - arcosh (q * r)) r := by
  have hin : HasDerivAt (fun y => q * y) q r := by simpa using (hasDerivAt_id r).const_mul q
  have := ((hasDerivAt_Kt hρ).comp r hin).div_const q
  convert this using 1
  · funext y; rfl
  · field_simp

/-- **The tone law, assembled with round 113's `ToneCalc`.** For the kernel `K_q(r) = K̃(qr)/q`: at the point
where the γ-derivative vanishes, the x-rate `4π(r + K_q(r) − r K_q'(r))` is exactly `2π(p − 1/p)/q`. -/
theorem tone_law {p q r : ℝ} (hp : 1 < p) (hq : 0 < q) (hρ : 1 < q * r)
    (hstat : log (2 * (q * r)) - arcosh (q * r) + log p - log (2 * q * r) = 0) :
    q * r = cosh (log p) ∧
      4 * π * (r + Kt (q * r) / q - r * (log (2 * (q * r)) - arcosh (q * r))) = 2 * π * (p - p⁻¹) / q := by
  have r0 : 0 < r := by
    by_contra h; push Not at h; nlinarith
  have hk := (ToneCalc.stationary_iff (by linarith : (0:ℝ) < p) hq r0).mp hstat
  have hc := (stationary_iff hp hq hρ).mp hk
  refine ⟨hc, ?_⟩
  rw [ToneCalc.tone_at_stationary (by linarith : (0:ℝ) < p) hq r0 hk]
  exact tone_eq hp hq hc

/-- The tone and its stationary point lie on the unit hyperbola: `(qr*)² − (qω/4π)² = 1`. -/
theorem on_hyperbola {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (cosh (log p)) ^ 2 - (q * (2 * π * (p - p⁻¹) / q) / (4 * π)) ^ 2 = 1 := by
  have : q * (2 * π * (p - p⁻¹) / q) / (4 * π) = sinh (log p) := by
    rw [sinh_log hp]; field_simp; ring
  rw [this, cosh_sq]; ring

/-- The tone of `n` at conductor `q`. -/
noncomputable def tone (q n : ℝ) : ℝ := 2 * π * (n - n⁻¹) / q

theorem tone_eq_sinh {q n : ℝ} (hn : 0 < n) : tone q n = 4 * π * sinh (log n) / q := by
  unfold tone; rw [sinh_log hn]; ring

/-- Composition is a Lorentz boost: the stationary point and tone of `mn` are those of `n` boosted by rapidity
`log m`. -/
theorem boost_mul {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    cosh (log (m * n)) = cosh (log m) * cosh (log n) + sinh (log m) * sinh (log n) ∧
      sinh (log (m * n)) = sinh (log m) * cosh (log n) + cosh (log m) * sinh (log n) := by
  rw [log_mul hm.ne' hn.ne']; exact ⟨cosh_add _ _, sinh_add _ _⟩

/-- Rapidities add: the product line is `4π sinh(log m + log n)/q`. -/
theorem tone_mul {q m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    tone q (m * n) = 4 * π * sinh (log m + log n) / q := by
  rw [tone_eq_sinh (mul_pos hm hn), log_mul hm.ne' hn.ne']

/-- Rapidities subtract for ratio (conjugate-product) lines. -/
theorem tone_div {q m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    tone q (m / n) = 4 * π * sinh (log m - log n) / q := by
  rw [tone_eq_sinh (div_pos hm hn), log_div hm.ne' hn.ne']

/-- The product line lies strictly above the sum of the tones: rapidity addition is not frequency addition. -/
theorem tone_mul_gt {q m n : ℝ} (hq : 0 < q) (hm : 1 < m) (hn : 1 < n) :
    tone q m + tone q n < tone q (m * n) := by
  unfold tone
  have m0 : 0 < m := by linarith
  have n0 : 0 < n := by linarith
  rw [← add_div, div_lt_div_iff_of_pos_right hq, ← mul_add]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have key : (m * n - (m * n)⁻¹) - ((m - m⁻¹) + (n - n⁻¹)) = (m - 1) * (n - 1) * (1 - (m * n)⁻¹) := by
    field_simp; ring
  have : 0 < (m - 1) * (n - 1) * (1 - (m * n)⁻¹) := by
    have : (m * n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have := mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn); nlinarith
  linarith

/-- The leading Stirling phase of `θ_χ` with conductor `q`: `(γ/2) log(qγ/(2πe))`. -/
noncomputable def stirl (q γ : ℝ) : ℝ := γ / 2 * log (q * γ / (2 * π * exp 1))

/-- Conductor scaling: the conductor-`q` phase at `γ` is the `q = 1` phase at `qγ`, divided by `q`. -/
theorem stirling_scaling {q γ : ℝ} (hq : 0 < q) : stirl q γ = stirl 1 (q * γ) / q := by
  unfold stirl; field_simp

/-- The leading Stirling phase satisfies `ToneCalc.hasDerivAt_gamma`'s hypothesis exactly:
`θ'(γ) = log(qγ/2π)/2`. -/
theorem stirling_deriv {q γ : ℝ} (hq : 0 < q) (hγ : 0 < γ) :
    HasDerivAt (stirl q) (log (q * γ / (2 * π)) / 2) γ := by
  have hpos : 0 < q * γ / (2 * π * exp 1) := by positivity
  have hin : HasDerivAt (fun g => q * g / (2 * π * exp 1)) (q * 1 / (2 * π * exp 1)) γ :=
    ((hasDerivAt_id γ).const_mul q).div_const _
  have hl := hin.log hpos.ne'
  have := ((hasDerivAt_id γ).div_const 2).mul hl
  have hle : log (q * γ / (2 * π * exp 1)) = log (q * γ / (2 * π)) - 1 := by
    rw [show q * γ / (2 * π * exp 1) = (q * γ / (2 * π)) / exp 1 by field_simp, log_div (by positivity)
      (exp_pos 1).ne', log_exp]
  unfold stirl
  convert this using 1
  · funext y; rfl
  · simp only [id]; rw [hle]; field_simp; ring

/-- The multiplier inside the wall: `d/dw [w arcsin w + √(1 − w²) − 1] = arcsin w` for `|w| < 1`. -/
theorem multiplier_deriv {w : ℝ} (h1 : -1 < w) (h2 : w < 1) :
    HasDerivAt (fun v => v * arcsin v + √(1 - v ^ 2) - 1) (arcsin w) w := by
  have hs : 0 < 1 - w ^ 2 := by nlinarith
  have ha := (hasDerivAt_id w).mul (hasDerivAt_arcsin h1.ne' h2.ne)
  have hq : HasDerivAt (fun v => √(1 - v ^ 2)) ((0 - 2 * w ^ 1 * 1) / (2 * √(1 - w ^ 2))) w :=
    ((hasDerivAt_const w (1:ℝ)).sub ((hasDerivAt_id w).pow 2)).sqrt hs.ne'
  have := (ha.add hq).sub (hasDerivAt_const w (1:ℝ))
  have hsq : 0 < √(1 - w ^ 2) := sqrt_pos.mpr hs
  convert this using 1
  · funext v; rfl
  · simp only [id_eq]; field_simp; ring

end ToneHyperbola

#print axioms ToneHyperbola.hasDerivAt_Kt
#print axioms ToneHyperbola.stationary_iff
#print axioms ToneHyperbola.tone_eq
#print axioms ToneHyperbola.hasDerivAt_Kq
#print axioms ToneHyperbola.tone_law
#print axioms ToneHyperbola.on_hyperbola
#print axioms ToneHyperbola.tone_eq_sinh
#print axioms ToneHyperbola.boost_mul
#print axioms ToneHyperbola.tone_mul
#print axioms ToneHyperbola.tone_div
#print axioms ToneHyperbola.tone_mul_gt
#print axioms ToneHyperbola.stirling_scaling
#print axioms ToneHyperbola.stirling_deriv
#print axioms ToneHyperbola.multiplier_deriv
