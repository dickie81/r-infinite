/-
# The ball tower from integers and primes (round 183, formalised in round 184)

Plain statement of what this file proves.

* **The tower.** `ballVol n = √π ^ n / Γ(n/2 + 1)` is the volume of the unit ball in `ℝⁿ`: it is exactly
  Mathlib's `EuclideanSpace.volume_ball` (`ballVol_eq_volume`). `sphereArea n = n · ballVol n` is the area
  of the unit sphere `S^{n-1}`.
* **The two tower maxima.** Among all whole-number dimensions the ball volume is largest at `n = 5`
  (`ballVol_lt_five`) and the sphere area is largest at `n = 7`, i.e. on `S⁶` (`sphereArea_lt_seven`).
  Both follow from the two-step recurrences `ballVol (n+2) = 2π/(n+2) · ballVol n` and
  `sphereArea (n+2) = 2π/n · sphereArea n`, plus `π < 3.15`.
* **Primes plus the integers' mirror symmetry force the tower as the completing factor.** Mathlib
  supplies `ζ(s) = ∏_p (1 - p^{-s})⁻¹` (the primes) and `Λ(1 - s) = Λ(s)` for
  `Λ = Gammaℝ · ζ` (the functional equation, proved in Mathlib from Poisson summation on ℤ). We prove:
  if another factor `h · Gammaℝ`, with `h` entire, zero-free and of growth order below 2, also makes
  `ζ` symmetric, then `h` is constant (`completing_factor_unique`). And `Gammaℝ(n) · sphereArea n = 2`
  (`Gammaℝ_mul_sphereArea`): the forced factor is twice the reciprocal sphere area.

What this file does NOT prove: the integer-counting route (round 183, Step 1) and the Tauberian step
(Step 2) are checked numerically only; Part 0's thresholds `19` and `217` and its "no fifth" claim are
not touched.
-/
import Mathlib

open Real Complex Metric Filter Topology

namespace BallTower

/-! ## Part A: the tower and its two maxima -/

/-- Volume of the unit ball in `ℝⁿ`. -/
noncomputable def ballVol (n : ℕ) : ℝ := √π ^ n / Real.Gamma (n / 2 + 1)

/-- Area of the unit sphere `S^{n-1}` bounding it. -/
noncomputable def sphereArea (n : ℕ) : ℝ := n * ballVol n

lemma ballVol_pos (n : ℕ) : 0 < ballVol n := by
  unfold ballVol
  exact div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

/-- `ballVol` is Mathlib's volume of the Euclidean unit ball. -/
theorem ballVol_eq_volume (n : ℕ) [NeZero n] :
    (MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = ballVol n := by
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (ballVol_pos n).le

/-- The two-step recurrence: `ballVol (n+2) = 2π/(n+2) · ballVol n`. -/
lemma ballVol_add_two (n : ℕ) : ballVol (n + 2) = 2 * π / (n + 2) * ballVol n := by
  unfold ballVol
  have hG : Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1) = ((n : ℝ) / 2 + 1) * Real.Gamma (n / 2 + 1) := by
    rw [show ((n + 2 : ℕ) : ℝ) / 2 + 1 = ((n : ℝ) / 2 + 1) + 1 by push_cast; ring]
    exact Real.Gamma_add_one (by positivity)
  have hs : √π ^ (n + 2) = π * √π ^ n := by
    rw [pow_add, Real.sq_sqrt Real.pi_pos.le]; ring
  have hΓ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  rw [hG, hs]
  field_simp

lemma ballVol_zero : ballVol 0 = 1 := by simp [ballVol]

lemma ballVol_one : ballVol 1 = 2 := by
  unfold ballVol
  have h : Real.Gamma ((1 : ℕ) / 2 + 1 : ℝ) = √π / 2 := by
    rw [show ((1 : ℕ) : ℝ) / 2 + 1 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [h, pow_one]
  field_simp

lemma ballVol_two : ballVol 2 = π := by
  have h := ballVol_add_two 0; rw [ballVol_zero] at h; norm_num at h; rw [h]
lemma ballVol_three : ballVol 3 = 4 * π / 3 := by
  have h := ballVol_add_two 1; rw [ballVol_one] at h; norm_num at h; rw [h]; ring
lemma ballVol_four : ballVol 4 = π ^ 2 / 2 := by
  have h := ballVol_add_two 2; rw [ballVol_two] at h; norm_num at h; rw [h]; ring
lemma ballVol_five : ballVol 5 = 8 * π ^ 2 / 15 := by
  have h := ballVol_add_two 3; rw [ballVol_three] at h; norm_num at h; rw [h]; ring
lemma ballVol_six : ballVol 6 = π ^ 3 / 6 := by
  have h := ballVol_add_two 4; rw [ballVol_four] at h; norm_num at h; rw [h]; ring
lemma ballVol_seven : ballVol 7 = 16 * π ^ 3 / 105 := by
  have h := ballVol_add_two 5; rw [ballVol_five] at h; norm_num at h; rw [h]; ring
lemma ballVol_eight : ballVol 8 = π ^ 4 / 24 := by
  have h := ballVol_add_two 6; rw [ballVol_six] at h; norm_num at h; rw [h]; ring

/-- Past dimension 5 the two-step recurrence shrinks: `2π/(n+2) < 1` once `n + 2 ≥ 7`. -/
lemma ballVol_add_two_lt {n : ℕ} (hn : 5 ≤ n) : ballVol (n + 2) < ballVol n := by
  rw [ballVol_add_two]
  have h7 : (7 : ℝ) ≤ n + 2 := by exact_mod_cast (by omega : 7 ≤ n + 2)
  have hr : 2 * π / (n + 2) < 1 := by
    rw [div_lt_one (by linarith)]; linarith [Real.pi_lt_d2]
  have := ballVol_pos n
  nlinarith

lemma ballVol_le_of_ge {m n : ℕ} (hm : 5 ≤ m) (h : ∃ k, n = m + 2 * k) : ballVol n ≤ ballVol m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
    have := ballVol_add_two_lt (n := m + 2 * k) (by omega)
    rw [show m + 2 * (k + 1) = m + 2 * k + 2 by ring]
    linarith

/-- **The ball volume is largest in dimension 5**, strictly, among all whole-number dimensions. -/
theorem ballVol_lt_five (n : ℕ) (hn : n ≠ 5) : ballVol n < ballVol 5 := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have h56 : ballVol 6 < ballVol 5 := by
    rw [ballVol_five, ballVol_six]
    have : 0 < π ^ 2 := by positivity
    nlinarith
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n
    · rw [ballVol_zero, ballVol_five]; nlinarith
    · rw [ballVol_one, ballVol_five]; nlinarith
    · rw [ballVol_two, ballVol_five]; nlinarith
    · rw [ballVol_three, ballVol_five]; nlinarith
    · rw [ballVol_four, ballVol_five]; nlinarith
  · rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h6 : 6 ≤ n := by omega
      have := ballVol_le_of_ge (m := 6) (n := n) (by norm_num) ⟨k - 3, by omega⟩
      linarith
    · have h7 : 7 ≤ n := by omega
      have h75 := ballVol_add_two_lt (n := 5) le_rfl
      have := ballVol_le_of_ge (m := 7) (n := n) (by norm_num) ⟨k - 3, by omega⟩
      linarith

/-- The sphere-area recurrence: `sphereArea (n+2) = 2π/n · sphereArea n`. -/
lemma sphereArea_add_two {n : ℕ} (hn : 1 ≤ n) : sphereArea (n + 2) = 2 * π / n * sphereArea n := by
  unfold sphereArea
  rw [ballVol_add_two]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  push_cast
  field_simp

lemma sphereArea_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sphereArea n :=
  mul_pos (by exact_mod_cast hn) (ballVol_pos n)

lemma sphereArea_add_two_lt {n : ℕ} (hn : 7 ≤ n) : sphereArea (n + 2) < sphereArea n := by
  rw [sphereArea_add_two (by omega)]
  have h7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 2 * π / n < 1 := by rw [div_lt_one (by linarith)]; linarith [Real.pi_lt_d2]
  have := sphereArea_pos (n := n) (by omega)
  nlinarith

lemma sphereArea_le_of_ge {m n : ℕ} (hm : 7 ≤ m) (h : ∃ k, n = m + 2 * k) :
    sphereArea n ≤ sphereArea m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
    have := sphereArea_add_two_lt (n := m + 2 * k) (by omega)
    rw [show m + 2 * (k + 1) = m + 2 * k + 2 by ring]
    linarith

/-- **The sphere area is largest in dimension 7 (the sphere `S⁶`)**, strictly. -/
theorem sphereArea_lt_seven (n : ℕ) (hn : n ≠ 7) : sphereArea n < sphereArea 7 := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have e7 : sphereArea 7 = 16 * π ^ 3 / 15 := by
    unfold sphereArea; rw [ballVol_seven]; push_cast; ring
  have e8 : sphereArea 8 = π ^ 4 / 3 := by
    unfold sphereArea; rw [ballVol_eight]; push_cast; ring
  have p3 : 0 < π ^ 3 := by positivity
  have hp2 : 9.8 < π ^ 2 := by nlinarith
  have hp3 : 30 < π ^ 3 := by nlinarith
  have h87 : sphereArea 8 < sphereArea 7 := by
    rw [e7, e8, show π ^ 4 = π * π ^ 3 by ring]; nlinarith
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> rw [e7] <;> unfold sphereArea <;> push_cast
    · simp; positivity
    · rw [ballVol_one]; nlinarith
    · rw [ballVol_two]; nlinarith [mul_pos Real.pi_pos (by linarith : (0:ℝ) < π ^ 2 - 1.9)]
    · rw [ballVol_three]; nlinarith [mul_pos Real.pi_pos (by linarith : (0:ℝ) < π ^ 2 - 3.8)]
    · rw [ballVol_four]; nlinarith
    · rw [ballVol_five]; nlinarith
    · rw [ballVol_six]; nlinarith
  · rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have := sphereArea_le_of_ge (m := 8) (n := n) (by norm_num) ⟨k - 4, by omega⟩
      linarith
    · have h97 := sphereArea_add_two_lt (n := 7) le_rfl
      have := sphereArea_le_of_ge (m := 9) (n := n) (by norm_num) ⟨k - 4, by omega⟩
      linarith

/-- **The completing factor is twice the reciprocal sphere area**: `Gammaℝ(n) · |S^{n-1}| = 2`. -/
theorem Gammaℝ_mul_sphereArea (n : ℕ) (hn : 1 ≤ n) :
    Complex.Gammaℝ (n : ℂ) * (sphereArea n : ℂ) = 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hG : Real.Gamma ((n : ℝ) / 2 + 1) = (n : ℝ) / 2 * Real.Gamma ((n : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hΓpos : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hsq : √π ^ n = π ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; ring_nf
  have hreal : π ^ (-(n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) * sphereArea n = 2 := by
    unfold sphereArea ballVol
    rw [hG, hsq, show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg Real.pi_pos.le]
    have : 0 < π ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    field_simp
  have hcast : Complex.Gammaℝ (n : ℂ) = ((π ^ (-(n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.Gammaℝ, Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le, ← Complex.Gamma_ofReal]
    push_cast; ring_nf
  rw [hcast, ← Complex.ofReal_mul, hreal]; norm_num

/-! ## Part B: primes + mirror symmetry force the completing factor -/

/-- The primes: `ζ` is the product over primes of `(1 - p^{-s})⁻¹` (Mathlib). -/
theorem zeta_from_primes {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- A zero-free entire function is `exp` of an entire function. -/
theorem exists_exp_of_ne_zero {h : ℂ → ℂ} (hd : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, h z = Complex.exp (g z) := by
  have hd' : Differentiable ℂ (deriv h) := fun z => (hd.analyticAt z).deriv.differentiableAt
  have hL : Differentiable ℂ (fun z => deriv h z / h z) := hd'.div hd hne
  obtain ⟨g₀, hg₀⟩ := hL.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv h z / h z) z := fun z => hg₀ z (Set.mem_univ z)
  set F : ℂ → ℂ := fun z => h z * Complex.exp (-g₀ z)
  have hF : ∀ z, HasDerivAt F 0 z := by
    intro z
    have h1 := (hd z).hasDerivAt
    have h2 := ((hg₀' z).neg).cexp
    convert h1.mul h2 using 1
    field_simp [hne z]
    ring
  have hFc : ∀ z, F z = F 0 := fun z =>
    is_const_of_deriv_eq_zero (fun w => (hF w).differentiableAt) (fun w => (hF w).deriv) z 0
  have hF0 : F 0 ≠ 0 := mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => Complex.log (F 0) + g₀ z,
    fun z => (differentiableAt_const _).add (hg₀' z).differentiableAt, fun z => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hF0, ← hFc z]
  simp only [F, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- An entire function whose real part grows slower than `|z|²` is affine (Borel–Carathéodory plus
Cauchy's estimate for the second derivative). -/
theorem deriv2_eq_zero_of_re_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K ρ : ℝ} (hK : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 2) (hre : ∀ z, (g z).re ≤ K * (1 + ‖z‖) ^ ρ) (c : ℂ) :
    iteratedDeriv 2 g c = 0 := by
  set A : ℝ := 4 + 6 * ‖g 0‖
  -- bound valid for every radius `R ≥ 1 + ‖c‖`
  have key : ∀ R : ℝ, 1 + ‖c‖ ≤ R →
      ‖iteratedDeriv 2 g c‖ ≤ 100 * K * R ^ (-(2 - ρ)) + A / R ^ 2 := by
    intro R hR
    have hR1 : 1 ≤ R := by linarith [norm_nonneg c]
    have hR0 : 0 < R := by linarith
    set M : ℝ := K * (1 + 4 * R) ^ ρ + 1
    have hM : 0 < M := by positivity
    have hmaps : Set.MapsTo g (ball 0 (4 * R)) {z | z.re ≤ M} := by
      intro x hx
      have hx' : ‖x‖ < 4 * R := mem_ball_zero_iff.mp hx
      have : (1 + ‖x‖) ^ ρ ≤ (1 + 4 * R) ^ ρ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hρ0
      simp only [Set.mem_ofPred_eq]
      nlinarith [hre x]
    have hsph : ∀ w ∈ sphere c R, ‖g w‖ ≤ 2 * M + 3 * ‖g 0‖ := by
      intro w hw
      have hwc : ‖w - c‖ = R := by simpa [dist_eq_norm] using hw
      have hw2 : ‖w‖ ≤ 2 * R := by
        have := norm_le_norm_add_norm_sub' w c
        have : ‖w‖ ≤ ‖c‖ + ‖w - c‖ := by
          calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
            _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
        linarith
      have hwb : w ∈ ball (0 : ℂ) (4 * R) := mem_ball_zero_iff.mpr (by linarith)
      have bc := Complex.borelCaratheodory hM hg.differentiableOn hmaps (by positivity) hwb
      have hden : 0 < 4 * R - ‖w‖ := by linarith
      have e1 : 2 * M * ‖w‖ / (4 * R - ‖w‖) ≤ 2 * M := by
        rw [div_le_iff₀ hden]; nlinarith [norm_nonneg w]
      have e2 : ‖g 0‖ * (4 * R + ‖w‖) / (4 * R - ‖w‖) ≤ 3 * ‖g 0‖ := by
        rw [div_le_iff₀ hden]; nlinarith [norm_nonneg w, norm_nonneg (g 0)]
      linarith
    have cauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR0 hg.diffContOnCl hsph
    have hpow : (1 + 4 * R) ^ ρ ≤ 25 * R ^ ρ := by
      calc (1 + 4 * R) ^ ρ ≤ (5 * R) ^ ρ := Real.rpow_le_rpow (by positivity) (by linarith) hρ0
        _ = 5 ^ ρ * R ^ ρ := Real.mul_rpow (by norm_num) hR0.le
        _ ≤ 5 ^ (2 : ℝ) * R ^ ρ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ.le) (by positivity)
        _ = 25 * R ^ ρ := by norm_num
    have hRr : R ^ ρ / R ^ 2 = R ^ (-(2 - ρ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hR0]; norm_num
    have hR2 : 0 < R ^ 2 := by positivity
    calc ‖iteratedDeriv 2 g c‖ ≤ (Nat.factorial 2) * (2 * M + 3 * ‖g 0‖) / R ^ 2 := cauchy
      _ ≤ (100 * K * R ^ ρ + A) / R ^ 2 := by
          gcongr
          simp only [Nat.factorial, M, A]
          norm_num
          nlinarith [mul_le_mul_of_nonneg_left hpow hK]
      _ = 100 * K * (R ^ ρ / R ^ 2) + A / R ^ 2 := by ring
      _ = 100 * K * R ^ (-(2 - ρ)) + A / R ^ 2 := by rw [hRr]
  have hlim : Tendsto (fun R : ℝ => 100 * K * R ^ (-(2 - ρ)) + A / R ^ 2) atTop (𝓝 0) := by
    have t1 := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 - ρ)).const_mul (100 * K)
    have t2 : Tendsto (fun R : ℝ => A / R ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    simpa using t1.add t2
  have hle : ‖iteratedDeriv 2 g c‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1 + ‖c‖, key⟩)
  exact norm_le_zero_iff.mp hle

/-- Hence such a function is affine. -/
theorem affine_of_re_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K ρ : ℝ} (hK : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 2) (hre : ∀ z, (g z).re ≤ K * (1 + ‖z‖) ^ ρ) :
    ∀ z, g z = g 0 + deriv g 0 * z := by
  have hg' : Differentiable ℂ (deriv g) := fun z => (hg.analyticAt z).deriv.differentiableAt
  have h2 : ∀ z, deriv (deriv g) z = 0 := fun z => by
    have := deriv2_eq_zero_of_re_growth hg hK hρ0 hρ hre z
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have hb : ∀ z, deriv g z = deriv g 0 := fun z => is_const_of_deriv_eq_zero hg' h2 z 0
  set b := deriv g 0
  have hk : ∀ z, HasDerivAt (fun w => g w - b * w) 0 z := fun z => by
    have := ((hg z).hasDerivAt).sub ((hasDerivAt_id' z).const_mul b)
    rw [hb z, mul_one, sub_self] at this
    exact this
  intro z
  have := is_const_of_deriv_eq_zero (fun w => (hk w).differentiableAt) (fun w => (hk w).deriv) z 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this

/-- **A zero-free entire function of order below 2 that is symmetric under `s ↦ 1 - s` is
constant.** -/
theorem const_of_symmetric {h : ℂ → ℂ} (hd : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) {K ρ : ℝ}
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ : ρ < 2) (hgrowth : ∀ z, ‖h z‖ ≤ Real.exp (K * (1 + ‖z‖) ^ ρ))
    (hsym : ∀ s, h (1 - s) = h s) : ∀ z, h z = h 0 := by
  obtain ⟨g, hg, hhg⟩ := exists_exp_of_ne_zero hd hne
  have hre : ∀ z, (g z).re ≤ K * (1 + ‖z‖) ^ ρ := fun z => by
    have := hgrowth z
    rw [hhg z, Complex.norm_exp] at this
    exact Real.exp_le_exp.mp this
  have haff := affine_of_re_growth hg hK hρ0 hρ hre
  set a := g 0
  set b := deriv g 0
  have hb : b = 0 := by
    by_contra hb
    set s : ℂ := (b - 1) / (2 * b)
    have e := hsym s
    rw [hhg, hhg, haff, haff] at e
    have e2 : Complex.exp ((a + b * (1 - s)) - (a + b * s)) = 1 := by
      rw [Complex.exp_sub, e, div_self (Complex.exp_ne_zero _)]
    have e3 : (a + b * (1 - s)) - (a + b * s) = 1 := by
      simp only [s]; field_simp; ring
    rw [e3] at e2
    have := congrArg (‖·‖) e2
    simp only [Complex.norm_exp, Complex.one_re, norm_one] at this
    exact absurd this (by
      have := Real.add_one_lt_exp (x := 1) one_ne_zero
      intro h; linarith)
  intro z
  rw [hhg z, hhg 0, haff z, hb, zero_mul, add_zero]

/-- The tower `Gammaℝ` completes `ζ`: `Λ = Gammaℝ · ζ` on `Re s > 1` and `Λ(1 - s) = Λ(s)` (Mathlib). -/
theorem completed_eq_Gammaℝ_mul {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- **Uniqueness of the completing factor.** Suppose `h · Gammaℝ` also completes `ζ` symmetrically,
i.e. `h(s) Λ(s) = h(1 - s) Λ(1 - s)` for `Re s > 1`, with `h` entire, zero-free and of order below 2.
Then `h` is constant: the ball-tower factor `Gammaℝ = 2 / sphereArea` is the only one. -/
theorem completing_factor_unique {h : ℂ → ℂ} (hd : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0)
    {K ρ : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ : ρ < 2)
    (hgrowth : ∀ z, ‖h z‖ ≤ Real.exp (K * (1 + ‖z‖) ^ ρ))
    (hfe : ∀ s : ℂ, 1 < s.re →
      h s * completedRiemannZeta s = h (1 - s) * completedRiemannZeta (1 - s)) :
    ∀ z, h z = h 0 := by
  have hU : ∀ s : ℂ, 1 < s.re → h (1 - s) = h s := by
    intro s hs
    have hΛ : completedRiemannZeta s ≠ 0 := by
      rw [completed_eq_Gammaℝ_mul hs]
      exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
        (riemannZeta_ne_zero_of_one_lt_re hs)
    have := hfe s hs
    rw [completedRiemannZeta_one_sub] at this
    exact (mul_right_cancel₀ hΛ this).symm
  have han : AnalyticOnNhd ℂ h Set.univ := fun z _ => hd.analyticAt z
  have han' : AnalyticOnNhd ℂ (fun s => h (1 - s)) Set.univ := fun z _ =>
    (hd.comp (differentiable_const 1 |>.sub differentiable_id)).analyticAt z
  have hev : (fun s => h (1 - s)) =ᶠ[𝓝 (2 : ℂ)] h := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs using hU s hs
  have heq := han'.eq_of_eventuallyEq han hev
  exact const_of_symmetric hd hne hK hρ0 hρ hgrowth (fun s => congrFun heq s)

end BallTower
