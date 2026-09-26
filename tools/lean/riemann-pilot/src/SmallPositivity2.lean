import Mathlib
import SmallPositivity

/-! # Sharper constants: `λ₁ ≥ 1/20` for every `0 < a ≤ 1/12` (round 122, part 1)

This extends round 121's `weilQ_ge_quarter` (`a ≤ 1/16`) to `a ≤ 1/12`, still analytic and still on every
normalised even probe. Three constants are sharpened.
* **`γ < 0.60815`** from Mathlib's `γ < H_n − log n` at `n = 16` (`gamma_lt`, now in SmallPositivity.lean).
* **`log 3 > 1.0986`** (`log_three_gt`, FourierGap.lean) from Mathlib's Taylor bound `exp_bound` at `0.0986` and `e < 2.7182818286`.
* **The far field without the `−a` loss**: `(eᵃ + 1)/(eᵃ − 1) ≥ 2/a`, i.e. `tanh y ≤ y`, proved by
  monotonicity. So `Far(a) ≥ log(2/a) + π/2 − sinh a ≥ log 24 + π/2 − sinh(1/12)`.

The budget at `a = 1/12` is `c₀ ≥ −5.4301`, `Far ≥ 4.6654` and `Near ≥ 0.834`, for a total of `0.069 ≥ 1/20`.
The method's ceiling is about `a ≈ 0.095`, where `λ₀ → 0` (round 121). Beyond it the pole term is needed:
see `PoleRelax.lean` (round 122, part 2).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- `tanh y ≤ y` in the form `2(eᵃ − 1) ≤ a(eᵃ + 1)` for `a ≥ 0`. -/
theorem two_exp_sub_le {a : ℝ} (ha : 0 ≤ a) : 2 * (Real.exp a - 1) ≤ a * (Real.exp a + 1) := by
  set h : ℝ → ℝ := fun x => x * (Real.exp x + 1) - 2 * (Real.exp x - 1) with hh
  have hd : ∀ x, HasDerivAt h (1 - Real.exp x + x * Real.exp x) x := by
    intro x
    have := ((hasDerivAt_id x).mul ((Real.hasDerivAt_exp x).add_const 1)).sub
      (((Real.hasDerivAt_exp x).sub_const 1).const_mul 2)
    convert this using 1
    · funext y; simp [hh]
    · simp only [id]; ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (by fun_prop : Continuous h).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      have h1 := Real.add_one_le_exp (-x)
      have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ha) ha
  simp only [hh, Real.exp_zero] at this
  linarith

/-- **The far field for `0 < a ≤ 1/12`**: `≥ 4.6654`. -/
theorem farField_ge' {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 12) : (4.6654 : ℝ) ≤ ∫ u in Ioi (2 * a), kerK u := by
  rw [farField_eq ha]
  have hE : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hratio : 2 / a ≤ (Real.exp a + 1) / (Real.exp a - 1) := by
    rw [div_le_div_iff₀ ha (by linarith)]
    nlinarith [two_exp_sub_le ha.le]
  have hneg : -Real.log ((Real.exp a - 1) / (Real.exp a + 1)) = Real.log ((Real.exp a + 1) / (Real.exp a - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hlogr : Real.log (2 / a) ≤ Real.log ((Real.exp a + 1) / (Real.exp a - 1)) :=
    Real.log_le_log (by positivity) hratio
  have h24 : Real.log 24 ≤ Real.log (2 / a) := Real.log_le_log (by norm_num) (by
    rw [le_div_iff₀ ha]; linarith)
  have hl24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have hat : Real.arctan (Real.sinh a) ≤ Real.sinh a := Real.arctan_le_self (Real.sinh_nonneg_iff.mpr ha.le)
  have hsh : Real.sinh a ≤ a + a ^ 3 / 6 + a ^ 5 / 100 := sinh_le_taylor ha.le (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl3 := log_three_gt
  have hπ := Real.pi_gt_d6
  have h3 : a ^ 3 ≤ (1 / 12) ^ 3 := pow_le_pow_left₀ ha.le ha1 3
  have h5 : a ^ 5 ≤ (1 / 12) ^ 5 := pow_le_pow_left₀ ha.le ha1 5
  rw [hneg]
  norm_num at hl2 hπ h3 h5 ⊢
  linarith

/-- **The near field of every normalised probe, for `0 < a ≤ 1/12`**: `≥ 0.834`. -/
theorem nearField_all' {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 12) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (0.834 : ℝ) ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  set τ := 2.2965 - errK a with hτ
  have hE := energy_ge_trunc ha hp hn lowS2 (τ := τ) (tail3_all ha (by linarith))
  have hsum : ∑ n ∈ lowS2, (modeE a n - τ) * pm a g n
      = (modeE a 0 - τ) * pm a g 0
        + 2 * ((modeE a 1 - τ) * pm a g 1 + (modeE a 2 - τ) * pm a g 2) :=
    sum_lowS2_even fun k => by simp only [modeE_neg, pm_neg ha hp]
  rw [hsum] at hE
  have herr0 : 0 ≤ errK a := errK_nonneg ha.le
  have herr : errK a ≤ 0.0014 := by
    unfold errK
    have h2 : a ^ 2 ≤ (1 / 12) ^ 2 := pow_le_pow_left₀ ha.le ha1 2
    have h3 : a ^ 3 ≤ (1 / 12) ^ 3 := pow_le_pow_left₀ ha.le ha1 3
    have h4 : a ^ 4 ≤ (1 / 12) ^ 4 := pow_le_pow_left₀ ha.le ha1 4
    have h5 : a ^ 5 ≤ (1 / 12) ^ 5 := pow_le_pow_left₀ ha.le ha1 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have t0 : (0 - τ) * (1 / 4) ≤ (modeE a 0 - τ) * pm a g 0 :=
    term_ge (le_of_eq (modeE_zero a).symm) (by rw [hτ]; linarith) (pm_nonneg ha g 0) (pm_cap0 ha hp hn)
  have t1 := term_mode ha (by linarith) (g := g) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338) (X := 0)
    (Y := 0) (τ := τ) (P := 0.2046) (by simpa using cin_val1) dlo1 le_rfl
    (by rw [hτ]; nlinarith) (pm_cap1 ha hp hn)
  have t2 := term_mode ha (by linarith) (g := g) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1) (X := 0)
    (Y := 0) (τ := τ) (P := 1 / 8) (by simpa using cin_val2) dlo2 le_rfl
    (by rw [hτ]; nlinarith) (pm_cap2 ha hp hn)
  simp only [sub_zero] at t1 t2
  rw [hτ] at t0 t1 t2 hE
  nlinarith

/-- **Weil positivity on every probe, `0 < a ≤ 1/12`**: `Q(g) ≥ 1/20` for every normalised probe. -/
theorem weilQ_ge_twentieth {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 12) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (1 / 20 : ℝ) ≤ weilQ a g := by
  have hlog : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  rw [weilQ_eq', primeS_eq_zero hlog hp, hn, archE_split ha hp hn]
  have hC := weilConst_ge
  have hF := farField_ge' ha ha1
  have hN := nearField_all' ha ha1 hp hn
  have hP : 0 ≤ 2 * poleR g a ^ 2 := by positivity
  linarith

end Pilot1ca

#print axioms Pilot1ca.gamma_lt
#print axioms Pilot1ca.log_three_gt
#print axioms Pilot1ca.two_exp_sub_le
#print axioms Pilot1ca.farField_ge'
#print axioms Pilot1ca.nearField_all'
#print axioms Pilot1ca.weilQ_ge_twentieth
