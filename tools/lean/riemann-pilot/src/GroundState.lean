import Mathlib
import Curvature

/-! # Ground states of Weil's form: the structural facts

`Roadmap.lean` defines Theorem 1bn(i)'s form `weilQ`, the admissible class `Probe` (real, even,
supported in `[−a, a]`, in `L²`, archimedean integral convergent) and `IsGroundState` (a normalised
minimiser). This file proves what the definitions give:

* `abs_autocorr_le`: `|f(u)| ≤ f(0) = ‖g‖²`, so the archimedean integrand is non-negative;
* `prime_sum_eq`: only the prime powers `n ≤ e^{2a} = e^δ` enter the prime sum;
* `weilQ_ge`: `Q(g) ≥ (ψ(¼) − log π − 2P(a))‖g‖²`, `P(a) = Σ_{n ≤ e^δ} Λ(n)/√n`, so the ground
  energy `λ₁(δ)` is finite;
* `Probe.intervalIntegrable`: a probe is integrable on `[−a, a]`;
* `rh_of_groundStates_dodging`: the chain of `Curvature.lean` for ground states, with evenness and
  integrability discharged by the definition.

Not proved: that a ground state exists (the minimum is attained). That needs the compactness supplied
by the archimedean term's logarithmic growth in frequency.
-/

open Real Filter Topology Complex MeasureTheory Set ArithmeticFunction

noncomputable section

namespace Pilot1ca

/-- The constant `ψ(¼) − log π` of `weilQ`. -/
def weilConst : ℝ := (Complex.digamma (1 / 4)).re - Real.log π

/-! ## The autocorrelation -/

theorem autocorr_zero (g : ℝ → ℝ) : autocorr g 0 = normSq g := by
  simp [autocorr, normSq, sq]

/-- `|f(u)| ≤ f(0)`, from `|g(t)g(t+u)| ≤ (g(t)² + g(t+u)²)/2`. -/
theorem abs_autocorr_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    |autocorr g u| ≤ normSq g := by
  have hI : Integrable (fun t => g t ^ 2) := hg.integrable_sq
  have hJ : Integrable (fun t => g (t + u) ^ 2) := hI.comp_add_right u
  have hb : Integrable (fun t => (g t ^ 2 + g (t + u) ^ 2) / 2) := (hI.add hJ).div_const 2
  have hle := norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => by
    show ‖g t * g (t + u)‖ ≤ (g t ^ 2 + g (t + u) ^ 2) / 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (g t - g (t + u)), sq_nonneg (g t + g (t + u))])
  rw [Real.norm_eq_abs] at hle
  unfold autocorr normSq
  refine hle.trans (le_of_eq ?_)
  rw [integral_div, integral_add hI hJ, integral_add_right_eq_self (fun t => g t ^ 2) u]
  ring

/-- The autocorrelation vanishes beyond `2a`. -/
theorem autocorr_eq_zero {a : ℝ} {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) {u : ℝ}
    (hu : 2 * a < |u|) : autocorr g u = 0 := by
  have h0 : (fun t => g t * g (t + u)) = fun _ => 0 := by
    funext t
    by_cases ht : a < |t|
    · rw [hsupp t ht, zero_mul]
    · have htu : a < |t + u| := by
        rw [not_lt] at ht
        by_contra h
        rw [not_lt] at h
        have : |u| ≤ |t + u| + |t| := by
          have := abs_sub (t + u) t
          rwa [add_sub_cancel_left] at this
        linarith
      rw [hsupp _ htu, mul_zero]
  simp [autocorr, h0]

/-! ## The prime sum is finite -/

/-- The prime powers that enter: `n < N(a) = ⌊e^{2a}⌋ + 1`, i.e. `n ≤ e^δ`. -/
def primeCut (a : ℝ) : ℕ := ⌊Real.exp (2 * a)⌋₊ + 1

/-- `P(a) = Σ_{n ≤ e^{2a}} Λ(n)/√n`. -/
def primeWeight (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (primeCut a), Λ n / Real.sqrt n

theorem prime_sum_eq {a : ℝ} {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) :
    (∑' n : ℕ, Λ n / Real.sqrt n * autocorr g (Real.log n))
      = ∑ n ∈ Finset.range (primeCut a),
          Λ n / Real.sqrt n * autocorr g (Real.log n) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hlt : Real.exp (2 * a) < n := by
    have := Nat.lt_floor_add_one (Real.exp (2 * a))
    have hn' : ((⌊Real.exp (2 * a)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hn'
    linarith
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hlt
  have hlog : 2 * a < Real.log n := by
    rw [← Real.log_exp (2 * a)]
    exact Real.log_lt_log (Real.exp_pos _) hlt
  rw [autocorr_eq_zero hsupp (hlog.trans_le (le_abs_self _)), mul_zero]

theorem abs_prime_sum_le {a : ℝ} {g : ℝ → ℝ} (hadm : Probe a g) :
    |∑' n : ℕ, Λ n / Real.sqrt n * autocorr g (Real.log n)|
      ≤ primeWeight a * normSq g := by
  rw [prime_sum_eq hadm.supp, primeWeight, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hc : 0 ≤ Λ n / Real.sqrt n := div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_autocorr_le hadm.memL2 _) hc

/-! ## The lower bound -/

/-- **`Q(g) ≥ (ψ(¼) − log π − 2P(a))‖g‖²`** on probes: the pole and archimedean terms are
non-negative and `|f(log n)| ≤ ‖g‖²`. -/
theorem weilQ_ge {a : ℝ} {g : ℝ → ℝ} (hadm : Probe a g) :
    (weilConst - 2 * primeWeight a) * normSq g ≤ weilQ a g := by
  have hpole : 0 ≤ 2 * poleR g a ^ 2 := by positivity
  have harch : 0 ≤ ∫ u in Ioi (0 : ℝ), archIntegrand g u := by
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => mul_nonneg ?_
      (div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)).le
    rw [autocorr_zero, sub_nonneg]
    exact (le_abs_self _).trans (abs_autocorr_le hadm.memL2 u)
  have hprime := (le_abs_self _).trans (abs_prime_sum_le hadm)
  have e : (weilConst - 2 * primeWeight a) * normSq g
      = weilConst * normSq g - 2 * (primeWeight a * normSq g) := by ring
  unfold weilQ
  rw [e, weilConst]
  linarith

/-- **The ground energy is bounded below**: `λ₁(δ) ≥ ψ(¼) − log π − 2Σ_{n ≤ e^δ} Λ(n)/√n`. -/
theorem groundState_energy_ge {a : ℝ} {g : ℝ → ℝ} (hgs : IsGroundState a g) :
    weilConst - 2 * primeWeight a ≤ weilQ a g := by
  have := weilQ_ge hgs.1
  rwa [hgs.2.1, mul_one] at this

/-! ## The chain for ground states -/

theorem Probe.intervalIntegrable {a : ℝ} {g : ℝ → ℝ} (hadm : Probe a g) :
    IntervalIntegrable g volume (-a) a := by
  have h2 : MemLp g 2 (volume.restrict (Set.uIoc (-a) a)) := hadm.memL2.restrict _
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (-a) a)) :=
    isFiniteMeasure_restrict.2 (by simp [Set.uIoc])
  have h1 : Integrable g (volume.restrict (Set.uIoc (-a) a)) := h2.integrable (by norm_num)
  exact (intervalIntegrable_iff).2 h1

/-- **Roadmap item 1 ⇒ `RiemannHypothesis`, for the ground states of Weil's form.** Let `g_n` be a
ground state of `Q` at support `2a_n`, with `∫g_n ≠ 0`. If `ĝ_n` is real-rooted, satisfies dodging D
(`η_n → 0`, `T_D(n) → ∞`) and its curvature `∫u²g_n/(2∫g_n)` converges to `Ξ`'s `Re Σ γ⁻²`, then RH. -/
theorem rh_of_groundStates_dodging {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hg0 : ∀ n, (∫ u in (-(a n))..(a n), g n u) ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ZeroIdx (sqF (ghatC (g n) (a n))) → Prop)
      (e : {i // p i} ≃ {j : ZeroIdx (sqF Xi) // t n < ‖j.1⁻¹‖}),
      (∑' i : {i // p i}, ‖i.1.1⁻¹ - (e i).1.1⁻¹‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (hκ : Tendsto (fun n => (∫ u in (-(a n))..(a n), u ^ 2 * g n u)
        / (2 * ∫ u in (-(a n))..(a n), g n u))
      atTop (𝓝 (∑' j : ZeroIdx (sqF Xi), j.1⁻¹).re)) :
    RiemannHypothesis :=
  rh_of_dodging_and_curvature_final ha (fun n => (hgs n).1.intervalIntegrable)
    (fun n => (hgs n).1.even) hg0 hRR hD hη ht hκ

end Pilot1ca

#print axioms Pilot1ca.abs_autocorr_le
#print axioms Pilot1ca.autocorr_eq_zero
#print axioms Pilot1ca.prime_sum_eq
#print axioms Pilot1ca.weilQ_ge
#print axioms Pilot1ca.groundState_energy_ge
#print axioms Pilot1ca.Probe.intervalIntegrable
#print axioms Pilot1ca.rh_of_groundStates_dodging
