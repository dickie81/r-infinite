import Mathlib
import Hadamard
import Limit

/-! # Hadamard's factorisation for even functions, applied to `ĝ` and `Ξ`

An even entire `f` is `f(z) = F(z²)` with `F(w) = f(√w)` entire (any square root, by evenness), and
`f` of order `< 2` makes `F` of order `< 1`. `hadamard_genus0` then gives
`f(z) = f(0)Π(1 − z²/u)` over the zeros `u` of `F`, the squares of `f`'s zero pairs. That is
`HadamardW f w` with `w = u⁻¹ = τ⁻²` and the family being `f`'s own zero list:
* `ĝ` is even (`g` even) and of exponential type, so order `≤ 1`;
* `Ξ` is even (the functional equation `Λ₀(1 − s) = Λ₀(s)`), and its order is the named input
  `XiGrowth` (`‖Ξ(t)‖ ≤ C exp(A‖t‖^{3/2})`, true with order 1), with `Ξ(0) ≠ 0` (`Ξ(0) = 0.497…`). -/

open Real Filter Topology Metric Complex MeasureTheory

noncomputable section

namespace Pilot1ca

/-! ## Even functions as functions of `z²` -/

/-- `F(w) = f(√w)` with the principal square root. -/
def sqF (f : ℂ → ℂ) (w : ℂ) : ℂ := f (w ^ ((2 : ℂ)⁻¹))

theorem sqrt_sq' (w : ℂ) : (w ^ ((2 : ℂ)⁻¹)) ^ 2 = w := cpow_ofNat_inv_pow w 2

theorem even_eq_of_sq {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) {a b : ℂ} (h : a ^ 2 = b ^ 2) :
    f a = f b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · rw [h]
  · rw [h, heven]

theorem sqF_sq {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) (z : ℂ) : sqF f (z ^ 2) = f z :=
  even_eq_of_sq heven (sqrt_sq' (z ^ 2))

theorem sqF_zero (f : ℂ → ℂ) : sqF f 0 = f 0 := by
  simp [sqF, zero_cpow (inv_ne_zero (two_ne_zero))]

/-- `sqF f = f ∘ (v ↦ i√(−v))` too (evenness), which is differentiable across the negative axis. -/
theorem sqF_eq_alt {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) :
    sqF f = fun v => f (I * (-v) ^ ((2 : ℂ)⁻¹)) := by
  funext v
  apply even_eq_of_sq heven
  rw [sqrt_sq', mul_pow, sqrt_sq', I_sq]; ring

theorem sqF_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (heven : ∀ z, f (-z) = f z) :
    Differentiable ℂ (sqF f) := by
  have hon : DifferentiableOn ℂ (sqF f) Set.univ := by
    rw [← differentiableOn_compl_singleton_and_continuousAt_iff (c := 0) Filter.univ_mem]
    constructor
    · intro w hw
      have hw0 : w ≠ 0 := by simpa using hw.2
      apply DifferentiableAt.differentiableWithinAt
      by_cases hs : w ∈ slitPlane
      · exact (hf _).comp w (differentiableAt_id.cpow_const hs)
      · rw [sqF_eq_alt heven]
        have hs' : -w ∈ slitPlane := by
          rw [mem_slitPlane_iff] at hs ⊢
          obtain ⟨hs1, hs2⟩ := not_or.1 hs
          have hs1' : w.re ≤ 0 := le_of_not_gt hs1
          have hs2' : w.im = 0 := not_not.1 hs2
          left
          have hre : w.re ≠ 0 := by
            intro h; apply hw0; exact Complex.ext (by simp [h]) (by simp [hs2'])
          simp only [neg_re]
          exact lt_of_le_of_ne (by linarith) (fun h => hre (by linarith))
        exact (hf _).comp w ((differentiableAt_const _).mul
          (differentiableAt_id.neg.cpow_const hs'))
    · -- continuity at `0`
      have h1 : Tendsto (fun v : ℂ => v ^ ((2 : ℂ)⁻¹)) (𝓝 0) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have e : (fun v : ℂ => ‖v ^ ((2 : ℂ)⁻¹)‖) = fun v => ‖v‖ ^ (2⁻¹ : ℝ) := by
          funext v
          rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
        rw [e]
        have hc : ContinuousAt (fun x : ℝ => x ^ (2⁻¹ : ℝ)) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))
        have := hc.tendsto.comp (tendsto_norm_zero (E := ℂ))
        rw [Real.zero_rpow (by norm_num : (2⁻¹ : ℝ) ≠ 0)] at this
        exact this
      have h2 := (hf.continuous.tendsto 0).comp h1
      show Tendsto (sqF f) (𝓝 0) (𝓝 (sqF f 0))
      rw [sqF_zero]
      exact h2
  exact fun w => (hon w (Set.mem_univ w)).differentiableAt Filter.univ_mem

/-- **Hadamard's factorisation for even entire functions of order `< 2`**: `f(z) = f(0)Π(1 − z²/u)` over
the zeros `u` of `F(w) = f(√w)` (with multiplicity), i.e. `HadamardW f (u⁻¹)` over `f`'s zero pairs. -/
theorem hadamardW_even {f : ℂ → ℂ} (hf : Differentiable ℂ f) (heven : ∀ z, f (-z) = f z)
    (hf0 : f 0 ≠ 0) {C A β : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A) (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖ ^ β)) :
    HadamardW f (fun i : ZeroIdx (sqF f) => i.1⁻¹) := by
  have hF := sqF_differentiable hf heven
  have hF0 : sqF f 0 ≠ 0 := by rwa [sqF_zero]
  have hgF : ∀ w, ‖sqF f w‖ ≤ C * Real.exp (A * ‖w‖ ^ (β / 2)) := by
    intro w
    refine (hgrowth _).trans ?_
    have hn : ‖w ^ ((2 : ℂ)⁻¹)‖ = ‖w‖ ^ (2⁻¹ : ℝ) := by
      rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [hn, ← Real.rpow_mul (norm_nonneg _)]
    rw [show (2⁻¹ : ℝ) * β = β / 2 by ring]
  obtain ⟨hsum, hprod⟩ := hadamard_genus0 hF hF0 hC hA (by positivity) (by linarith) hgF
  refine ⟨hf0, hsum, fun z => ?_⟩
  have h := hprod (z ^ 2)
  rw [sqF_sq heven, sqF_zero] at h
  exact h

/-! ## `ĝ` -/

theorem norm_ghatC_le {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (z : ℂ) :
    ‖ghatC g a z‖ ≤ (1 + ∫ u in (-a)..a, |g u|) * Real.exp (a * ‖z‖ ^ (1 : ℝ)) := by
  rw [Real.rpow_one]
  have hle : -a ≤ a := by linarith
  have hpt : ∀ u ∈ Set.Ioc (-a) a,
      ‖((g u : ℝ) : ℂ) * Complex.exp (I * z * u)‖ ≤ Real.exp (a * ‖z‖) * |g u| := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.exp_le_exp.2
    have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [mul_re]
    rw [e]
    have hu' : |u| ≤ a := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ ‖z‖ * a := mul_le_mul (abs_im_le_norm z) hu' (abs_nonneg _) (norm_nonneg _)
      _ = a * ‖z‖ := mul_comm _ _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hle
    (Filter.Eventually.of_forall hpt) (hg.abs.const_mul (Real.exp (a * ‖z‖)))
  rw [intervalIntegral.integral_const_mul] at h1
  unfold ghatC
  refine h1.trans ?_
  have hI : 0 ≤ ∫ u in (-a)..a, |g u| :=
    intervalIntegral.integral_nonneg hle (fun u _ => abs_nonneg _)
  nlinarith [Real.exp_pos (a * ‖z‖)]

/-- **Hadamard's factorisation of the transform** of an even probe with `ĝ(0) ≠ 0`, over its own zero
pairs. No named input. -/
theorem hadamardW_ghat {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) :
    HadamardW (ghatC g a) (fun i : ZeroIdx (sqF (ghatC g a)) => i.1⁻¹) := by
  have hI : 0 ≤ ∫ u in (-a)..a, |g u| :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => abs_nonneg (g u))
  exact hadamardW_even (ghatC_differentiable hg) (fun z => ghatC_even heven a z) h0
    (by linarith : (1 : ℝ) ≤ 1 + ∫ u in (-a)..a, |g u|) ha (by norm_num)
    (by norm_num) (norm_ghatC_le ha hg)

/-! ## `Ξ` -/

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem Xi_even (t : ℂ) : Xi (-t) = Xi t := by
  unfold Xi
  rw [← xi_one_sub]
  congr 1; ring

/-- **The order of `Ξ`** (named input; true with exponent `1 + ε`, used with `3/2`). -/
def XiGrowth : Prop := ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ t, ‖Xi t‖ ≤ C * Real.exp (A * ‖t‖ ^ (3 / 2 : ℝ))

/-- **Hadamard's factorisation of `Ξ`** over its zero pairs, from its order and `Ξ(0) ≠ 0`. -/
theorem hadamardW_Xi (hgrowth : XiGrowth) (h0 : Xi 0 ≠ 0) :
    HadamardW Xi (fun i : ZeroIdx (sqF Xi) => i.1⁻¹) := by
  obtain ⟨C, A, hC, hA, hg⟩ := hgrowth
  exact hadamardW_even differentiable_Xi Xi_even h0 hC hA (by norm_num) (by norm_num) hg

/-! ## The chain, with Hadamard proved -/

/-- **§11 item 1 ⇒ RH with Hadamard's factorisation proved.** Ground states `g n` at supports `2a n`
(even, integrable, `ĝ_n(0) ≠ 0`) whose transforms are real-rooted, satisfying Hypothesis D exactly
below `T_D(n)` against `Ξ`'s zero list, with `Σ_τ τ⁻²` bounded and `ε(δ_n) → 0`, give Mathlib's
`RiemannHypothesis`. The zero lists are the functions' own (`ZeroIdx ∘ sqF`); the named inputs
left are `Ξ`'s order (`XiGrowth`) and `Ξ(0) ≠ 0`. -/
theorem rh_of_D_and_realRooted_proved {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n)) (hXg : XiGrowth) (hX0 : Xi 0 ≠ 0)
    {B : ℝ} (hB : ∀ n, (∑' i : ZeroIdx (sqF (ghatC (g n) (a n))), ‖i.1⁻¹‖) ≤ B)
    {t : ℕ → ℝ}
    (hD : ∀ n, DFamW (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF Xi) => i.1⁻¹) (t n))
    (hε : Tendsto (fun n => tailEps (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF Xi) => i.1⁻¹) (t n)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  rh_of_D_and_realRooted hint hRR (fun n => hadamardW_ghat (ha n) (hint n) (heven n) (hg0 n))
    (hadamardW_Xi hXg hX0) hB hD hε

end Pilot1ca

#print axioms Pilot1ca.sqF_differentiable
#print axioms Pilot1ca.hadamardW_even
#print axioms Pilot1ca.hadamardW_ghat
#print axioms Pilot1ca.Xi_even
#print axioms Pilot1ca.hadamardW_Xi
#print axioms Pilot1ca.rh_of_D_and_realRooted_proved
