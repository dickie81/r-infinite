import Mathlib
import FirstFailure

/-! # The ground energy's rate of failure measures the zeros (round 221)

`WeilLandau.weil_twins_rate` grades Weil positivity: the twin form `Q(twin (box 1) λ)` is bounded
below by `−C·e^{σλ}` exactly when every nontrivial zero has `|2 Re ρ − 1| ≤ σ`. Since
`Q(g) ≥ λ₁(a)‖g‖²` and `‖twin (box 1) λ‖² ≤ 4`, the same holds for the ground energy `λ₁`.

* `zeros_of_lam_ge`: if `λ₁(a) ≥ −C·e^{σa}` for every `a ≥ 1`, every nontrivial zero has
  `|2 Re ρ − 1| ≤ σ`. A lower bound on `λ₁` of any exponential rate is a zero-free half-plane.
* `rh_iff_lam_subexp`: RH holds if and only if, for every `σ > 0`, `λ₁(a) ≥ −C_σ·e^{σa}` for `a ≥ 1`.
* `lam_rate`: conversely, a zero with `|2 Re ρ − 1| > σ` forces `λ₁(a) < −C·e^{σa}` at arbitrarily
  large `a`, for every `C`.
* `lam_fails_exponentially`: if RH fails, there is `δ > 0` such that, for every `σ < δ` and every
  `C`, `λ₁(a) < −C·e^{σa}` at arbitrarily large `a`.

Compare `KaiserNine.lam_nine`: under RH, `0 ≤ λ₁(a) ≤ K(a+1)e^{9a−4πe^{2a}}`, double-exponentially
small. A failure of RH is not a marginal crossing: after the first failure (`first_failure`), `λ₁`
falls away at an exponential rate.

No bearing on RH: these are equivalences and their quantitative forms.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

theorem normSq_twin_le (l : ℝ) : normSq (twin (box 1) l) ≤ 4 := by
  have hm := (box_probe 1).memL2
  have e : twin (box 1) l = fun t => box 1 (t + -l) + box 1 (t + l) := by
    funext t; simp [twin, sub_eq_add_neg]
  rw [e]
  have h := normSq_add_le (memLp_shift hm (-l)) (memLp_shift hm l)
  rw [normSq_shift, normSq_shift, normSq_box one_pos] at h
  linarith

/-- **A lower bound on `λ₁` of exponential rate `σ` is the zero-free half-plane `Re s > (1 + σ)/2`.** -/
theorem zeros_of_lam_ge {C σ : ℝ} (hσ : 0 ≤ σ) (h : ∀ a, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lam a)
    (s : ℂ) (hs : IsNontrivialZero s) : |2 * s.re - 1| ≤ σ := by
  refine (weil_twins_rate hσ).1 ⟨4 * (|C| * Real.exp σ), fun l hl => ?_⟩ s hs
  set K := |C| * Real.exp σ * Real.exp (σ * l)
  have hK : 0 ≤ K := by positivity
  have hN := normSq_twin_le l
  have hN0 := normSq_nonneg (twin (box 1) l)
  have hlam := lam_mul_le (twin_probe (box_probe 1) hl)
  have h1 : -K ≤ lam (l + 1) := by
    have := h (l + 1) (by linarith)
    have e : Real.exp (σ * (l + 1)) = Real.exp σ * Real.exp (σ * l) := by
      rw [← Real.exp_add]; ring_nf
    rw [e] at this
    have : C * (Real.exp σ * Real.exp (σ * l)) ≤ |C| * (Real.exp σ * Real.exp (σ * l)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    simp only [K]; nlinarith
  have h2 : -K * normSq (twin (box 1) l) ≤ lam (l + 1) * normSq (twin (box 1) l) :=
    mul_le_mul_of_nonneg_right h1 hN0
  have h3 : -K * 4 ≤ -K * normSq (twin (box 1) l) := by nlinarith
  calc -(4 * (|C| * Real.exp σ) * Real.exp (σ * l)) = -K * 4 := by simp only [K]; ring
    _ ≤ _ := h3.trans (h2.trans hlam)

/-- **RH ⟺ `λ₁` has no negative part of exponential rate.** -/
theorem rh_iff_lam_subexp :
    RiemannHypothesis ↔ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lam a := by
  constructor
  · intro hRH σ _
    exact ⟨0, fun a ha => by simpa using lam_nonneg_of_RH hRH (by linarith : (0 : ℝ) < a)⟩
  · intro h s hs htriv _
    have hs' : IsNontrivialZero s := ⟨hs, htriv⟩
    have key : ∀ σ > 0, |2 * s.re - 1| ≤ σ := fun σ hσ => by
      obtain ⟨C, hC⟩ := h σ hσ
      exact zeros_of_lam_ge hσ.le hC s hs'
    have : |2 * s.re - 1| = 0 := le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      simpa using key ε hε) (abs_nonneg _)
    rw [abs_eq_zero] at this; linarith

/-- **A zero with `|2 Re ρ − 1| > σ` makes `λ₁(a) < −C·e^{σa}` at arbitrarily large `a`.** -/
theorem lam_rate {s : ℂ} (hs : IsNontrivialZero s) {σ : ℝ} (hσ : 0 ≤ σ) (hlt : σ < |2 * s.re - 1|)
    (C X : ℝ) : ∃ a, X < a ∧ lam a < -(C * Real.exp (σ * a)) := by
  by_contra hno
  push Not at hno
  set b := max X 1 + 1
  have hb1 : 1 ≤ b := by linarith [le_max_right X 1]
  have hbX : X < b := by linarith [le_max_left X 1]
  set K := |C| * Real.exp (σ * b)
  have hK1 : |C| ≤ K := le_mul_of_one_le_right (abs_nonneg C) (Real.one_le_exp (by positivity))
  refine absurd (zeros_of_lam_ge (C := K) hσ (fun a ha => ?_) s hs) (not_le.2 hlt)
  have hea : 1 ≤ Real.exp (σ * a) := Real.one_le_exp (by nlinarith)
  rcases lt_or_ge X a with hXa | haX
  · have := hno a hXa
    have : C * Real.exp (σ * a) ≤ K * Real.exp (σ * a) :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans hK1) (by positivity)
    linarith
  · have hab : lam b ≤ lam a := lam_antitone (by linarith) (by linarith)
    have h1 := hno b hbX
    have : C * Real.exp (σ * b) ≤ K := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hK0 : 0 ≤ K := by positivity
    nlinarith

/-- **If RH fails, `λ₁` fails exponentially.** There is `δ > 0` such that for every `0 ≤ σ < δ` and
every `C`, `λ₁(a) < −C·e^{σa}` at arbitrarily large `a`. -/
theorem lam_fails_exponentially (hRH : ¬RiemannHypothesis) :
    ∃ δ > 0, ∀ σ, 0 ≤ σ → σ < δ → ∀ C X : ℝ, ∃ a, X < a ∧ lam a < -(C * Real.exp (σ * a)) := by
  unfold RiemannHypothesis at hRH
  push Not at hRH
  obtain ⟨s, hs, htriv, -, hre⟩ := hRH
  have hs' : IsNontrivialZero s := ⟨hs, fun ⟨n, hn⟩ => htriv n hn⟩
  refine ⟨|2 * s.re - 1|, abs_pos.2 (fun h => hre (by linarith)), fun σ hσ hlt C X =>
    lam_rate hs' hσ hlt C X⟩

end Pilot1ca

#print axioms Pilot1ca.zeros_of_lam_ge
#print axioms Pilot1ca.rh_iff_lam_subexp
#print axioms Pilot1ca.lam_rate
#print axioms Pilot1ca.lam_fails_exponentially
