import PhiDExp
import VinoStep
import VinoConst

/-! # Decay corollaries and the weak VMVT (round 250)

`lam_decay` without its three unused hypotheses, `lamO_decay_uncond` from `lam_dexp`, the absorption `c·a − 2πe^{a − ¼} ≤ c + c²`, and the `ε`-form of Vinogradov's mean value theorem from `VinoRec2`.
-/

open Real Complex MeasureTheory Set Filter Topology

namespace DecayCorollaries

open Pilot1ca Pilot1bt PilotWeil

/-- For every `c`, `c·a − 2π e^{a − d} ≤ M` for `a ≥ 1` (any `d ≤ 1/4`): the double exponential beats
every exponential rate. -/
theorem dexp_absorb (c : ℝ) (hc : 0 ≤ c) : ∀ a : ℝ, 1 ≤ a →
    c * a - 2 * π * Real.exp (a - 1 / 4) ≤ c + c ^ 2 := by
  intro a ha
  have hx : 0 ≤ a - 1 / 4 := by linarith
  have h2 := Real.pow_div_factorial_le_exp (a - 1 / 4) hx 2
  norm_num [Nat.factorial] at h2
  have hπ := Real.pi_gt_three
  have h3 : π * ((a - 1 / 4) ^ 2 / 2) ≤ π * Real.exp (a - 1 / 4) :=
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have h4 : 3 * (a - 1 / 4) ^ 2 ≤ π * (a - 1 / 4) ^ 2 :=
    mul_le_mul_of_nonneg_right hπ.le (sq_nonneg _)
  nlinarith [sq_nonneg (a - 1 / 4 - c / 6)]

/-- `PhiDecay.lam_decay` (round 133), verbatim statement: its hypotheses are superfluous given round
159's unconditional `lam_dexp`. -/
theorem lam_decay' {ι : Type*} {ρ : ι → ℂ} (_hz : ∀ i, Xi ((ρ i - 1 / 2) / Complex.I) = 0)
    (_hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (_hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    (_hEF : ∀ a, 1 ≤ a → WeilExplicit ρ (fun z => ghatC (PhiA a) a z ^ 2) (hsq (PhiA a) a))
    (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (-B * a) := by
  obtain ⟨K, hK, h⟩ := lam_dexp
  set c := 16 + |B|
  have hc : 0 ≤ c := by positivity
  refine ⟨K * Real.exp (c + c ^ 2), by positivity, fun a ha => (h a ha).trans ?_⟩
  rw [show K * Real.exp (c + c ^ 2) * Real.exp (-B * a) = K * Real.exp (c + c ^ 2 + -B * a) by
    rw [mul_assoc, ← Real.exp_add]]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
  have h1 := dexp_absorb c hc a ha
  have h2 : Real.exp (a - 1 / 4) ≤ Real.exp (2 * a) := Real.exp_le_exp.2 (by linarith)
  have h2' : π * Real.exp (a - 1 / 4) ≤ π * Real.exp (2 * a) := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hB : -|B| * a ≤ -B * a := by nlinarith [le_abs_self B]
  have hca : c * a = 16 * a + |B| * a := by simp only [c]; ring
  nlinarith

/-- `WeilDischarge.lamO_decay_uncond` (round 153), verbatim statement, from round 159's `lamO_dexp`. -/
theorem lamO_decay_uncond' (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lamO a ≤ K * Real.exp (-B * a) := by
  obtain ⟨K, hK, h⟩ := lamO_dexp
  set c := 16 + |B|
  have hc : 0 ≤ c := by positivity
  refine ⟨K * Real.exp (c + c ^ 2), by positivity, fun a ha => (h a ha).trans ?_⟩
  rw [show K * Real.exp (c + c ^ 2) * Real.exp (-B * a) = K * Real.exp (c + c ^ 2 + -B * a) by
    rw [mul_assoc, ← Real.exp_add]]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
  have h1 := dexp_absorb c hc a ha
  have hB : -|B| * a ≤ -B * a := by nlinarith [le_abs_self B]
  have hca : c * a = 16 * a + |B| * a := by simp only [c]; ring
  nlinarith

end DecayCorollaries

namespace VmvtWeak

open Finset

/-- `Vinogradov.esymm_eq_of_psum` (over `ℚ`), verbatim statement, from `VinoStep.esymm_eq_of_psum_field`. -/
theorem esymm_eq_of_psum' {s : ℕ} (x y : Fin s → ℚ)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ n, n ≤ s → (univ.val.map x).esymm n = (univ.val.map y).esymm n :=
  VinoStep.esymm_eq_of_psum_field (fun n hn _ => by exact_mod_cast (by omega : n ≠ 0)) x y h

/-- `Vinogradov.map_eq_of_psum`, verbatim statement, from `VinoStep.map_eq_of_psum_field`. -/
theorem map_eq_of_psum' {s : ℕ} (x y : Fin s → ℚ)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    univ.val.map x = univ.val.map y :=
  VinoStep.map_eq_of_psum_field (fun n hn _ => by exact_mod_cast (by omega : n ≠ 0)) x y h

/-- `VinoRec.vmvt_iter` (round 202), verbatim statement, from round 207's `vmvt_explicit`. -/
theorem vmvt_iter' {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ∃ C > 0, ∀ P : ℕ, 1 ≤ P → (Vinogradov.J (k + m * k) k P : ℝ) ≤ C * (P : ℝ) ^ (VinoRec.expo k m) :=
  ⟨VinoRec.Cvm k m, (VinoRec.vmvt_explicit hk m).1, (VinoRec.vmvt_explicit hk m).2⟩

end VmvtWeak

#print axioms DecayCorollaries.lam_decay'
#print axioms DecayCorollaries.lamO_decay_uncond'
#print axioms VmvtWeak.esymm_eq_of_psum'
#print axioms VmvtWeak.map_eq_of_psum'
#print axioms VmvtWeak.vmvt_iter'
