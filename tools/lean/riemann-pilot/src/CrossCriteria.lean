import WeilChiCriterion
import MertensOmega
import ShortPrimes
import WeilRate
import Zeta

/-! # Weil positivity modulo real zeros, and the missing Props stated (round 246)

`Q_χ ≥ 0` follows from GRH off the real axis (`QC_nonneg_of_cross`, `twins_nonneg_of_cross`); with `hS` it is GRH (`grh_of_cross`); one-sided Liouville bounds at every `θ > ½` give RH. The open inputs the density route and the `χ` chain would need are stated as named `Prop`s: `ZetaCritBound c`, `ConvexityBound`, `WeylBound`, `Lindelof`, `DensityHypothesis`, `NoRealZero χ`, `GRHCross χ`, `PsiOmegaSqrt`, `LittlewoodS1`, `FirstZeroAbove14`, `LamGradedConverse`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace CrossCriteria

open PsiOmega Pilot1ca Pilot1bt PilotWeil DirichletCharacter

/-! ### (A) Real zeros are invisible to even real probes -/

/-- `ĝ(iy) = ∫ g(u) e^{−yu} du` is real, for every real `g` (no parity needed). -/
theorem ghatC_I_mul (g : ℝ → ℝ) (a y : ℝ) :
    ghatC g a (I * y) = ((∫ u in (-a)..a, g u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
  unfold ghatC
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u _
  have e : I * (I * (y : ℂ)) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
    push_cast
    linear_combination (y * u : ℂ) * I_mul_I
  simp only
  rw [e, ← ofReal_exp]
  push_cast
  ring

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **Weil positivity for `L(s, χ)` without the Siegel hypothesis `hS`.** If every zero of `L(s, χ)` in
the critical strip is on the critical line or real, then `Q_χ(g) ≥ 0` for every probe whose `ĝ²` is a
strip test function. A real zero `β` has `τ = ±i|β − ½|`, and `ĝ(τ)` is real there, so its term
`2ĝ(τ)²` is `≥ 0`: the even-probe form cannot see real zeros. -/
theorem QC_nonneg_of_cross (hG : GoodChar χ)
    (hcross : ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0)
    {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) : 0 ≤ QC χ a g := by
  have h := (QC_hasSum hG hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
  have hre : (1 / 2 + I * tauC i).re = 1 / 2 - (tauC i).im := by simp; ring
  have him : (1 / 2 + I * tauC i).im = (tauC i).re := by simp
  rcases hcross _ hz h0 h1 with hl | hr
  · have hi : (tauC i).im = 0 := by linarith
    have e : tauC i = ((tauC i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [e, hsq_ofReal hp ha.le]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by norm_num) (hsq_nonneg _)
  · have hr' : (tauC i).re = 0 := by rw [← him]; exact hr
    have e : tauC i = I * ((tauC i).im : ℂ) := Complex.ext (by simp [hr']) (by simp)
    rw [e, ghatC_I_mul]
    set x : ℝ := ∫ u in (-a)..a, g u * Real.exp (-((tauC i).im * u))
    have e2 : (2 * ((x : ℝ) : ℂ) ^ 2 : ℂ) = ((2 * x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e2, ofReal_re]
    positivity

/-- The twin form, without `hS`: zeros on the line or real give `Q_χ(twin (box 1) λ) ≥ 0`. -/
theorem twins_nonneg_of_cross (hG : GoodChar χ)
    (hcross : ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0)
    {l : ℝ} (hl : 0 ≤ l) : 0 ≤ QC χ (l + 1) (twin (box 1) l) := by
  obtain ⟨K, hK⟩ := striptest_twin_box hl
  exact QC_nonneg_of_cross hG hcross (twin_probe (box_probe 1) hl) (by linarith) hK

/-- The converse direction of `grh_iff_twins` is the only place `hS` enters: with `hS` the cross
hypothesis is GRH. -/
theorem grh_of_cross (hcross : ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) : GRH χ := by
  intro s hs h0 h1
  rcases hcross s hs h0 h1 with h | h
  · exact h
  · exfalso
    have e : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [h])
    rw [e] at hs
    exact hS s.re h0 h1 hs

/-! ### (B) The θ-family Liouville route -/

/-- **RH from one-sided Liouville bounds at every exponent `θ > ½`.** Unlike `rh_of_liouville_bound`
(exponent exactly `½`), the hypothesis is the one RH is expected to give. -/
theorem rh_of_liouville_theta {ε : ℝ} (hε : ε ≠ 0)
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ c : ℝ, ∀ x : ℝ, 1 < x → ε * summ fLi x ≤ c * x ^ θ) :
    RiemannHypothesis := by
  intro s hs htriv h1
  have hs' : IsNontrivialZero s := ⟨hs, htriv⟩
  have key : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0 := fun ρ hρ => by
    rcases le_or_gt 1 ρ.re with h1' | h1'
    · exact zeta_ne_zero_re_ge_one h1'
    · obtain ⟨c, hc⟩ := h ((1 / 2 + ρ.re) / 2) (by linarith) (by linarith)
      exact zeta_ne_zero_of_liouville (by linarith) (by linarith) hε hc (by linarith)
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exact absurd (IsNontrivialZero.one_sub hs').1 (key _ (by simp; linarith))
  · exact heq
  · exact absurd hs (key s hgt)

/-! ### (C) The exact missing Props (well-typed; none is proved in the three layers, except `NoRealZero` at `chi3`, `chi4`, `chi7`, `chi8`, whose bodies are `WeilTwinGeneral.hS3`, `Dedekind4.hS4`, `WeilTwinGeneral.hS7`, `WeilTwinGeneral.hS8`) -/

/-- Pointwise growth exponent `c` for `ζ` on the critical line. -/
def ZetaCritBound (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ c

/-- The convexity bound (Lindelöf 1908: functional equation + Phragmén–Lindelöf + Stirling). -/
def ConvexityBound : Prop := ∀ ε > 0, ZetaCritBound (1 / 4 + ε)

/-- Weyl–Hardy–Littlewood (van der Corput's method). -/
def WeylBound : Prop := ∀ ε > 0, ZetaCritBound (1 / 6 + ε)

/-- The Lindelöf hypothesis. -/
def Lindelof : Prop := ∀ ε > 0, ZetaCritBound ε

/-- The density route's target (PAPER): pointwise `c` gives Ingham's exponent `2 + 4c`. -/
def InghamFromC (c : ℝ) : Prop :=
  ZetaCritBound c → ∀ ε > 0, ∃ B : ℝ, ShortWeil.DensityXi (2 + 4 * c + ε) B

/-- The density hypothesis in the stack's normalisation. -/
def DensityHypothesis : Prop := ∀ ε > 0, ∃ B : ℝ, ShortWeil.DensityXi (2 + ε) B

/-- Siegel-zero exclusion for one character (the `hS` of the χ chain). -/
def NoRealZero (χ : DirichletCharacter ℂ N) : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0

/-- GRH modulo real zeros (the cross hypothesis of `QC_nonneg_of_cross`). -/
def GRHCross (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0

/-- The hS-free Weil criterion (PAPER: the positivity-to-zeros direction needs a probe family whose
transform vanishes at the finitely many real zeros). -/
def WeilChiCrossCriterion (χ : DirichletCharacter ℂ N) : Prop :=
  (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC χ a g) ↔ GRHCross χ

/-- `ψ(x) − x = Ω±(√x)` (Ingham's twist of the Landau argument, PAPER). -/
def PsiOmegaSqrt : Prop :=
  ∃ c > 0, ∀ X : ℝ, (∃ x, X < x ∧ c * x ^ (1 / 2 : ℝ) < Chebyshev.psi x - x) ∧
    (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ (1 / 2 : ℝ)))

/-- Littlewood's `S₁(t) = O(log t)`: the wall law's remaining analytic input `hS1log`. -/
def LittlewoodS1 (G : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, G ≤ t → |S1 (Sz zetaOrd) G t| ≤ C * Real.log t

/-- The wall law's first-zero height input `h_height` at `G = 14`. -/
def FirstZeroAbove14 : Prop := ∀ p, (14 : ℝ) ≤ zetaOrd p

/-- The graded converse of `zeros_of_lam_ge` (missing: `weil_twins_rate` has it for twins only). -/
def LamGradedConverse : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → (∀ s : ℂ, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) →
    ∃ C : ℝ, ∀ a : ℝ, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lam a

end CrossCriteria

#print axioms CrossCriteria.ghatC_I_mul
#print axioms CrossCriteria.QC_nonneg_of_cross
#print axioms CrossCriteria.twins_nonneg_of_cross
#print axioms CrossCriteria.grh_of_cross
#print axioms CrossCriteria.rh_of_liouville_theta
