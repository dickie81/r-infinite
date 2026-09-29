import Mathlib
import WeilCriterion
import Zeta
import LandauLaplace
import TwinLandau

/-! # Weil's criterion for `ζ` with no finiteness hypothesis (round 220)

Round 157's `rh_of_weil_finite` needs `hfin`: only finitely many zeros off the critical line. Its
proof integrates the twin boxes' form against a weight and needs a zero of maximal `|Im t|`. This file
removes `hfin` with Landau's theorem for Laplace transforms (`LandauLaplace.lean`).

**The transform.** For the box `g₀ = box 1` and its twins `g_λ = twin g₀ λ`, the explicit formula
(`weilExplicit_twinbox_zeta`) gives `Q(λ) := Q(g_λ) = Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`, where
`P_ρ = 2(ρ − ½) = 2i·t_ρ`. For `Re z > 1` it can be integrated term by term:
`∫_0^∞ Q(λ)e^{−zλ}dλ = F(z) := Σ_ρ ĝ₀(t_ρ)²(2/z + 1/(z − P_ρ) + 1/(z + P_ρ))` (`lap_eq_Fw`).

**The argument** (`line_of_weil_twins`). Suppose `Q(λ) ≥ 0` for every `λ ≥ 0`.
1. `F` is holomorphic off its poles `0, ±P_ρ`, which are locally finite (`Fw_differentiableAt`). No
   pole is real, because `ζ ≠ 0` on `(0, 1)`. Near every real `c > 0`, `F` is holomorphic and equals
   the transform, by the identity theorem on a thin strip. Landau's theorem then makes the integral
   converge on all of `Re z > 0` (`conv_gt`).
2. An off-line zero gives a pole `P` with `Re P > 0`. Take the pole on that horizontal line with the
   largest real part, `p`. On a thin horizontal strip to the right of `p` there is no pole, so `F`
   equals the transform, which is continuous at `p`. But `F(z) = G(z) + R/(z − p)` with `G`
   continuous at `p` and `R = N·ĝ₀(t_p)² ≠ 0` (`N ≥ 1` counts the zeros with `±P_ρ = p`;
   `ĝ₀ ≠ 0` off the real axis, `ghat_box_ne`). That is a contradiction.

The argument itself is `TwinLandau.lean` (round 225), generic over the zero family; this file
supplies the `ζ` data (`twinData_zeta`).

**Results.**
* `rh_of_weil_twins`: `Q(twin (box 1) λ) ≥ 0` for every `λ ≥ 0` gives Mathlib's `RiemannHypothesis`.
* `rh_of_weil`: `Q ≥ 0` for every probe gives `RiemannHypothesis`.

It is an equivalence-type statement, with no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory Metric

open scoped Nat

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil LandauLaplace

instance : Countable ZIdx := zetaEquiv.injective.countable

/-- The pole `P_ρ = 2(ρ − ½) = 2i·t_ρ`. -/
def poleP (q : ZIdx) : ℂ := 2 * (zetaZeroFamily q - 1 / 2)

/-- The weight `ĝ₀(t_ρ)²`, `g₀ = box 1`. -/
def cw (q : ZIdx) : ℂ := ghatC (box 1) 1 (ordi zetaZeroFamily q) ^ 2

theorem two_I_ordi (q : ZIdx) : 2 * I * ordi zetaZeroFamily q = poleP q := by
  unfold ordi poleP; field_simp

theorem nontrivial_zZF (q : ZIdx) : IsNontrivialZero (zetaZeroFamily q) := q.1.2

theorem abs_re_poleP (q : ZIdx) : |(poleP q).re| < 1 := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  have e : (poleP q).re = 2 * (zetaZeroFamily q).re - 1 := by unfold poleP; simp; ring
  rw [e, abs_lt]; constructor <;> linarith

theorem im_poleP_ne (q : ZIdx) : (poleP q).im ≠ 0 := by
  have e : (poleP q).im = 2 * (zetaZeroFamily q).im := by unfold poleP; simp
  rw [e]; exact mul_ne_zero two_ne_zero (im_zetaZeroFamily_ne q)

theorem summable_cw : Summable fun q : ZIdx => ‖cw q‖ :=
  summable_norm_iff.2 (weilQ_eq_zero_sum (box_probe 1) one_pos weilExplicit_box_zeta).summable

/-! ## The poles are locally finite -/

theorem norm_zZF_sub (q : ZIdx) : ‖zetaZeroFamily q - 1 / 2‖ = ‖tau (zetaEquiv q).2‖ := by
  rw [← rhoXi_zetaEquiv q]
  unfold rhoXi
  split_ifs <;> simp

theorem finite_poleP (R : ℝ) : {q : ZIdx | ‖poleP q‖ ≤ R}.Finite := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ := (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  set K : ℝ := max (R ^ 2 / 4) 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {i : ZeroIdx (sqF Xi) | ‖i.1‖ ≤ K}.Finite := by
    have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [mem_ofPred_eq, not_lt]
    rw [norm_inv]
    have hi' : ‖i.1‖ ≤ K := hi
    have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx_ne_zero i)
    exact inv_anti₀ hp hi'
  refine ((Set.finite_univ.prod hfin).preimage zetaEquiv.injective.injOn).subset fun q hq => ?_
  simp only [mem_preimage, Set.mem_prod, mem_univ, true_and, mem_ofPred_eq]
  have hq' : ‖poleP q‖ ≤ R := hq
  have e1 : ‖poleP q‖ = 2 * ‖tau (zetaEquiv q).2‖ := by
    unfold poleP; rw [norm_mul, norm_zZF_sub]; simp
  have e2 : ‖(zetaEquiv q).2.1‖ = ‖tau (zetaEquiv q).2‖ ^ 2 := by rw [← tau_sq, norm_pow]
  rw [e2]
  have h0 := norm_nonneg (tau (zetaEquiv q).2)
  have : ‖tau (zetaEquiv q).2‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  exact this.trans (le_max_left _ _)

/-- **The explicit formula for the twins**: `Q(twin λ) = Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`. -/
theorem hasSum_wq {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q => cw q * (2 + cexp (l * poleP q) + cexp (-(l * poleP q)))) (weilQ (l + 1) (twin (box 1) l) : ℂ) := by
  have h := weilQ_eq_zero_sum (twin_probe (box_probe 1) hl) (by linarith) (weilExplicit_twinbox_zeta hl)
  convert h using 1
  funext q
  rw [ghatC_twin one_pos (box_probe 1) hl, TwinLandau.twin_sq, two_I_ordi]
  rfl

/-- The weight as a function of the pole: `G(p) = ĝ₀(p/2i)²`. -/
def Gbox (p : ℂ) : ℂ := ghatC (box 1) 1 (p / (2 * I)) ^ 2

/-- **The `ζ` data of the twin-form Landau argument.** -/
theorem twinData_zeta : TwinLandau.TwinData poleP cw Gbox (fun l => weilQ (l + 1) (twin (box 1) l)) where
  summ := summable_cw
  re_lt := abs_re_poleP
  im_ne := im_poleP_ne
  finite := finite_poleP
  c_eq q := by unfold cw Gbox; rw [← two_I_ordi]; congr 2; field_simp
  G_even p := by
    unfold Gbox; rw [show -p / (2 * I) = -(p / (2 * I)) by ring, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine pow_ne_zero 2 (ghat_box_ne ?_)
    have e : (p / (2 * I)).im = -p.re / 2 := by simp [Complex.div_im]; ring
    rw [e]; intro h; linarith
  hasSum l hl := hasSum_wq hl

theorem re_poleP (q : ZIdx) : (poleP q).re = 2 * (zetaZeroFamily q).re - 1 := by
  unfold poleP; simp; ring

/-- **Weil's criterion, twin boxes only.** If `Q(twin (box 1) λ) ≥ 0` for every `λ ≥ 0`, every
nontrivial zero of `ζ` lies on the critical line. -/
theorem line_of_weil_twins (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) (q0 : ZIdx) :
    (zetaZeroFamily q0).re = 1 / 2 := by
  have h := TwinLandau.abs_re_le twinData_zeta (C := 0) le_rfl (fun l hl => by simpa using hQ l hl) q0
  rw [re_poleP] at h
  have := abs_nonpos_iff.1 h
  linarith

/-- **Weil's criterion for `ζ`, twin boxes only, no finiteness hypothesis.** -/
theorem rh_of_weil_twins (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) :
    RiemannHypothesis := by
  intro s hs htriv _
  exact line_of_weil_twins hQ ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- **Weil's criterion for `ζ`, no finiteness hypothesis.** If `Q ≥ 0` for every probe at every
support, Mathlib's `RiemannHypothesis` holds. -/
theorem rh_of_weil (hQ : ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g) :
    RiemannHypothesis :=
  rh_of_weil_twins fun l hl => hQ _ _ (by linarith) (twin_probe (box_probe 1) hl)

/-! ## The graded equivalence -/

/-- **Weil positivity, graded.** For `σ ≥ 0`: `Q(twin (box 1) λ) ≥ −C·e^{σλ}` for some `C` and all
`λ ≥ 0` if and only if every nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ σ`. The exponential rate at
which the twin form can go negative is exactly `2Θ − 1`, `Θ = sup Re ρ`. -/
theorem weil_twins_rate {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ weilQ (l + 1) (twin (box 1) l)) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ := by
  constructor
  · rintro ⟨C, h⟩ s hs
    have := TwinLandau.abs_re_le twinData_zeta hσ h ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩
    rwa [re_poleP] at this
  · intro h
    exact (TwinLandau.rate_iff twinData_zeta hσ).2 fun q => by rw [re_poleP]; exact h _ (nontrivial_zZF q)

/-- **RH ⟺ the twin form's defect is subexponential.** -/
theorem rh_iff_twins_subexp :
    RiemannHypothesis ↔
      ∀ σ > 0, ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ weilQ (l + 1) (twin (box 1) l) := by
  constructor
  · intro hRH σ hσ
    refine (weil_twins_rate hσ.le).2 fun s hs => ?_
    have h1 : s ≠ 1 := fun e => by have := hs.re_lt_one; rw [e, one_re] at this; exact lt_irrefl _ this
    rw [hRH s hs.1 hs.2 h1]; norm_num; exact hσ.le
  · intro h s hs htriv h1
    have hs' : IsNontrivialZero s := ⟨hs, htriv⟩
    have key : ∀ σ > 0, |2 * s.re - 1| ≤ σ := fun σ hσ => (weil_twins_rate hσ.le).1 (h σ hσ) s hs'
    have : |2 * s.re - 1| = 0 := le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      simpa using key ε hε) (abs_nonneg _)
    rw [abs_eq_zero] at this; linarith

end Pilot1ca

#print axioms Pilot1ca.rh_of_weil_twins
#print axioms Pilot1ca.rh_of_weil
#print axioms Pilot1ca.weil_twins_rate
#print axioms Pilot1ca.rh_iff_twins_subexp
