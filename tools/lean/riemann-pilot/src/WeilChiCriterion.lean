import Mathlib
import WeilChi
import WeilCriterion
import TwinLandau
import PrimeRaces
import WeilRate

/-! # Weil's criterion for Dirichlet L-functions (round 225) -/

open Real Complex MeasureTheory Filter Topology Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter Pilot1ca Pilot1bt PilotWeil

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **Weil's form for `L(s, χ)`** at support `[−a, a]`, in its Guinand–Weil presentation:
`Q_χ(g) = g_h(0)log(N/π) + (1/2π)∫ĝ(r)² Re ψ((½ + δ)/2 + ir/2)dr − 2Σ Λ(n)χ(n)n^{−1/2}g_h(log n)`,
`h = ĝ²`. No zero of `L` enters. -/
def QC (χ : DirichletCharacter ℂ N) (a : ℝ) (g : ℝ → ℝ) : ℝ := weilRHSC χ (hsq g a)

/-- The generalized Riemann hypothesis for `L(s, χ)`: every zero in the critical strip is on the
line. -/
def GRH (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

variable (hG : GoodChar χ)
include hG

/-- **The explicit formula for a probe**: `Q_χ(g) = Σ_u 2ĝ(τ_u)²`. -/
theorem QC_hasSum {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 * ghatC g a (tauC i) ^ 2) (QC χ a g : ℂ) :=
  weil_XiC hG hK (fun t => even_ghat_sq hp.even a t) (hsq_ofReal hp ha.le)

/-! ## Zeros of `Ξ_χ` and of `L(s, χ)` -/

omit hG in
theorem LFunction_of_LamG {s : ℂ} (hs : 0 < s.re) (h : LamG χ s = 0) : LFunction χ s = 0 := by
  by_contra hL; exact LamG_ne_zero hs hL h

/-- Each `τ_u` gives a zero `½ + iτ_u` of `L(s, χ)` in the critical strip. -/
theorem zero_of_tau (i : ZeroIdx (sqF (XiC χ))) :
    LFunction χ (1 / 2 + I * tauC i) = 0 ∧ 0 < (1 / 2 + I * tauC i).re ∧
      (1 / 2 + I * tauC i).re < 1 := by
  have him := abs_lt.1 (tauC_im hG i)
  have hre : (1 / 2 + I * tauC i).re = 1 / 2 - (tauC i).im := by simp; ring
  refine ⟨LFunction_of_LamG (by rw [hre]; linarith) (XiC_tau hG i), by rw [hre]; linarith,
    by rw [hre]; linarith⟩

/-- Every zero of `L(s, χ)` in the critical strip is `½ ± iτ_u` for some `u`. -/
theorem tau_of_zero {s : ℂ} (hs : LFunction χ s = 0) (h0 : 0 < s.re) :
    ∃ i : ZeroIdx (sqF (XiC χ)), tauC i = (s - 1 / 2) / I ∨ tauC i = -((s - 1 / 2) / I) := by
  set t := (s - 1 / 2) / I
  have hst : 1 / 2 + I * t = s := by simp only [t]; field_simp; ring
  have hXt : XiC χ t = 0 := by
    unfold XiC; rw [hst, LamG]; rw [completed_eq_mul h0, hs]; simp
  have hF := sqF_differentiable (differentiable_XiC hG) (XiC_even hG)
  have hF0 : sqF (XiC χ) 0 ≠ 0 := by rw [sqF_zero]; exact XiC_zero_ne hG
  have hu : sqF (XiC χ) (t ^ 2) = 0 := by rw [sqF_sq (XiC_even hG)]; exact hXt
  have hord : ordN (sqF (XiC χ)) (t ^ 2) ≠ 0 := (ordN_ne_zero_iff hF hF0 _).2 hu
  refine ⟨⟨t ^ 2, ⟨0, Nat.pos_of_ne_zero hord⟩⟩, ?_⟩
  have hsq : tauC (χ := χ) ⟨t ^ 2, ⟨0, Nat.pos_of_ne_zero hord⟩⟩ ^ 2 = t ^ 2 := tauC_sq _
  exact sq_eq_sq_iff_eq_or_eq_neg.1 hsq

/-! ## The twin data -/

/-- `G(p) = 2ĝ₀(p/2i)²`, `g₀ = box 1`. -/
def GboxC (p : ℂ) : ℂ := 2 * ghatC (box 1) 1 (p / (2 * I)) ^ 2

theorem finite_tauC (R : ℝ) : {i : ZeroIdx (sqF (XiC χ)) | ‖2 * I * tauC i‖ ≤ R}.Finite := by
  have hs : Summable fun i : ZeroIdx (sqF (XiC χ)) => ‖i.1⁻¹‖ := (hadamard_XiC hG).summ
  set K : ℝ := max (R ^ 2 / 4) 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {i : ZeroIdx (sqF (XiC χ)) | ‖i.1‖ ≤ K}.Finite := by
    have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [mem_ofPred_eq, not_lt]
    rw [norm_inv]
    have hi' : ‖i.1‖ ≤ K := hi
    have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdxC_ne_zero hG i)
    exact inv_anti₀ hp hi'
  refine hfin.subset fun i hi => ?_
  have hi' : ‖2 * I * tauC i‖ ≤ R := hi
  have e1 : ‖2 * I * tauC i‖ = 2 * ‖tauC i‖ := by simp
  have e2 : ‖i.1‖ = ‖tauC i‖ ^ 2 := by rw [← tauC_sq, norm_pow]
  show ‖i.1‖ ≤ K
  rw [e2]
  have h0 := norm_nonneg (tauC i)
  have : ‖tauC i‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  exact this.trans (le_max_left _ _)

omit [NeZero N] hG in
theorem striptest_twin_box {l : ℝ} (hl : 0 ≤ l) :
    ∃ K, StripTest (fun z => ghatC (twin (box 1) l) (l + 1) z ^ 2) K := by
  have hp := box_probe 1
  obtain ⟨K, hK⟩ := ghat_antitone_strip one_pos hp.even box_antitone box_nonneg hp.intervalIntegrable
  have hT := striptest_mul_sq (G := ghatC (box 1) 1) (m := fun z => 2 * Complex.cos (l * z))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => norm_two_cos_strip hl ht)
  have e : (fun z => ghatC (twin (box 1) l) (l + 1) z ^ 2)
      = fun z => (2 * Complex.cos (l * z) * ghatC (box 1) 1 z) ^ 2 := by
    funext z; rw [ghatC_twin one_pos hp hl]
  exact ⟨_, e ▸ hT⟩

/-- **The data of the twin-form Landau argument for `L(s, χ)`**, when `L(σ, χ) ≠ 0` on `(0, 1)`. -/
theorem twinData_chi (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    TwinLandau.TwinData (fun i : ZeroIdx (sqF (XiC χ)) => 2 * I * tauC i)
      (fun i => 2 * ghatC (box 1) 1 (tauC i) ^ 2) GboxC
      (fun l => QC χ (l + 1) (twin (box 1) l)) where
  summ := by
    obtain ⟨K, hK⟩ := striptest_antitone one_pos (box_probe 1).even box_antitone box_nonneg
      (box_probe 1).intervalIntegrable
    have h := QC_hasSum hG (box_probe 1) one_pos hK
    exact summable_norm_iff.2 (by simpa using h.summable)
  re_lt i := by
    have := tauC_im hG i
    have e : (2 * I * tauC i).re = -2 * (tauC i).im := by simp
    rw [e, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]; linarith
  im_ne i := by
    have e : (2 * I * tauC i).im = 2 * (tauC i).re := by simp
    rw [e]
    intro h
    have hre : (tauC i).re = 0 := by linarith
    obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
    set σ : ℝ := (1 / 2 + I * tauC i).re
    have e2 : 1 / 2 + I * tauC i = (σ : ℂ) := Complex.ext (by simp [σ]) (by simp [hre])
    rw [e2] at hz
    exact hS σ h0 h1 hz
  finite R := finite_tauC hG R
  c_eq i := by unfold GboxC; congr 3; field_simp
  G_even p := by
    unfold GboxC; rw [show -p / (2 * I) = -(p / (2 * I)) by ring, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine mul_ne_zero two_ne_zero (pow_ne_zero 2 (ghat_box_ne ?_))
    have e : (p / (2 * I)).im = -p.re / 2 := by simp [Complex.div_im]; ring
    rw [e]; intro h; linarith
  hasSum l hl := by
    obtain ⟨K, hK⟩ := striptest_twin_box hl
    have h := QC_hasSum hG (twin_probe (box_probe 1) hl) (by linarith) hK
    convert h using 1
    funext i
    rw [ghatC_twin one_pos (box_probe 1) hl, TwinLandau.twin_sq]
    ring_nf

/-! ## The criterion -/

/-- Under GRH every `τ_u` is real. -/
theorem tau_real_of_GRH (hGRH : GRH χ) (i : ZeroIdx (sqF (XiC χ))) : (tauC i).im = 0 := by
  obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
  have := hGRH _ hz h0 h1
  have hre : (1 / 2 + I * tauC i).re = 1 / 2 - (tauC i).im := by simp; ring
  linarith

/-- **GRH ⟹ `Q_χ ≥ 0`** for every probe whose `ĝ²` is a strip test function. -/
theorem QC_nonneg_of_GRH (hGRH : GRH χ) {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) : 0 ≤ QC χ a g := by
  have h := (QC_hasSum hG hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  have hi := tau_real_of_GRH hG hGRH i
  have e : tauC i = ((tauC i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
  rw [e, hsq_ofReal hp ha.le]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (by norm_num) (hsq_nonneg _)

/-- **Weil's criterion for `L(s, χ)`, twin boxes.** With `L(σ, χ) ≠ 0` on `(0, 1)`:
GRH for `χ` holds iff `Q_χ(twin (box 1) λ) ≥ 0` for every `λ ≥ 0`. -/
theorem grh_iff_twins (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC χ (l + 1) (twin (box 1) l) := by
  have := countable_ZeroIdxC hG
  constructor
  · intro hGRH l hl
    obtain ⟨K, hK⟩ := striptest_twin_box hl
    exact QC_nonneg_of_GRH hG hGRH (twin_probe (box_probe 1) hl) (by linarith) hK
  · intro hQ s hs h0 h1
    obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
    have hb := TwinLandau.abs_re_le (twinData_chi hG hS) (C := 0) le_rfl
      (fun l hl => by simpa using hQ l hl) i
    have e : (2 * I * tauC i).re = -2 * (tauC i).im := by simp
    rw [e, abs_mul, show |(-2 : ℝ)| = 2 by norm_num] at hb
    have him : (tauC i).im = 0 := abs_nonpos_iff.1 (by linarith [abs_nonneg (tauC i).im])
    have ht : ((s - 1 / 2) / I).im = 0 := by
      rcases hi with h | h
      · rw [← h]; exact him
      · rw [← neg_neg ((s - 1 / 2) / I), ← h, neg_im, him, neg_zero]
    have e2 : ((s - 1 / 2) / I).im = -(s.re - 1 / 2) := by simp
    linarith

/-- **Weil positivity for `L(s, χ)`, graded.** For `σ ≥ 0`: `Q_χ(twin (box 1) λ) ≥ −C·e^{σλ}` for
some `C` and all `λ ≥ 0` iff every zero of `L(s, χ)` in the critical strip has `|2 Re ρ − 1| ≤ σ`. -/
theorem twins_rate (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QC χ (l + 1) (twin (box 1) l)) ↔
      ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ := by
  have := countable_ZeroIdxC hG
  rw [TwinLandau.rate_iff (twinData_chi hG hS) hσ]
  have e : ∀ i : ZeroIdx (sqF (XiC χ)), |(2 * I * tauC i).re| = |2 * (1 / 2 + I * tauC i).re - 1| := by
    intro i; congr 1; simp; ring
  constructor
  · intro h s hs h0 _
    obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
    have hb := h i
    rw [e] at hb
    have hst : (1 / 2 + I * ((s - 1 / 2) / I)) = s := by field_simp; ring
    rcases hi with hi | hi
    · rwa [hi, hst] at hb
    · rw [hi] at hb
      have : (1 / 2 + I * -((s - 1 / 2) / I)).re = 1 - s.re := by
        rw [show 1 / 2 + I * -((s - 1 / 2) / I) = 1 - (1 / 2 + I * ((s - 1 / 2) / I)) by ring, hst]; simp
      rw [this] at hb
      rw [show 2 * (1 - s.re) - 1 = -(2 * s.re - 1) by ring, abs_neg] at hb
      exact hb
  · intro h i
    obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
    rw [e]; exact h _ hz h0 h1

/-! ## The ground-energy layer -/

omit [NeZero N] hG in
/-- A probe whose `ĝ²` is a strip test function (every monotone profile and every twin). -/
def ProbeS (a : ℝ) (g : ℝ → ℝ) : Prop := Probe a g ∧ ∃ K, StripTest (fun z => ghatC g a z ^ 2) K

omit [NeZero N] hG in
theorem probeS_twin {l : ℝ} (hl : 0 ≤ l) : ProbeS (l + 1) (twin (box 1) l) :=
  ⟨twin_probe (box_probe 1) hl, striptest_twin_box hl⟩

/-- **A lower bound of exponential rate `σ` on `Q_χ/‖g‖²` is a zero-free half-plane.** If
`Q_χ(g) ≥ −C·e^{σa}‖g‖²` for every probe at every support `a ≥ 1`, every zero of `L(s, χ)` in the
critical strip has `|2 Re ρ − 1| ≤ σ`. -/
theorem zeros_of_QC_ge (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) {C σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ a, 1 ≤ a → ∀ g, ProbeS a g → -(C * Real.exp (σ * a)) * normSq g ≤ QC χ a g) :
    ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ := by
  refine (twins_rate hG hS hσ).1 ⟨4 * (|C| * Real.exp σ), fun l hl => ?_⟩
  have h1 := h (l + 1) (by linarith) _ (probeS_twin hl)
  have hN := normSq_twin_le l
  have hN0 := normSq_nonneg (twin (box 1) l)
  have e : Real.exp (σ * (l + 1)) = Real.exp σ * Real.exp (σ * l) := by
    rw [← Real.exp_add]; ring_nf
  rw [e] at h1
  have hC : C * (Real.exp σ * Real.exp (σ * l)) ≤ |C| * (Real.exp σ * Real.exp (σ * l)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hp : 0 ≤ |C| * (Real.exp σ * Real.exp (σ * l)) := by positivity
  nlinarith

/-- **GRH for `χ` ⟺ `Q_χ/‖g‖²` has no negative part of exponential rate.** -/
theorem grh_iff_QC_subexp (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → ∀ g, ProbeS a g →
      -(C * Real.exp (σ * a)) * normSq g ≤ QC χ a g := by
  constructor
  · intro hGRH σ _
    refine ⟨0, fun a ha g hg => ?_⟩
    obtain ⟨K, hK⟩ := hg.2
    simpa using QC_nonneg_of_GRH hG hGRH hg.1 (by linarith) hK
  · intro h s hs h0 h1
    have key : ∀ σ > 0, |2 * s.re - 1| ≤ σ := fun σ hσ => by
      obtain ⟨C, hC⟩ := h σ hσ
      exact zeros_of_QC_ge hG hS hσ.le hC s hs h0 h1
    have : |2 * s.re - 1| = 0 := le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      simpa using key ε hε) (abs_nonneg _)
    rw [abs_eq_zero] at this; linarith

/-- **An off-line zero makes `Q_χ` fail at an exponential rate.** A zero of `L(s, χ)` in the strip
with `|2 Re ρ − 1| > σ` gives, for every `C` and `X`, a support `a > X` and a probe `g` with
`Q_χ(g) < −C·e^{σa}‖g‖²`. -/
theorem QC_fails_rate (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) {s : ℂ}
    (hs : LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) {σ : ℝ} (hσ : 0 ≤ σ)
    (hlt : σ < |2 * s.re - 1|) (C X : ℝ) :
    ∃ a, X < a ∧ ∃ g, ProbeS a g ∧ QC χ a g < -(C * Real.exp (σ * a)) * normSq g := by
  have := countable_ZeroIdxC hG
  by_contra hno
  push Not at hno
  have D := twinData_chi hG hS
  set Sc := ∑' i, ‖(fun i : ZeroIdx (sqF (XiC χ)) => 2 * ghatC (box 1) 1 (tauC i) ^ 2) i‖
  have hSc : 0 ≤ Sc := tsum_nonneg fun _ => norm_nonneg _
  set X' := max X 0
  have hrate : ∀ i : ZeroIdx (sqF (XiC χ)), |(2 * I * tauC i).re| ≤ σ := by
    refine (TwinLandau.rate_iff D hσ).1 ⟨4 * (|C| * Real.exp σ) + 4 * Sc * Real.exp X', fun l hl => ?_⟩
    have hsmall : -(4 * Sc * Real.exp X') ≤ QC χ (l + 1) (twin (box 1) l) ∨
        -(4 * (|C| * Real.exp σ) * Real.exp (σ * l)) ≤ QC χ (l + 1) (twin (box 1) l) := by
      rcases le_or_gt l X' with hlX | hlX
      · left
        have hA := TwinLandau.abs_Aw_le D.toTwinPoles hl
        rw [TwinLandau.Aw_eq D hl] at hA
        have : Real.exp l ≤ Real.exp X' := Real.exp_le_exp.2 hlX
        have := neg_abs_le (QC χ (l + 1) (twin (box 1) l))
        nlinarith
      · right
        have h1' := hno (l + 1) (by linarith [le_max_left X 0]) _ (probeS_twin hl)
        have hN := normSq_twin_le l
        have hN0 := normSq_nonneg (twin (box 1) l)
        have e : Real.exp (σ * (l + 1)) = Real.exp σ * Real.exp (σ * l) := by
          rw [← Real.exp_add]; ring_nf
        rw [e] at h1'
        have hC : C * (Real.exp σ * Real.exp (σ * l)) ≤ |C| * (Real.exp σ * Real.exp (σ * l)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        have hp : 0 ≤ |C| * (Real.exp σ * Real.exp (σ * l)) := by positivity
        nlinarith
    have hE : 1 ≤ Real.exp (σ * l) := Real.one_le_exp (by positivity)
    have hP1 : 0 ≤ 4 * (|C| * Real.exp σ) := by positivity
    have hP2 : 0 ≤ 4 * Sc * Real.exp X' := by positivity
    rcases hsmall with hsm | hsm <;> nlinarith
  obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
  have hb := hrate i
  have e : ∀ t : ℂ, |(2 * I * t).re| = |2 * (1 / 2 + I * t).re - 1| := fun t => by
    congr 1; simp; ring
  rw [e] at hb
  have hst : (1 / 2 + I * ((s - 1 / 2) / I)) = s := by field_simp; ring
  refine absurd ?_ (not_le.2 hlt)
  rcases hi with hi | hi
  · rwa [hi, hst] at hb
  · rw [hi] at hb
    have : (1 / 2 + I * -((s - 1 / 2) / I)).re = 1 - s.re := by
      rw [show 1 / 2 + I * -((s - 1 / 2) / I) = 1 - (1 / 2 + I * ((s - 1 / 2) / I)) by ring, hst]; simp
    rw [this, show 2 * (1 - s.re) - 1 = -(2 * s.re - 1) by ring, abs_neg] at hb
    exact hb

omit hG in
/-- The hypotheses hold when `χ` is primitive, real and has nonnegative partial sums. -/
theorem goodChar_of_sums (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hsum : ∀ x, 0 ≤ summ (cR χ) x) : GoodChar χ :=
  ⟨hχ1, hq, hprim, by
    simpa using LFunction_ne_zero_of_sums_nonneg hχ1 hq hsum (σ := 1 / 2) (by norm_num)⟩

end PsiOmega

/-! ## `χ₋₃`, `χ₋₄`, `χ₋₈` -/

namespace PsiOmega

open Pilot1ca Pilot1bt DirichletCharacter

theorem sums_chi3 : ∀ x, 0 ≤ summ (cR chi3) x :=
  summ_nonneg_of_sum fun n => by rw [sum_chi3]; split_ifs <;> norm_num

theorem sums_chi4 : ∀ x, 0 ≤ summ (cR chi4) x :=
  summ_nonneg_of_sum fun n => by rw [sum_chi4]; split_ifs <;> norm_num

theorem sums_chi8 : ∀ x, 0 ≤ summ (cR chi8) x :=
  summ_nonneg_of_sum fun n => by rw [sum_chi8]; split_ifs <;> norm_num

theorem good_chi3 : GoodChar chi3 :=
  goodChar_of_sums chi3_ne_one chi3_isQuadratic chi3_isPrimitive sums_chi3
theorem good_chi4 : GoodChar chi4 :=
  goodChar_of_sums chi4_ne_one chi4_isQuadratic chi4_isPrimitive sums_chi4
theorem good_chi8 : GoodChar chi8 :=
  goodChar_of_sums chi8_ne_one chi8_isQuadratic chi8_isPrimitive sums_chi8

/-- **Weil's criterion for `L(s, χ₋₄)`**: GRH for `χ₋₄` iff `Q_{χ₋₄}(twin (box 1) λ) ≥ 0` for all `λ ≥ 0`. -/
theorem grh_iff_twins_chi4 : GRH chi4 ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC chi4 (l + 1) (twin (box 1) l) :=
  grh_iff_twins good_chi4 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ

theorem grh_iff_twins_chi3 : GRH chi3 ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC chi3 (l + 1) (twin (box 1) l) :=
  grh_iff_twins good_chi3 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi3_ne_one chi3_isQuadratic sums_chi3 hσ

theorem grh_iff_twins_chi8 : GRH chi8 ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC chi8 (l + 1) (twin (box 1) l) :=
  grh_iff_twins good_chi8 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ

/-- **The graded criterion for `χ₋₄`.** -/
theorem twins_rate_chi4 {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QC chi4 (l + 1) (twin (box 1) l)) ↔
      ∀ s : ℂ, LFunction chi4 s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ :=
  twins_rate good_chi4 (fun _ hσ' _ =>
    LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ') hσ

/-- **GRH for `χ₋₄` ⟺ `Q_{χ₋₄}/‖g‖²` has no negative part of exponential rate.** -/
theorem grh_iff_QC_subexp_chi4 :
    GRH chi4 ↔ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → ∀ g, ProbeS a g →
      -(C * Real.exp (σ * a)) * normSq g ≤ QC chi4 a g :=
  grh_iff_QC_subexp good_chi4 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ

end PsiOmega

#print axioms PsiOmega.QC_nonneg_of_GRH
#print axioms PsiOmega.grh_iff_twins
#print axioms PsiOmega.twins_rate
#print axioms PsiOmega.zeros_of_QC_ge
#print axioms PsiOmega.grh_iff_QC_subexp
#print axioms PsiOmega.QC_fails_rate
#print axioms PsiOmega.grh_iff_twins_chi4
#print axioms PsiOmega.grh_iff_twins_chi3
#print axioms PsiOmega.grh_iff_twins_chi8
#print axioms PsiOmega.twins_rate_chi4
#print axioms PsiOmega.grh_iff_QC_subexp_chi4
