import Mathlib
import TwinLandau
import WeilChiCriterion
import WeilRate
import DHExplicit
import DHColumn
import DHRealAxis
import DHForm

/-! # The dh column of the substitution matrix, part 2: the twin form

The Davenport–Heilbronn instance of the twin-form Landau argument (`TwinLandau.lean`) and its
refutations. `twinData_dh` is the exact analogue of `twinData_zeta` (WeilLandau.lean) and
`twinData_chi` (WeilChiCriterion.lean) in the normalisation of `QDH`: poles `P_u = 2iτ_u` over the
zeros `±τ_u` of `Ξ₃(t) = Ξ_dh(3t)`, weights `2ĝ₀(τ_u)² = GboxC(P_u)`, `g₀ = box 1`, and
`Q(λ) = Q_dh(twin (box 1) λ)` at support `λ + 1`. Its fields: `|Re P_u| < 1` from `tau3_im_lt`
(DHColumn.lean), `Im P_u ≠ 0` from `XiDH_I_mul_ne_zero` (DHRealAxis.lean: `Λ_dh` has no real zero),
local finiteness from `hadamard_XiDH3`, and the sums from `QDH_hasSum` with `striptest_twin_box`.

**The scaling.** A zero `s = ½ + 3iτ_u` of `dh` (`dh_zero_of_XiDH3`, `tau3_of_dh_zero`) has
`|2 Re s − 1| = 6|Im τ_u| = 3|Re P_u|` (`abs_two_re_sub_one_eq`, `exists_dh_zero_of_tau3`), so the
rate `σ` of the twin form `Q_dh(twin (box 1) λ)` measures `|2 Re s − 1| ≤ 3σ`.

Each declaration (left) and the pilot declaration it is the dh column of (right):

* `twinData_dh` — `twinData_zeta` (WeilLandau.lean:119), `twinData_chi` (WeilChiCriterion.lean:110)
* `dhRH_of_twins` — `line_of_weil_twins`, `rh_of_weil_twins` (WeilLandau.lean:138, 146)
* `not_twins_nonneg_dh` — refutes the hypothesis of `rh_of_weil_twins` (with `dh_offline_zero`)
* `dh_twins_rate` — `weil_twins_rate` (WeilLandau.lean:162), constant `3σ`, and for every `σ`
  (for `σ < 0` both sides are false)
* `not_twins_subexp_dh` — refutes the right-hand side of `rh_iff_twins_subexp` (WeilLandau.lean:173)
* `twinData_dhu` — the same poles with the u-space form `QDHu` (DHBridge.lean) on the twins
  `twin (box 1) (λ/3)`: the bridge from the twin form to the ground energy `lamDH` (DHForm.lean),
  which is defined from `QDHu`
* `zeros_of_lamDH_ge`, `lamDH_rate`, `lamDH_fails_exponentially`, `not_lamDH_subexp` —
  `zeros_of_lam_ge`, `lam_rate`, `lam_fails_exponentially`, the right-hand side of
  `rh_iff_lam_subexp` (WeilRate.lean:43, 81, 105, 66); in the u-space normalisation the constant
  is `σ`, as for `ζ`
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## The twin data for `dh` -/

theorem finite_tau3 (R : ℝ) : {i : ZeroIdx (sqF XiDH3) | ‖2 * I * tau3 i‖ ≤ R}.Finite := by
  have hs : Summable fun i : ZeroIdx (sqF XiDH3) => ‖i.1⁻¹‖ := hadamard_XiDH3.summ
  set K : ℝ := max (R ^ 2 / 4) 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {i : ZeroIdx (sqF XiDH3) | ‖i.1‖ ≤ K}.Finite := by
    have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [mem_ofPred_eq, not_lt]
    rw [norm_inv]
    have hi' : ‖i.1‖ ≤ K := hi
    have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx3_ne_zero i)
    exact inv_anti₀ hp hi'
  refine hfin.subset fun i hi => ?_
  have hi' : ‖2 * I * tau3 i‖ ≤ R := hi
  have e1 : ‖2 * I * tau3 i‖ = 2 * ‖tau3 i‖ := by simp
  have e2 : ‖i.1‖ = ‖tau3 i‖ ^ 2 := by rw [← tau3_sq, norm_pow]
  show ‖i.1‖ ≤ K
  rw [e2]
  have h0 := norm_nonneg (tau3 i)
  have : ‖tau3 i‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  exact this.trans (le_max_left _ _)

theorem re_pole3 (i : ZeroIdx (sqF XiDH3)) : (2 * I * tau3 i).re = -2 * (tau3 i).im := by simp

theorem abs_re_pole3_lt (i : ZeroIdx (sqF XiDH3)) : |(2 * I * tau3 i).re| < 1 := by
  have := tau3_im_lt i
  rw [re_pole3, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]; linarith

/-- No `τ_u` is purely imaginary: `Ξ_dh` has no zero on `iℝ`. -/
theorem tau3_re_ne (i : ZeroIdx (sqF XiDH3)) : (tau3 i).re ≠ 0 := by
  intro h
  have hz := XiDH3_tau i
  unfold XiDH3 at hz
  have e : (3 : ℂ) * tau3 i = I * ((3 * (tau3 i).im : ℝ) : ℂ) :=
    Complex.ext (by simp [h]) (by simp)
  rw [e] at hz
  exact XiDH_I_mul_ne_zero _ hz

theorem im_pole3_ne (i : ZeroIdx (sqF XiDH3)) : (2 * I * tau3 i).im ≠ 0 := by
  have e : (2 * I * tau3 i).im = 2 * (tau3 i).re := by simp
  rw [e]
  have := tau3_re_ne i
  intro h; exact this (by linarith)

/-- **The data of the twin-form Landau argument for `dh`.** -/
theorem twinData_dh :
    TwinLandau.TwinData (fun i : ZeroIdx (sqF XiDH3) => 2 * I * tau3 i)
      (fun i => 2 * ghatC (box 1) 1 (tau3 i) ^ 2) GboxC
      (fun l => QDH (l + 1) (twin (box 1) l)) where
  summ := by
    obtain ⟨K, hK⟩ := striptest_antitone one_pos (box_probe 1).even box_antitone box_nonneg
      (box_probe 1).intervalIntegrable
    have h := QDH_hasSum (box_probe 1) one_pos hK
    exact summable_norm_iff.2 (by simpa using h.summable)
  re_lt := abs_re_pole3_lt
  im_ne := im_pole3_ne
  finite := finite_tau3
  c_eq i := by unfold GboxC; congr 3; field_simp
  G_even p := by
    unfold GboxC; rw [show -p / (2 * I) = -(p / (2 * I)) by ring, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine mul_ne_zero two_ne_zero (pow_ne_zero 2 (ghat_box_ne ?_))
    have e : (p / (2 * I)).im = -p.re / 2 := by simp [Complex.div_im]; ring
    rw [e]; intro h; linarith
  hasSum l hl := by
    obtain ⟨K, hK⟩ := striptest_twin_box hl
    have h := QDH_hasSum (twin_probe (box_probe 1) hl) (by linarith) hK
    convert h using 1
    funext i
    rw [ghatC_twin one_pos (box_probe 1) hl, TwinLandau.twin_sq]
    ring_nf

/-! ## The pole's real part and the zero's distance from the line -/

/-- `3|Re P_u| = |2 Re s − 1|` for a zero `s = ½ ± 3iτ_u`. -/
theorem abs_two_re_sub_one_eq {s : ℂ} {i : ZeroIdx (sqF XiDH3)}
    (hi : tau3 i = (s - 1 / 2) / (3 * I) ∨ tau3 i = -((s - 1 / 2) / (3 * I))) :
    |2 * s.re - 1| = 3 * |(2 * I * tau3 i).re| := by
  have e : ((s - 1 / 2) / (3 * I)).im = -(s.re - 1 / 2) / 3 := by
    simp [Complex.div_im]; ring
  rw [re_pole3]
  rcases hi with hi | hi
  · rw [hi, e, show -2 * (-(s.re - 1 / 2) / 3) = (2 * s.re - 1) / 3 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]; ring
  · rw [hi, neg_im, e, show -2 * -(-(s.re - 1 / 2) / 3) = -((2 * s.re - 1) / 3) by ring, abs_neg,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; ring

/-- Each `τ_u` is a zero `s` of `dh` with `Re s > 0` and `|2 Re s − 1| = 3|Re P_u|`. -/
theorem exists_dh_zero_of_tau3 (i : ZeroIdx (sqF XiDH3)) :
    ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ |2 * s.re - 1| = 3 * |(2 * I * tau3 i).re| := by
  have hz := XiDH3_tau i
  rcases le_or_gt (tau3 i).im 0 with h | h
  · obtain ⟨hd, h0⟩ := dh_zero_of_XiDH3 hz h
    refine ⟨_, hd, h0, ?_⟩
    have hre : (1 / 2 + I * (3 * tau3 i)).re = 1 / 2 - 3 * (tau3 i).im := by simp; ring
    rw [hre, re_pole3, show 2 * (1 / 2 - 3 * (tau3 i).im) - 1 = 3 * (-2 * (tau3 i).im) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  · obtain ⟨hd, h0⟩ := dh_zero_of_XiDH3 (τ := -(tau3 i)) (by rw [XiDH3_even]; exact hz)
      (by simp; linarith)
    refine ⟨_, hd, h0, ?_⟩
    have hre : (1 / 2 + I * (3 * -tau3 i)).re = 1 / 2 + 3 * (tau3 i).im := by simp
    rw [hre, re_pole3, show 2 * (1 / 2 + 3 * (tau3 i).im) - 1 = -(3 * (-2 * (tau3 i).im)) by ring,
      abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]

/-! ## Weil positivity on the twins: the Landau implication and its refutation -/

/-- **The dh column of `line_of_weil_twins`/`rh_of_weil_twins`**: if the twin form is `≥ 0` for
every `λ ≥ 0`, every zero of `dh` with `Re s > 0` is on the line. -/
theorem dhRH_of_twins (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ QDH (l + 1) (twin (box 1) l)) : DHRH := by
  have := countable_ZeroIdx3
  intro s hs h0
  obtain ⟨i, hi⟩ := tau3_of_dh_zero hs h0
  have hb := TwinLandau.abs_re_le twinData_dh (C := 0) le_rfl (fun l hl => by simpa using hQ l hl) i
  have h1 := abs_two_re_sub_one_eq hi
  have h2 : |2 * s.re - 1| = 0 := le_antisymm (by rw [h1]; linarith) (abs_nonneg _)
  rw [abs_eq_zero] at h2; linarith

/-- **The twin form of `dh` is negative somewhere**: `dhRH_of_twins` and the certificate
`dh_offline_zero`. -/
theorem not_twins_nonneg_dh : ¬ ∀ l : ℝ, 0 ≤ l → 0 ≤ QDH (l + 1) (twin (box 1) l) := fun hQ => by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  exact hne (dhRH_of_twins hQ s hs h0)

/-! ## The graded criterion -/

/-- `dh_twins_rate` for `σ ≥ 0`: `TwinLandau.rate_iff`. -/
theorem dh_twins_rate_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l ≥ 0, -(C * Real.exp (σ * l)) ≤ QDH (l + 1) (twin (box 1) l)) ↔
      ∀ s, dh s = 0 → 0 < s.re → |2 * s.re - 1| ≤ 3 * σ := by
  have := countable_ZeroIdx3
  rw [TwinLandau.rate_iff twinData_dh hσ]
  constructor
  · intro h s hs h0
    obtain ⟨i, hi⟩ := tau3_of_dh_zero hs h0
    rw [abs_two_re_sub_one_eq hi]
    linarith [h i]
  · intro h i
    obtain ⟨s, hs, h0, he⟩ := exists_dh_zero_of_tau3 i
    have := h s hs h0
    linarith

/-- **The dh column of `weil_twins_rate`.** `Q_dh(twin (box 1) λ) ≥ −C·e^{σλ}` on `λ ≥ 0` for some
`C` iff every zero of `dh` with `Re s > 0` has `|2 Re s − 1| ≤ 3σ` (the factor `3` is the scaling
`s = ½ + 3iτ` of `Ξ₃`). For `σ < 0` both sides are false. -/
theorem dh_twins_rate {σ : ℝ} :
    (∃ C, ∀ l ≥ 0, -(C * Real.exp (σ * l)) ≤ QDH (l + 1) (twin (box 1) l)) ↔
      ∀ s, dh s = 0 → 0 < s.re → |2 * s.re - 1| ≤ 3 * σ := by
  rcases le_or_gt 0 σ with hσ | hσ
  · exact dh_twins_rate_of_nonneg hσ
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  have hpos : 0 < |2 * s.re - 1| := abs_pos.2 fun h => hne (by linarith)
  refine ⟨fun ⟨C, hC⟩ => ?_, fun h => absurd (h s hs h0) (by linarith)⟩
  refine absurd ((dh_twins_rate_of_nonneg le_rfl).1 ⟨max C 0, fun l hl => ?_⟩ s hs h0) (by linarith)
  have h1 := hC l hl
  have he : Real.exp (σ * l) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he0 := Real.exp_pos (σ * l)
  have h2 : C * Real.exp (σ * l) ≤ max C 0 := by
    calc C * Real.exp (σ * l) ≤ max C 0 * Real.exp (σ * l) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) he0.le
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left he (le_max_right _ _)
      _ = max C 0 := mul_one _
  rw [zero_mul, Real.exp_zero, mul_one]
  linarith

/-- **The twin form of `dh` has a negative part of exponential rate**: the dh column of the
right-hand side of `rh_iff_twins_subexp`. -/
theorem not_twins_subexp_dh :
    ¬ ∀ σ > 0, ∃ C, ∀ l ≥ 0, -(C * Real.exp (σ * l)) ≤ QDH (l + 1) (twin (box 1) l) := fun h => by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  have hpos : 0 < |2 * s.re - 1| := abs_pos.2 fun h => hne (by linarith)
  have := dh_twins_rate.1 (h (|2 * s.re - 1| / 6) (by positivity)) s hs h0
  linarith

/-! ## The u-space twins and the ground energy `λ_dh` -/

/-- The u-space weight `G(p) = 2ĝ₀(3p/2i)²`, `g₀ = box 1`. -/
def GboxDH (p : ℂ) : ℂ := 2 * ghatC (box 1) 1 (3 * (p / (2 * I))) ^ 2

/-- `ĝ_λ(3z)²` is a strip test function for the twin `g_λ = twin (box 1) (λ/3)`. -/
theorem striptest_twin_box3 {l : ℝ} (hl : 0 ≤ l) :
    ∃ K, StripTest (fun z => ghatC (twin (box 1) (l / 3)) (l / 3 + 1) (3 * z) ^ 2) K := by
  have hp := box_probe 1
  obtain ⟨K, hK⟩ := striptest_antitone3 one_pos hp.even (box_antitone' 1) (box_nonneg' 1)
    hp.intervalIntegrable
  have hK' : ∀ t ∈ PilotWeil.strip (-1) 1, ‖ghatC (box 1) 1 (3 * t)‖ ^ 2 * (1 + t.re ^ 2) ≤ K := by
    intro t ht
    have := hK.bound t ht
    rw [norm_pow, le_div_iff₀ (by positivity)] at this
    exact this
  have hT := striptest_mul_sq (G := fun z => ghatC (box 1) 1 (3 * z))
    (m := fun z => 2 * Complex.cos (l * z))
    ((ghatC_differentiable hp.intervalIntegrable).comp (differentiable_id.const_mul 3))
    (by fun_prop)
    hK' (fun t ht => norm_two_cos_strip hl ht)
  have e : (fun z => ghatC (twin (box 1) (l / 3)) (l / 3 + 1) (3 * z) ^ 2)
      = fun z => (2 * Complex.cos (l * z) * ghatC (box 1) 1 (3 * z)) ^ 2 := by
    funext z
    rw [ghatC_twin one_pos hp (by positivity : (0 : ℝ) ≤ l / 3)]
    congr 4; push_cast; ring
  exact ⟨_, e ▸ hT⟩

/-- **The u-space twin data for `dh`**: the same poles `2iτ_u`, the form `Q_dh` of the twins
`twin (box 1) (λ/3)` (support `λ/3 + 1`), weights `2ĝ₀(3τ_u)²`. -/
theorem twinData_dhu :
    TwinLandau.TwinData (fun i : ZeroIdx (sqF XiDH3) => 2 * I * tau3 i)
      (fun i => 2 * ghatC (box 1) 1 (3 * tau3 i) ^ 2) GboxDH
      (fun l => QDHu (twin (box 1) (l / 3))) where
  summ := by
    obtain ⟨K, hK⟩ := striptest_antitone3 one_pos (box_probe 1).even (box_antitone' 1)
      (box_nonneg' 1) (box_probe 1).intervalIntegrable
    have h := QDHu_hasSum (box_probe 1) one_pos hK
    exact summable_norm_iff.2 (by simpa using h.summable)
  re_lt := abs_re_pole3_lt
  im_ne := im_pole3_ne
  finite := finite_tau3
  c_eq i := by unfold GboxDH; congr 4; field_simp
  G_even p := by
    unfold GboxDH
    rw [show 3 * (-p / (2 * I)) = -(3 * (p / (2 * I))) by ring, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine mul_ne_zero two_ne_zero (pow_ne_zero 2 (ghat_box_ne ?_))
    have e : (3 * (p / (2 * I))).im = -(3 * p.re) / 2 := by simp [Complex.div_im]; ring
    rw [e]; intro h; linarith
  hasSum l hl := by
    have hl3 : (0 : ℝ) ≤ l / 3 := by positivity
    obtain ⟨K, hK⟩ := striptest_twin_box3 hl
    have h := QDHu_hasSum (twin_probe (box_probe 1) hl3) (by positivity) hK
    convert h using 1
    funext i
    rw [ghatC_twin one_pos (box_probe 1) hl3,
      show (((l / 3 : ℝ)) : ℂ) * (3 * tau3 i) = (l : ℂ) * tau3 i by push_cast; ring,
      TwinLandau.twin_sq]
    ring_nf

/-- **A lower bound on `λ_dh` of exponential rate `σ` is a zero-free region**: the dh column of
`zeros_of_lam_ge`. If `λ_dh(a) ≥ −C·e^{σa}` for every `a ≥ 1`, every zero of `dh` with `Re s > 0`
has `|2 Re s − 1| ≤ σ`. -/
theorem zeros_of_lamDH_ge {C σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ a, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lamDH a) {s : ℂ} (hs : dh s = 0) (h0 : 0 < s.re) :
    |2 * s.re - 1| ≤ σ := by
  have := countable_ZeroIdx3
  have hQ : ∀ l : ℝ, 0 ≤ l →
      -((4 * (|C| * Real.exp σ)) * Real.exp (σ / 3 * l)) ≤ QDHu (twin (box 1) (l / 3)) := by
    intro l hl
    have hl3 : (0 : ℝ) ≤ l / 3 := by positivity
    set K := |C| * Real.exp σ * Real.exp (σ / 3 * l)
    have hK : 0 ≤ K := by positivity
    have hN := normSq_twin_le (l / 3)
    have hN0 := normSq_nonneg (twin (box 1) (l / 3))
    have hlam := lamDH_mul_le (twin_probe (box_probe 1) hl3)
    have h1 : -K ≤ lamDH (l / 3 + 1) := by
      have := h (l / 3 + 1) (by linarith)
      have e : Real.exp (σ * (l / 3 + 1)) = Real.exp σ * Real.exp (σ / 3 * l) := by
        rw [← Real.exp_add]; ring_nf
      rw [e] at this
      have : C * (Real.exp σ * Real.exp (σ / 3 * l)) ≤ |C| * (Real.exp σ * Real.exp (σ / 3 * l)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      simp only [K]; nlinarith
    have h2 : -K * normSq (twin (box 1) (l / 3))
        ≤ lamDH (l / 3 + 1) * normSq (twin (box 1) (l / 3)) :=
      mul_le_mul_of_nonneg_right h1 hN0
    have h3 : -K * 4 ≤ -K * normSq (twin (box 1) (l / 3)) := by nlinarith
    calc -((4 * (|C| * Real.exp σ)) * Real.exp (σ / 3 * l)) = -K * 4 := by simp only [K]; ring
      _ ≤ _ := h3.trans (h2.trans hlam)
  obtain ⟨i, hi⟩ := tau3_of_dh_zero hs h0
  have hb := TwinLandau.abs_re_le twinData_dhu (by positivity : 0 ≤ σ / 3) hQ i
  rw [abs_two_re_sub_one_eq hi]
  linarith

/-- **A zero with `|2 Re s − 1| > σ` makes `λ_dh(a) < −C·e^{σa}` at arbitrarily large `a`**: the dh
column of `lam_rate`. -/
theorem lamDH_rate {s : ℂ} (hs : dh s = 0) (h0 : 0 < s.re) {σ : ℝ} (hσ : 0 ≤ σ)
    (hlt : σ < |2 * s.re - 1|) (C X : ℝ) : ∃ a, X < a ∧ lamDH a < -(C * Real.exp (σ * a)) := by
  by_contra hno
  push Not at hno
  set b := max X 1 + 1
  have hb1 : 1 ≤ b := by linarith [le_max_right X 1]
  have hbX : X < b := by linarith [le_max_left X 1]
  set K := |C| * Real.exp (σ * b)
  have hK1 : |C| ≤ K := le_mul_of_one_le_right (abs_nonneg C) (Real.one_le_exp (by positivity))
  refine absurd (zeros_of_lamDH_ge (C := K) hσ (fun a ha => ?_) hs h0) (not_le.2 hlt)
  have hea : 1 ≤ Real.exp (σ * a) := Real.one_le_exp (by nlinarith)
  rcases lt_or_ge X a with hXa | haX
  · have := hno a hXa
    have : C * Real.exp (σ * a) ≤ K * Real.exp (σ * a) :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans hK1) (by positivity)
    linarith
  · have hab : lamDH b ≤ lamDH a := lamDH_antitone (by linarith) (by linarith)
    have h1 := hno b hbX
    have : C * Real.exp (σ * b) ≤ K := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hK0 : 0 ≤ K := by positivity
    nlinarith

/-- **`λ_dh` fails exponentially, unconditionally**: the dh column of `lam_fails_exponentially`, its
hypothesis `¬RiemannHypothesis` discharged by the certificate `dh_offline_zero`. -/
theorem lamDH_fails_exponentially :
    ∃ δ > 0, ∀ σ, 0 ≤ σ → σ < δ → ∀ C X : ℝ, ∃ a, X < a ∧ lamDH a < -(C * Real.exp (σ * a)) := by
  obtain ⟨s, hs, h0, hre⟩ := dh_offline_zero
  exact ⟨|2 * s.re - 1|, abs_pos.2 fun h => hre (by linarith),
    fun σ hσ hlt C X => lamDH_rate hs h0 hσ hlt C X⟩

/-- **`λ_dh` has a negative part of exponential rate**: the dh column of the right-hand side of
`rh_iff_lam_subexp`. -/
theorem not_lamDH_subexp :
    ¬ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lamDH a := fun h => by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  have hpos : 0 < |2 * s.re - 1| := abs_pos.2 fun h => hne (by linarith)
  obtain ⟨C, hC⟩ := h (|2 * s.re - 1| / 2) (by positivity)
  have := zeros_of_lamDH_ge (by positivity) hC hs h0
  linarith

end PsiOmega

#print axioms PsiOmega.twinData_dh
#print axioms PsiOmega.dhRH_of_twins
#print axioms PsiOmega.not_twins_nonneg_dh
#print axioms PsiOmega.dh_twins_rate
#print axioms PsiOmega.not_twins_subexp_dh
#print axioms PsiOmega.twinData_dhu
#print axioms PsiOmega.zeros_of_lamDH_ge
#print axioms PsiOmega.lamDH_rate
#print axioms PsiOmega.lamDH_fails_exponentially
#print axioms PsiOmega.not_lamDH_subexp
