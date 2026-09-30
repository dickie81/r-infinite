import WeilLandau
import WeilChiCriterion
import AngularFamily

/-!
# The twin form of `ζ_{ℚ(i)} = ζ · L(s, χ₋₄)` (round 236)

Joining `twinData_zeta` (WeilLandau) and `twinData_chi good_chi4` (WeilChiCriterion) on the
sum of the two zero index types gives one `TwinLandau.TwinData` for the Dedekind zeta function of
`ℚ(i)`, whose Weil form on twin boxes is `2·Q_ζ + Q_{χ₋₄}`. The twin-form Landau argument then
gives: `RH ∧ GRH(χ₋₄)` ⟺ `2·Q_ζ(twin λ) + Q_{χ₋₄}(twin λ) ≥ 0` for every `λ ≥ 0`.
-/

open Complex Set
open Pilot1ca Pilot1bt PilotWeil PsiOmega TwinLandau

namespace Dedekind4

/-- `L(σ, χ₋₄) ≠ 0` on `(0, 1)` (from the nonnegative partial sums). -/
theorem hS4 : ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction chi4 σ ≠ 0 := fun _ hσ _ =>
  LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ

/-- The zeros of `ζ_{ℚ(i)}`: the zeros of `ζ` (with multiplicity) and the `τ`-family of `L(s, χ₋₄)`. -/
abbrev IdxK : Type := ZIdx ⊕ ZeroIdx (sqF (XiC chi4))

/-- The poles. -/
noncomputable def PK : IdxK → ℂ := Sum.elim poleP (fun i => 2 * I * tauC i)

/-- The weights (both normalised to `G = GboxC = 2ĝ₀(p/2i)²`). -/
noncomputable def cK : IdxK → ℂ := Sum.elim (fun q => 2 * cw q) (fun i => 2 * ghatC (box 1) 1 (tauC i) ^ 2)

/-- The Weil form of `ζ_{ℚ(i)}` on twin boxes, in the normalisation of `cK`. -/
noncomputable def QK (a : ℝ) (g : ℝ → ℝ) : ℝ := 2 * weilQ a g + QC chi4 a g

/-- The `χ₋₄` data. -/
theorem twinData_chi4 : TwinData (fun i : ZeroIdx (sqF (XiC chi4)) => 2 * I * tauC i)
    (fun i => 2 * ghatC (box 1) 1 (tauC i) ^ 2) GboxC (fun l => QC chi4 (l + 1) (twin (box 1) l)) :=
  twinData_chi good_chi4 hS4

theorem twinData_K : TwinData PK cK GboxC (fun l => QK (l + 1) (twin (box 1) l)) where
  summ := by
    refine Summable.sum _ ?_ ?_
    · refine (twinData_zeta.summ.mul_left 2).congr fun q => ?_
      simp [cK]
    · exact twinData_chi4.summ
  re_lt := by
    rintro (q | i)
    · exact twinData_zeta.re_lt q
    · exact twinData_chi4.re_lt i
  im_ne := by
    rintro (q | i)
    · exact twinData_zeta.im_ne q
    · exact twinData_chi4.im_ne i
  finite R := by
    refine (((twinData_zeta.finite R).image Sum.inl).union
      ((twinData_chi4.finite R).image Sum.inr)).subset ?_
    rintro (q | i) hq
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨i, hq, rfl⟩
  c_eq := by
    rintro (q | i)
    · show 2 * cw q = GboxC (poleP q)
      rw [twinData_zeta.c_eq q]; simp only [GboxC, Gbox]
    · exact twinData_chi4.c_eq i
  G_even := twinData_chi4.G_even
  G_ne := twinData_chi4.G_ne
  hasSum l hl := by
    have h1 := (twinData_zeta.hasSum l hl).mul_left 2
    have h2 := twinData_chi4.hasSum l hl
    have h := HasSum.sum (f := fun q => cK q * (2 + cexp (l * PK q) + cexp (-(l * PK q))))
      (a := 2 * (weilQ (l + 1) (twin (box 1) l) : ℂ)) (b := (QC chi4 (l + 1) (twin (box 1) l) : ℂ))
      (by refine h1.congr_fun fun q => ?_; simp only [Function.comp, cK, PK, Sum.elim_inl]; ring) h2
    convert h using 1
    simp only [QK]; push_cast; ring

/-- The pole condition, translated to the zeros of `ζ` and of `L(s, χ₋₄)`. -/
theorem abs_re_PK_iff (σ : ℝ) :
    (∀ q : IdxK, |(PK q).re| ≤ σ) ↔
      (∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧
        (∀ s : ℂ, DirichletCharacter.LFunction chi4 s = 0 → 0 < s.re → s.re < 1 →
          |2 * s.re - 1| ≤ σ) := by
  have e : ∀ i : ZeroIdx (sqF (XiC chi4)),
      |(2 * I * tauC i).re| = |2 * (1 / 2 + I * tauC i).re - 1| := by
    intro i; congr 1; simp; ring
  constructor
  · intro h
    refine ⟨fun s hs => ?_, fun s hs h0 _ => ?_⟩
    · have hb := h (Sum.inl ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      change |(poleP _).re| ≤ σ at hb
      rwa [re_poleP] at hb
    · obtain ⟨i, hi⟩ := tau_of_zero good_chi4 hs h0
      have hb := h (Sum.inr i)
      change |(2 * I * tauC i).re| ≤ σ at hb
      rw [e] at hb
      have hst : (1 / 2 + I * ((s - 1 / 2) / I)) = s := by field_simp; ring
      rcases hi with hi | hi
      · rwa [hi, hst] at hb
      · rw [hi] at hb
        have : (1 / 2 + I * -((s - 1 / 2) / I)).re = 1 - s.re := by
          rw [show 1 / 2 + I * -((s - 1 / 2) / I) = 1 - (1 / 2 + I * ((s - 1 / 2) / I)) by ring, hst]
          simp
        rw [this, show 2 * (1 - s.re) - 1 = -(2 * s.re - 1) by ring, abs_neg] at hb
        exact hb
  · rintro ⟨hz, hL⟩ (q | i)
    · change |(poleP q).re| ≤ σ
      rw [re_poleP]; exact hz _ (nontrivial_zZF q)
    · change |(2 * I * tauC i).re| ≤ σ
      obtain ⟨h0, h1, h2⟩ := zero_of_tau good_chi4 i
      rw [e]; exact hL _ h0 h1 h2

instance : Countable IdxK := by
  have := countable_ZeroIdxC good_chi4
  infer_instance

/-- **The graded criterion for `ζ_{ℚ(i)}`.** -/
theorem QK_twins_rate {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QK (l + 1) (twin (box 1) l)) ↔
      (∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧
        (∀ s : ℂ, DirichletCharacter.LFunction chi4 s = 0 → 0 < s.re → s.re < 1 →
          |2 * s.re - 1| ≤ σ) := by
  rw [TwinLandau.rate_iff twinData_K hσ, abs_re_PK_iff]

/-- **`RH ∧ GRH(χ₋₄)` from positivity of the Dedekind twin form.** -/
theorem rh_grh_of_QK (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ QK (l + 1) (twin (box 1) l)) :
    RiemannHypothesis ∧ GRH chi4 := by
  have h := (QK_twins_rate le_rfl).1 ⟨0, fun l hl => by simpa using hQ l hl⟩
  constructor
  · intro s hs htriv _
    have := h.1 s ⟨hs, htriv⟩
    have := abs_nonpos_iff.1 this
    linarith
  · intro s hs h0 h1
    have := abs_nonpos_iff.1 (h.2 s hs h0 h1)
    linarith

/-- **Positivity of the Dedekind twin form from `RH ∧ GRH(χ₋₄)`.** -/
theorem QK_nonneg_of_rh_grh (hRH : RiemannHypothesis) (hG : GRH chi4) {l : ℝ} (hl : 0 ≤ l) :
    0 ≤ QK (l + 1) (twin (box 1) l) := by
  obtain ⟨K, hK⟩ := striptest_twin_box hl
  have h1 := weilQ_nonneg_of_RH hRH (by linarith : (0 : ℝ) < l + 1) (twin_probe (box_probe 1) hl)
  have h2 := QC_nonneg_of_GRH good_chi4 hG (twin_probe (box_probe 1) hl) (by linarith) hK
  unfold QK; linarith

/-- **Weil's criterion for `ζ_{ℚ(i)}`, twin boxes.** -/
theorem rh_grh_iff_QK_twins :
    (RiemannHypothesis ∧ GRH chi4) ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QK (l + 1) (twin (box 1) l) :=
  ⟨fun ⟨h1, h2⟩ _ hl => QK_nonneg_of_rh_grh h1 h2 hl, rh_grh_of_QK⟩

/-- **`RH ∧ GRH(χ₋₄)` ⟺ the Dedekind twin form's defect is subexponential.** -/
theorem rh_grh_iff_QK_subexp :
    (RiemannHypothesis ∧ GRH chi4) ↔
      ∀ σ > 0, ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QK (l + 1) (twin (box 1) l) := by
  constructor
  · rintro ⟨h1, h2⟩ σ hσ
    exact ⟨0, fun l hl => by simpa using QK_nonneg_of_rh_grh h1 h2 hl⟩
  · intro h
    have key : ∀ σ > 0, (∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧
        (∀ s : ℂ, DirichletCharacter.LFunction chi4 s = 0 → 0 < s.re → s.re < 1 →
          |2 * s.re - 1| ≤ σ) := fun σ hσ => (QK_twins_rate hσ.le).1 (h σ hσ)
    have z : ∀ x : ℝ, (∀ σ > 0, |x| ≤ σ) → x = 0 := fun x hx =>
      abs_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using hx ε hε)
        (abs_nonneg _))
    constructor
    · intro s hs htriv _
      have := z _ fun σ hσ => (key σ hσ).1 s ⟨hs, htriv⟩
      linarith
    · intro s hs h0 h1
      have := z _ fun σ hσ => (key σ hσ).2 s hs h0 h1
      linarith

/-! ## The link to `AngularFamily` -/

/-- `AngularFamily`'s character is `chi4`. -/
theorem χ4C_eq : AngularFamily.χ4C = chi4 := rfl

/-- **`GRHMemberZero` gives both RH and GRH(χ₋₄)** (the RH half is `rh_of_member_zero`). -/
theorem rh_grh_of_member_zero (h : AngularFamily.GRHMemberZero) : RiemannHypothesis ∧ GRH chi4 := by
  refine ⟨AngularFamily.rh_of_member_zero h, fun s hs h0 h1 => ?_⟩
  refine h s ?_ ?_ ?_ ?_
  · unfold AngularFamily.angularL0; rw [χ4C_eq, hs, mul_zero]
  · rintro ⟨n, rfl⟩; simp at h0; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rintro ⟨n, rfl⟩; simp at h0; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rintro rfl; simp at h1

/-- **`GRHMemberZero` forces the Dedekind twin form to be nonnegative.** -/
theorem QK_nonneg_of_member_zero (h : AngularFamily.GRHMemberZero) {l : ℝ} (hl : 0 ≤ l) :
    0 ≤ QK (l + 1) (twin (box 1) l) :=
  QK_nonneg_of_rh_grh (rh_grh_of_member_zero h).1 (rh_grh_of_member_zero h).2 hl

end Dedekind4

#print axioms Dedekind4.twinData_K
#print axioms Dedekind4.rh_grh_iff_QK_twins
#print axioms Dedekind4.QK_twins_rate
#print axioms Dedekind4.rh_grh_iff_QK_subexp
#print axioms Dedekind4.rh_grh_of_member_zero
#print axioms Dedekind4.QK_nonneg_of_member_zero
