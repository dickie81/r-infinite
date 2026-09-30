import Mathlib
import ZeroCount
import WeilIndexZeta

/-! # The ground-state ↔ Weil-index join (round 251)

Rounds 57–58 (ZeroCount.lean) count the off-line zeros of `ζ` from the ground-state side: under (a)
(`HypConv`) for ground states whose ground spaces eventually have dimension `≤ M`, `ζ` has at most
`2⌊(M − 1)/2⌋` zeros with `Re s > ½` (`zeta_offline_card_le`). Round 229 (WeilIndexZeta.lean) counts
them from the Weil side: `Q` negative definite on a `k`-dimensional space of strip-test probes exhibits
`k` distinct off-line quadruples (`finrank_le_quadruples_zeta`). Here the two counts are composed:

* `zeta_upper_offline_card_le`: at most `⌊(M − 1)/2⌋` zeros with `Re s > ½` and `Im s > 0`, that is,
  at most `⌊(M − 1)/2⌋` off-line quadruples;
* `offRight_finite`: the zeros to the right of the line form a finite set;
* `finrank_le_ground_index`, `finrank_le_ground_index_C2`: **every negative-definite space of
  strip-test (or `C²`) probes has `dim V ≤ ⌊(M − 1)/2⌋`**;
* `gdim_lower_of_neg_block`, the contrapositive: a certified negative block of dimension `k ≥ 1`
  forces `dim (ground space) ≥ 2k + 1` infinitely often along every (a)-family.

The representative set `R` of `finrank_le_quadruples_zeta` is one index per zero in the upper right
quarter: a zero with `Re ρ > ½` is that member or its conjugate, and a zero with `Re ρ < ½` is
`1 − ρ'` for such a `ρ'`, with `t_{1−ρ'} = −t_{ρ'}`. The quarter is finite by `zeta_offline_card_le`
and has no real member (`ζ ≠ 0` on `(0, 1)`). At `M ≤ 2` the bound reads `dim V = 0`, which
`rh_of_dim_le_two` and Weil's criterion also give.

No bearing on RH by itself: every scan so far finds `Q ≥ 0`, and no dimension bound is known.
Round 252 (GroundBlock.lean) composes the join with the ground space itself as a negative block: along
`a n → ∞`, any eventual dimension bound gives RH.
-/

open Real Complex MeasureTheory Filter

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-- The nontrivial zeros of `ζ` to the right of the critical line. -/
def OffRight : Set ℂ := {s | IsNontrivialZero s ∧ 1 / 2 < s.re}

/-- A nontrivial zero off the line is not real (`ζ ≠ 0` on `(0, 1)`). -/
theorem im_ne_zero_of_offRight {s : ℂ} (hs : s ∈ OffRight) : s.im ≠ 0 := by
  intro h0
  have hnt := hs.1
  apply zetaNoZeroInUnitInterval s.re hnt.re_pos hnt.re_lt_one
  have : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
  rw [← this]; exact hnt.1

/-- Conjugation preserves the nontrivial zeros (`riemannZeta_conj`). -/
theorem isNontrivialZero_conj {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero ((starRingEnd ℂ) s) := by
  refine ⟨by rw [riemannZeta_conj, hs.1, map_zero], ?_⟩
  rintro ⟨n, hn⟩
  apply hs.2
  refine ⟨n, ?_⟩
  have h := congrArg (starRingEnd ℂ) hn
  rw [Complex.conj_conj] at h
  rw [h]
  simp only [map_mul, map_neg, map_add, map_one, map_natCast, map_ofNat]

theorem offRight_conj {s : ℂ} (hs : s ∈ OffRight) : (starRingEnd ℂ) s ∈ OffRight :=
  ⟨isNontrivialZero_conj hs.1, by rw [Complex.conj_re]; exact hs.2⟩

/-- `ρ ↦ 1 − ρ` preserves the nontrivial zeros (`PsiOmega.IsNontrivialZero.one_sub`, restated to keep the
import closure small). -/
theorem isNontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZero s) : IsNontrivialZero (1 - s) := by
  rw [nontrivial_iff_Xi]
  have e : (1 - s - 1 / 2) / I = -((s - 1 / 2) / I) := by ring
  rw [e, Xi_even, ← nontrivial_iff_Xi]; exact hs

/-- **At most `⌊(M − 1)/2⌋` zeros of `ζ` with `Re s > ½` and `Im s > 0`**, under (a) for ground states
whose ground spaces eventually have dimension `≤ M`: the conjugate pairs of `zeta_offline_card_le`. -/
theorem zeta_upper_offline_card_le {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (T : Finset ℂ)
    (hT : ∀ s ∈ T, IsNontrivialZero s ∧ 1 / 2 < s.re ∧ 0 < s.im) : T.card ≤ (M - 1) / 2 := by
  classical
  have hdisj : Disjoint T (T.image (starRingEnd ℂ)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hs'
    have h1 := (hT _ hs).2.2
    have h2 := (hT _ hσ).2.2
    rw [Complex.conj_im] at h1; linarith
  have hinj : Set.InjOn (starRingEnd ℂ) T := fun x _ y _ h => (starRingEnd ℂ).injective h
  have hcard := zeta_offline_card_le ha hgs hdim hconv (T ∪ T.image (starRingEnd ℂ)) (by
    intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · obtain ⟨hnt, hre, _⟩ := hT s h; exact ⟨hnt.1, hnt.2, hre⟩
    · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hnt, hre, _⟩ := hT σ hσ
      have := isNontrivialZero_conj hnt
      exact ⟨this.1, this.2, by rw [Complex.conj_re]; exact hre⟩)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at hcard
  omega

/-- Under the same hypotheses the off-line zeros to the right form a finite set. -/
theorem offRight_finite {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) : OffRight.Finite := by
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * ((M - 1) / 2) + 1)
  have := zeta_offline_card_le ha hgs hdim hconv T (fun s hs => by
    have h := hT (Finset.mem_coe.2 hs)
    exact ⟨h.1.1, h.1.2, h.2⟩)
  omega

/-- **The join: negative directions of Weil's form are at most `⌊(M − 1)/2⌋`.** Under (a) for ground
states whose ground spaces eventually have dimension `≤ M`, every finite-dimensional space `V` of
strip-test probes on which `Q` is negative definite has `dim V ≤ ⌊(M − 1)/2⌋`. -/
theorem finrank_le_ground_index {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) {b : ℝ} (hb : 0 < b) (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ v ∈ V, Probe b v) (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v b z ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ b v < 0) :
    Module.finrank ℝ V ≤ (M - 1) / 2 := by
  classical
  have hfin := offRight_finite ha hgs hdim hconv
  set Sp := hfin.toFinset.filter (fun σ => 0 < σ.im) with hSp_def
  have hmemSp : ∀ s, s ∈ Sp ↔ s ∈ OffRight ∧ 0 < s.im := by
    intro s; rw [hSp_def, Finset.mem_filter, hfin.mem_toFinset]
  have hSp_card : Sp.card ≤ (M - 1) / 2 :=
    zeta_upper_offline_card_le ha hgs hdim hconv Sp (fun s hs => by
      obtain ⟨h1, h2⟩ := (hmemSp s).1 hs; exact ⟨h1.1, h1.2, h2⟩)
  have hnt : ∀ s ∈ Sp, IsNontrivialZero s := fun s hs => ((hmemSp s).1 hs).1.1
  let f : {s // s ∈ Sp} → (Σ w : NontrivialZero, Fin (zeroMult w)) :=
    fun p => ⟨⟨p.1, hnt p.1 p.2⟩, ⟨0, zeroMult_pos _⟩⟩
  set R := Sp.attach.image f with hR_def
  have hRcard : R.card ≤ Sp.card :=
    calc R.card ≤ Sp.attach.card := Finset.card_image_le
      _ = Sp.card := Finset.card_attach
  refine (finrank_le_quadruples_zeta V hb hV hS hneg R ?_).trans (hRcard.trans hSp_card)
  intro i
  have hρnt : IsNontrivialZero (zetaZeroFamily i) := i.1.2
  by_cases hline : (zetaZeroFamily i).re = 1 / 2
  · exact Or.inl hline
  right
  have hmemR : ∀ s (hs : s ∈ Sp), f ⟨s, hs⟩ ∈ R := fun s hs =>
    Finset.mem_image.2 ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
  have hfam : ∀ s (hs : s ∈ Sp), zetaZeroFamily (f ⟨s, hs⟩) = s := fun s hs => rfl
  have hmemSp' : ∀ s, s ∈ OffRight → 0 < s.im → s ∈ Sp := fun s hs him => (hmemSp s).2 ⟨hs, him⟩
  set ρ := zetaZeroFamily i with hρ
  rcases lt_or_gt_of_ne hline with hlt | hgt
  · -- `Re ρ < ½`: use `1 − ρ`
    have hρ' : (1 - ρ) ∈ OffRight :=
      ⟨isNontrivialZero_one_sub hρnt, by simp only [Complex.sub_re, Complex.one_re]; linarith⟩
    have him' := im_ne_zero_of_offRight hρ'
    rcases lt_or_gt_of_ne him' with hneg' | hpos'
    · have hc : (starRingEnd ℂ) (1 - ρ) ∈ Sp :=
        hmemSp' _ (offRight_conj hρ') (by rw [Complex.conj_im]; linarith)
      refine ⟨f ⟨_, hc⟩, hmemR _ hc, ?_⟩
      rw [hfam]
      right; right; left
      simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_conj, Complex.conj_I]
      ring
    · have hc : (1 - ρ) ∈ Sp := hmemSp' _ hρ' hpos'
      refine ⟨f ⟨_, hc⟩, hmemR _ hc, ?_⟩
      rw [hfam]
      right; left
      ring
  · -- `Re ρ > ½`
    have hρ' : ρ ∈ OffRight := ⟨hρnt, hgt⟩
    have him' := im_ne_zero_of_offRight hρ'
    rcases lt_or_gt_of_ne him' with hneg' | hpos'
    · have hc : (starRingEnd ℂ) ρ ∈ Sp :=
        hmemSp' _ (offRight_conj hρ') (by rw [Complex.conj_im]; linarith)
      refine ⟨f ⟨_, hc⟩, hmemR _ hc, ?_⟩
      rw [hfam]
      right; right; right
      simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_conj, Complex.conj_I]
      ring
    · have hc : ρ ∈ Sp := hmemSp' _ hρ' hpos'
      refine ⟨f ⟨_, hc⟩, hmemR _ hc, ?_⟩
      rw [hfam]
      left; rfl

/-- **The same for `C²` probes vanishing near `±b`.** -/
theorem finrank_le_ground_index_C2 {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) {b : ℝ} (hb : 0 < b) (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ v ∈ V, Probe b v) (hc : ∀ v ∈ V, ∃ r v₁ v₂, C2Supp r v v₁ v₂ ∧ 0 ≤ r ∧ r ≤ b)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ b v < 0) :
    Module.finrank ℝ V ≤ (M - 1) / 2 :=
  finrank_le_ground_index ha hgs hdim hconv hb V hV (fun v hv => strip_of_C2 hb (hV v hv) (hc v hv))
    hneg

/-- **Contrapositive: a certified negative block forces a ground-space dimension.** If `Q` is negative
definite on a `k`-dimensional space of strip-test probes, then along any (a)-family of ground states the
ground-space dimension is `≥ 2k + 1` infinitely often. -/
theorem gdim_lower_of_neg_block {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hconv : HypConv a g) {b : ℝ} (hb : 0 < b)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (hk : 0 < Module.finrank ℝ V)
    (hV : ∀ v ∈ V, Probe b v) (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v b z ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ b v < 0) :
    ∃ᶠ n in atTop, 2 * Module.finrank ℝ V + 1 ≤ gdim (a n) := by
  by_contra h
  rw [Filter.not_frequently] at h
  have hdim : ∀ᶠ n in atTop, gdim (a n) ≤ 2 * Module.finrank ℝ V :=
    h.mono fun n hn => by omega
  have := finrank_le_ground_index ha hgs hdim hconv hb V hV hS hneg
  omega

end Pilot1ca

#print axioms Pilot1ca.isNontrivialZero_conj
#print axioms Pilot1ca.zeta_upper_offline_card_le
#print axioms Pilot1ca.offRight_finite
#print axioms Pilot1ca.finrank_le_ground_index
#print axioms Pilot1ca.finrank_le_ground_index_C2
#print axioms Pilot1ca.gdim_lower_of_neg_block
