import DensityAsym
import ZeroLocal
import WeilZeta
import SlogZeta
import Zeta23.MV.Final

/-! # The two local zero counts compared (round 248)

zeta23's `Ncount t (t+1)` is bounded by the pilot's `Kloc (t + ½)`; the two `IsNontrivialZero` predicates agree.
-/

open Complex Real

namespace CountCompare

open Pilot1ca Pilot1bt ShortWeil

theorem nontriv_iff' (ρ : ℂ) : Pilot1bt.IsNontrivialZero ρ ↔ Zeta23.IsNontrivialZero ρ :=
  ⟨fun h => ⟨h.1, h.re_pos, h.re_lt_one⟩, fun h => ⟨h.1, h.not_trivial.1⟩⟩

theorem im_rhoXi (p : Bool × ZeroIdx (sqF Xi)) :
    (rhoXi p).im = if p.1 then (tau p.2).re else -(tau p.2).re := by
  unfold rhoXi; split_ifs <;> simp

/-- **zeta23's local count from the pilot's zero weight, with the pilot's explicit constant.** -/
theorem local_count_le {t : ℝ} (ht : 0 ≤ t) :
    (Zeta23.Ncount t (t + 1) : ℝ) ≤ Kloc (t + 1 / 2) := by
  classical
  set s := Zeta23.zerosIn t (t + 1) with hs
  have hfin : s.Finite := (SlogZeta.Zs_finite (t + 2)).subset fun ρ ⟨h, h0, h1⟩ =>
    ⟨h, by linarith, by linarith⟩
  let W := {p : ZIdx // t < (zetaZeroFamily p).im ∧ (zetaZeroFamily p).im ≤ t + 1}
  have hcard : Zeta23.Ncount t (t + 1) = Nat.card W := by
    rw [Zeta23.Ncount, SlogZeta.finsum_eq_card hfin]
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨⟨⟨x.1.1, (nontriv_iff' _).2 x.1.2.1⟩, x.2⟩, x.1.2.2.1, x.1.2.2.2⟩
        invFun := fun p => ⟨⟨p.1.1.1, (nontriv_iff' _).1 p.1.1.2, p.2.1, p.2.2⟩, p.1.2⟩
        left_inv := fun x => rfl
        right_inv := fun p => rfl }
  set S := {i : ZeroIdx (sqF Xi) | |(|(tau i).re| - (t + 1 / 2))| ≤ 1} with hSdef
  have hSfin : S.Finite := (finite_re_le (t + 3 / 2)).subset fun i hi => by
    have h := (abs_le.1 (show |(|(tau i).re| - (t + 1 / 2))| ≤ 1 from hi)).2
    show |(tau i).re| ≤ t + 3 / 2
    linarith
  have hre : ∀ p : W, |(tau (zetaEquiv p.1).2).re| = (zetaZeroFamily p.1).im := by
    intro p
    have e := congrArg Complex.im (rhoXi_zetaEquiv p.1)
    rw [im_rhoXi] at e
    have hpos : 0 < (zetaZeroFamily p.1).im := by linarith [p.2.1]
    split_ifs at e with hb
    · rw [← e] at hpos ⊢; exact abs_of_pos hpos
    · rw [← e] at hpos ⊢; rw [abs_of_neg (by linarith)]
  let φ : W → S := fun p => ⟨(zetaEquiv p.1).2, by
    show |(|(tau (zetaEquiv p.1).2).re| - (t + 1 / 2))| ≤ 1
    rw [hre p]
    rw [abs_le]; constructor <;> linarith [p.2.1, p.2.2]⟩
  have hinj : Function.Injective φ := by
    intro p q hpq
    have h2 : (zetaEquiv p.1).2 = (zetaEquiv q.1).2 := congrArg Subtype.val hpq
    have hsign : ∀ r : W, (zetaEquiv r.1).1 = true ↔ 0 < (tau (zetaEquiv r.1).2).re := by
      intro r
      have e := congrArg Complex.im (rhoXi_zetaEquiv r.1)
      rw [im_rhoXi] at e
      have hpos : 0 < (zetaZeroFamily r.1).im := by linarith [r.2.1]
      constructor
      · intro hb; rw [if_pos hb] at e; rw [e]; exact hpos
      · intro h; by_contra hb
        rw [if_neg hb] at e; rw [← e] at hpos; linarith
    have h1 : (zetaEquiv p.1).1 = (zetaEquiv q.1).1 := by
      have hp := hsign p
      have hq := hsign q
      rw [h2] at hp
      exact Bool.eq_iff_iff.2 (hp.trans hq.symm)
    have : zetaEquiv p.1 = zetaEquiv q.1 := Prod.ext h1 h2
    exact Subtype.ext (zetaEquiv.injective this)
  have : Finite S := hSfin.to_subtype
  have hle : Nat.card W ≤ Nat.card S := Nat.card_le_card_of_injective φ hinj
  have hS : (Nat.card S : ℝ) ≤ Kloc (t + 1 / 2) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hSfin]
    exact card_local_le (by linarith) _ fun i hi => by simpa [hSdef] using hi
  rw [hcard]
  calc (Nat.card W : ℝ) ≤ Nat.card S := by exact_mod_cast hle
    _ ≤ Kloc (t + 1 / 2) := hS

/-- The two mean-value inputs side by side (import check only). -/
example : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C := Zeta23.MV.mv_hilbert
#check @DirMean.mean_value

end CountCompare

#print axioms CountCompare.nontriv_iff'
#print axioms CountCompare.local_count_le
