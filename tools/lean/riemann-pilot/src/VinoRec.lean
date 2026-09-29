/-
# Vinogradov's mean value theorem, step I.3b: bad count and the one-step inequality (round 201)

Plain statements.
* `bad_card` (Step D): the tuples in `[1,P]^n` whose coordinates meet fewer than `k` residue
  classes mod `p` number at most `p^{k−1}·((k−1)(⌊P/p⌋+1))^n`. Such a tuple lives inside some
  set `S` of `k−1` classes; there are `C(p,k−1) ≤ p^{k−1}` choices of `S`, and each class holds
  at most `⌊P/p⌋+1` numbers.
* `one_step` (Steps A–D chained). For a prime `p > k` with `P ≤ p^k` and `s ≥ 1`:
  `J_{k+s,k}(P) ≤ 2·(p^{k−1}((k−1)(⌊P/p⌋+1))^{k+s})²
     + 16(k+s)^{2k}·p^{2s−1}·p·P^k·k!·p^{k(k−1)/2}·J_{s,k}(⌊P/p⌋+1)`.
-/
import VinoSplit

open Finset

namespace VinoRec

open Vinogradov VinoIter VinoHolder VinoSplit

lemma card_cls_le {P p a : ℕ} : (cls P p a).card ≤ P / p + 1 := by
  calc (cls P p a).card ≤ (range (P / p + 1)).card := by
        refine card_le_card_of_injOn (fun n => n / p) ?_ ?_
        · intro n hn
          have hn' := mem_coe.mp hn
          rw [cls, mem_filter, mem_Icc] at hn'
          rw [mem_coe, mem_range]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hn'.1.2)
        · intro n hn m hm h
          have hn' := mem_coe.mp hn
          have hm' := mem_coe.mp hm
          rw [cls, mem_filter] at hn' hm'
          simp only at h
          rw [← Nat.div_add_mod n p, ← Nat.div_add_mod m p, h, hn'.2, hm'.2]
    _ = P / p + 1 := card_range _

/-- **Step D (bad count).** -/
theorem bad_card {n k P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    ((box n P).filter (isBad k p)).card ≤ p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  set F := powersetCard (k - 1) (univ : Finset (ZMod p)) with hF
  set piece : Finset (ZMod p) → Finset (Fin n → ℕ) := fun S =>
    Fintype.piFinset fun _ : Fin n => (Icc 1 P).filter fun m => ((m : ℕ) : ZMod p) ∈ S with hpiece
  have hsub : (box n P).filter (isBad k p) ⊆ F.biUnion piece := by
    intro x hx
    rw [mem_filter] at hx
    set R := univ.image fun i => (x i : ZMod p)
    have hR0 : R.card < k := hx.2
    have hR : R.card ≤ k - 1 := by omega
    have hRp : k - 1 ≤ (univ : Finset (ZMod p)).card := by
      rw [card_univ, ZMod.card]; omega
    obtain ⟨S, hRS, _, hS⟩ := exists_subsuperset_card_eq (subset_univ R) hR hRp
    refine mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨subset_univ _, hS⟩, ?_⟩
    rw [hpiece, Fintype.mem_piFinset]
    intro i
    rw [mem_filter]
    have hb := hx.1
    rw [Vinogradov.box, Fintype.mem_piFinset] at hb
    exact ⟨hb i, hRS (mem_image_of_mem _ (mem_univ i))⟩
  have hpc : ∀ S ∈ F, (piece S).card ≤ ((k - 1) * (P / p + 1)) ^ n := by
    intro S hS
    rw [mem_powersetCard] at hS
    rw [hpiece, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    apply Nat.pow_le_pow_left
    calc ((Icc 1 P).filter fun m => ((m : ℕ) : ZMod p) ∈ S).card
        ≤ (S.biUnion fun r => cls P p r.val).card := by
          apply card_le_card
          intro m hm
          rw [mem_filter] at hm
          refine mem_biUnion.mpr ⟨((m : ℕ) : ZMod p), hm.2, ?_⟩
          rw [cls, mem_filter, ZMod.val_natCast]
          exact ⟨hm.1, rfl⟩
      _ ≤ ∑ r ∈ S, (cls P p r.val).card := card_biUnion_le
      _ ≤ ∑ _r ∈ S, (P / p + 1) := sum_le_sum fun r _ => card_cls_le
      _ = (k - 1) * (P / p + 1) := by rw [sum_const, hS.2, smul_eq_mul]
  have hFc : F.card ≤ p ^ (k - 1) := by
    rw [hF, card_powersetCard, card_univ, ZMod.card]
    exact Nat.choose_le_pow p (k - 1)
  calc ((box n P).filter (isBad k p)).card ≤ (F.biUnion piece).card := card_le_card hsub
    _ ≤ ∑ S ∈ F, (piece S).card := card_biUnion_le
    _ ≤ ∑ _S ∈ F, ((k - 1) * (P / p + 1)) ^ n := sum_le_sum hpc
    _ = F.card * ((k - 1) * (P / p + 1)) ^ n := by rw [sum_const, smul_eq_mul]
    _ ≤ p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ n := Nat.mul_le_mul_right _ hFc

lemma TBB_le {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    TBB k s P p ≤ (p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ (k + s)) ^ 2 := by
  unfold TBB pairCount
  refine (card_filter_le _ _).trans ?_
  rw [card_product, sq]
  exact Nat.mul_le_mul (bad_card hp hk hkp) (bad_card hp hk hkp)

/-- **One Karatsuba step** (A–D chained). -/
theorem one_step {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpk : k < p) (hP : P ≤ p ^ k)
    (hs : 1 ≤ s) :
    J (k + s) k P ≤ 2 * (p ^ (k - 1) * ((k - 1) * (P / p + 1)) ^ (k + s)) ^ 2 +
      16 * (k + s) ^ (2 * k) * (p ^ (2 * s - 1) *
        (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1)))) := by
  have hA := stepA k s P p
  have hD := TBB_le (s := s) (P := P) hp hk hpk.le
  have hB := Gfull_le (k := k) (s := s) (P := P) hp.pos hs
  have hC : ∑ a ∈ range p, Gcls k s P p a ≤
      p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1)) := by
    calc ∑ a ∈ range p, Gcls k s P p a
        ≤ ∑ _a ∈ range p, P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1) := by
          apply sum_le_sum
          intro a _
          exact (Gcls_le hp hpk hP).trans (Nat.mul_le_mul_left _ (Jc_cls_le hp.pos s k))
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  have hG : Gfull k s P p ≤ p ^ (2 * s - 1) *
      (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1))) :=
    hB.trans (Nat.mul_le_mul_left _ hC)
  calc J (k + s) k P ≤ 2 * TBB k s P p + 16 * (k + s) ^ (2 * k) * Gfull k s P p := hA
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hD) (Nat.mul_le_mul_left _ hG)

end VinoRec
