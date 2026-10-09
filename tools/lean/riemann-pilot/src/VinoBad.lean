/-
# Sharpening, step S2a: bad tuples by Hölder over classes (round 214)

Plain statement (`TBB_le2`). For a prime `p ≥ k ≥ 2` and `n = k + s`, the pairs of bad tuples
(coordinates in fewer than `k` residue classes mod `p`) with equal power sums number at most
  `T_BB ≤ 2·C(p,k−1)²·(k−1)^{2n}·J_{n,k}(⌊P/p⌋+1)`.

This replaces round 201's `T_BB ≤ #bad²`, which ignored the agreement condition and forced
`s ~ k³`. Here a bad tuple lies in a piece `S^n` with `|S| = k−1` classes; pairs across pieces
are split by Cauchy–Schwarz (`pairCount(A,B) ≤ pairCount(A,A) + pairCount(B,B)`), and within a
piece Hölder over its `k−1` classes reduces to the mean value of one class, an interval of
length `⌊P/p⌋+1` (`Jc_cls_le`).
-/
import VinoRec

open Finset MeasureTheory

namespace VinoBad

open Vinogradov VinoIter VinoHolder VinoSplit VinoRec

section counting
variable {β : Type*} {k : ℕ} (φ : β → Fin k → ℤ)

lemma pairCount_le_add [DecidableEq β] (A B : Finset β) :
    pairCount A B φ ≤ pairCount A A φ + pairCount B B φ := by
  have h := pairCount_sq_le φ A B
  by_contra hlt
  push Not at hlt
  have : (pairCount A A φ + pairCount B B φ) ^ 2 < pairCount A B φ ^ 2 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  nlinarith

lemma pairCount_biUnion2 [DecidableEq β] {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (A : ι → Finset β) :
    pairCount (I.biUnion A) (I.biUnion A) φ ≤ ∑ i ∈ I, ∑ j ∈ I, pairCount (A i) (A j) φ := by
  refine (pairCount_biUnion_le φ I A _).trans (sum_le_sum fun i _ => ?_)
  calc pairCount (A i) (I.biUnion A) φ ≤ pairCount (I.biUnion A) (A i) φ := pairCount_swap_le φ _ _
    _ ≤ ∑ j ∈ I, pairCount (A j) (A i) φ := pairCount_biUnion_le φ I A _
    _ ≤ ∑ j ∈ I, pairCount (A i) (A j) φ := sum_le_sum fun j _ => pairCount_swap_le φ _ _

end counting

/-- `g` over a piece is the sum of `g` over its classes. -/
lemma g_pieceS {P p : ℕ} (hp : p.Prime) (S : Finset (ZMod p)) {k : ℕ} (α : Fin k → ℝ) :
    g (pieceS P p S) α = ∑ r ∈ S, g (cls P p r.val) α := by
  have : Fact p.Prime := ⟨hp⟩
  unfold g
  rw [← Finset.sum_fiberwise_of_maps_to (s := pieceS P p S) (t := S)
    (g := fun m : ℕ => ((m : ℕ) : ZMod p)) (fun m hm => (mem_filter.mp hm).2)]
  apply sum_congr rfl
  intro r _
  apply sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [pieceS, cls, mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    refine ⟨h1, ?_⟩
    rw [← h3, ZMod.val_natCast]
  · rintro ⟨h1, h2⟩
    have hr : ((m : ℕ) : ZMod p) = r := by
      rw [← ZMod.natCast_zmod_val r, ZMod.natCast_eq_natCast_iff', h2,
        Nat.mod_eq_of_lt (ZMod.val_lt r)]
    exact ⟨⟨h1, hr ▸ ‹r ∈ S›⟩, hr⟩

/-- **One piece.** `pairCount(S^n, S^n) ≤ (k−1)^{2n}·J_n(⌊P/p⌋+1)` for `|S| = k − 1`. -/
theorem piece_self_le {n k P p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (S : Finset (ZMod p))
    (hS : S.card = k - 1) (kk : ℕ) :
    pairCount (piece n P p S) (piece n P p S) (pv kk) ≤
      (k - 1) ^ (2 * n) * J n kk (P / p + 1) := by
  have hcnt := count_eq_integral (piece n P p S) (pv kk)
  have hcls : ∀ r : ZMod p, ((Jc (cls P p r.val) n kk : ℕ) : ℝ) =
      ∫ α, ‖E (Wa n P p r.val) (pv kk) α‖ ^ 2 ∂torus kk := by
    intro r
    rw [← count_eq_integral]
    unfold Jc shiftCount Wa
    simp only [add_zero]
  have hpt : ∀ α, ‖E (piece n P p S) (pv kk) α‖ ^ 2 ≤
      ((k - 1 : ℕ) : ℝ) ^ (2 * n - 1) * ∑ r ∈ S, ‖E (Wa n P p r.val) (pv kk) α‖ ^ 2 := by
    intro α
    rw [piece, E_pi]
    simp_rw [Wa, E_pi]
    rw [g_pieceS hp S α, norm_pow, ← pow_mul]
    simp_rw [norm_pow, ← pow_mul]
    rw [show n * 2 = 2 * n from mul_comm n 2]
    have h1 : ‖∑ r ∈ S, g (cls P p r.val) α‖ ^ (2 * n) ≤
        (∑ r ∈ S, ‖g (cls P p r.val) α‖) ^ (2 * n) :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    have h2 := power_mean_fs S (fun r => ‖g (cls P p r.val) α‖) (fun r => norm_nonneg _)
      (ℓ := 2 * n) (by omega)
    rw [hS] at h2
    exact h1.trans h2
  have hmono := integral_mono (integrable_normsq _ _)
    ((integrable_finsetSum _ fun r _ => integrable_normsq _ _).const_mul
      (((k - 1 : ℕ) : ℝ) ^ (2 * n - 1))) hpt
  rw [integral_const_mul, integral_finsetSum _ fun r _ => integrable_normsq _ _] at hmono
  rw [← hcnt] at hmono
  simp_rw [← hcls] at hmono
  have hJ : ∀ r ∈ S, ((Jc (cls P p r.val) n kk : ℕ) : ℝ) ≤ (J n kk (P / p + 1) : ℝ) := by
    intro r _; exact_mod_cast Jc_cls_le hp.pos n kk
  have hsum : ∑ r ∈ S, ((Jc (cls P p r.val) n kk : ℕ) : ℝ) ≤
      ((k - 1 : ℕ) : ℝ) * (J n kk (P / p + 1) : ℝ) := by
    calc _ ≤ ∑ _r ∈ S, (J n kk (P / p + 1) : ℝ) := sum_le_sum hJ
      _ = _ := by rw [sum_const, hS, nsmul_eq_mul]
  have hfin : ((pairCount (piece n P p S) (piece n P p S) (pv kk) : ℕ) : ℝ) ≤
      ((k - 1 : ℕ) : ℝ) ^ (2 * n) * (J n kk (P / p + 1) : ℝ) := by
    unfold pairCount
    refine hmono.trans ?_
    calc ((k - 1 : ℕ) : ℝ) ^ (2 * n - 1) * ∑ r ∈ S, ((Jc (cls P p r.val) n kk : ℕ) : ℝ)
        ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * n - 1) * (((k - 1 : ℕ) : ℝ) * (J n kk (P / p + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
  exact_mod_cast hfin

/-- **Step D′.** `T_BB ≤ 2·C(p,k−1)²·(k−1)^{2n}·J_n(⌊P/p⌋+1)`, `n = k + s`. -/
theorem TBB_le2 {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    TBB k s P p ≤ 2 * (p.choose (k - 1)) ^ 2 * ((k - 1) ^ (2 * (k + s)) *
      J (k + s) k (P / p + 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set F := powersetCard (k - 1) (univ : Finset (ZMod p)) with hF
  set Bd := (k - 1) ^ (2 * (k + s)) * J (k + s) k (P / p + 1) with hBd
  have hself : ∀ S ∈ F, pairCount (piece (k + s) P p S) (piece (k + s) P p S) (pv k) ≤ Bd := by
    intro S hS
    exact piece_self_le hp (by omega) S (mem_powersetCard.mp hS).2 k
  have hFc : F.card = p.choose (k - 1) := by
    rw [hF, card_powersetCard, card_univ, ZMod.card]
  unfold TBB
  calc pairCount ((box (k + s) P).filter (isBad k p)) ((box (k + s) P).filter (isBad k p)) (pv k)
      ≤ pairCount (F.biUnion (piece (k + s) P p)) (F.biUnion (piece (k + s) P p)) (pv k) :=
        pairCount_mono _ (bad_sub hp hk hkp) (bad_sub hp hk hkp)
    _ ≤ ∑ S ∈ F, ∑ S' ∈ F, pairCount (piece (k + s) P p S) (piece (k + s) P p S') (pv k) :=
        pairCount_biUnion2 _ F _
    _ ≤ ∑ S ∈ F, ∑ S' ∈ F, (Bd + Bd) := by
        apply sum_le_sum; intro S hS; apply sum_le_sum; intro S' hS'
        exact (pairCount_le_add _ _ _).trans (Nat.add_le_add (hself S hS) (hself S' hS'))
    _ = 2 * (p.choose (k - 1)) ^ 2 * Bd := by
        rw [sum_const, sum_const, hFc, smul_eq_mul, smul_eq_mul]; ring

/-- **One Karatsuba step with the sharp bad bound.** -/
theorem one_step2 {k s P p : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpk : k < p) (hP : P ≤ p ^ k)
    (hs : 1 ≤ s) :
    J (k + s) k P ≤ 4 * (p.choose (k - 1)) ^ 2 * ((k - 1) ^ (2 * (k + s)) *
        J (k + s) k (P / p + 1)) +
      16 * (k + s) ^ (2 * k) * (p ^ (2 * s - 1) *
        (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1)))) := by
  have hA := stepA k s P p
  have hD := TBB_le2 (s := s) (P := P) hp hk hpk.le
  calc J (k + s) k P ≤ 2 * TBB k s P p + 16 * (k + s) ^ (2 * k) * Gfull k s P p := hA
    _ ≤ 2 * (2 * (p.choose (k - 1)) ^ 2 * ((k - 1) ^ (2 * (k + s)) * J (k + s) k (P / p + 1))) +
        16 * (k + s) ^ (2 * k) * (p ^ (2 * s - 1) *
          (p * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J s k (P / p + 1)))) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hD) (Nat.mul_le_mul_left _ (Gfull_le_J hp hpk hP hs))
    _ = _ := by ring

end VinoBad
