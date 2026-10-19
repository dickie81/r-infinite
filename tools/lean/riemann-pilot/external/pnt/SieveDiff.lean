/-
# Round 604: the tree's weights, and a leaf's difference (milestone M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `SieveFamily.dw q a n = 1[n ≡ a] − 1[(n, q) = 1]/φ(q)`.

* `tree_weighted`: for any weights `f`, `SieveTree.tree_pt` summed over a finite set.
* `sum_dw_eq`: a sum of `dw` over a set is the count of its `n ≡ a` minus the count of its `n` prime to `q`, divided
  by `φ(q)`.
* `leaf_diff`: for `a` a unit, `d > 0` with every prime factor at least `w ≥ 1`, and the ranges of `SieveLeaf.T`
  with `w^{2^{−J}} ≤ 2`: the `n ∈ (N₁, N₂]` with `d ∣ n` and no prime factor below `w` have `|A − B/φ(q)|` at most
  twice the fundamental lemma's error, `X·Σ_j e_{k_j}(T_j) ∏_{i≠j} trunc_{k_i}(T_i) + (J + 1)∏_j Σ_{i ≤ k_j}
  C(|T_j|, i)`, `X = (N₂ − N₁)/(dq)`, for even `k_j ≥ 1`.

`leaf_diff` is `SieveLeaf.leaf_A` minus `SieveLeaf.leaf_B`: the main terms `X ∏_j ∏_{T_j} (1 − g)` cancel. When `d`
shares a prime with `q`, both counts vanish.

The file imports `SieveTree.lean`, `SieveLeaf.lean` and `SieveFamily.lean`.
-/
import SieveTree
import SieveLeaf
import SieveFamily

open Real Finset SieveFamily SieveTree

namespace SieveDiff

/-- **The Buchstab tree, weighted.** For any weights `f`, the tree identity `tree_pt` summed over a finite set. -/
theorem tree_weighted (C : Finset ℕ) (f : ℕ → ℂ) {r X w z₀ : ℕ} (hwz : w ≤ z₀)
    (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) (hrX : r ≤ X) :
    ∑ n ∈ C, f n * (if r ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then ∑ n ∈ C, f n * (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0)
            else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            ∑ n ∈ C, f n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  have hptC : ∀ n, (if r ∣ n ∧ rough z₀ n then (1 : ℂ) else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
    intro n
    have h := congrArg (Int.cast : ℤ → ℂ) (tree_pt n hwz hr hrX)
    push_cast at h
    convert h using 1
  simp_rw [hptC, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp

/-- A weighted sum of `dw` as two counts: the `n ≡ a` and, divided by `φ(q)`, the `n` prime to `q`. -/
theorem sum_dw_eq {q : ℕ} [NeZero q] (a : ZMod q) (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ n ∈ s, dw q a n * (if c n then 1 else 0) =
      ((s.filter (fun n => n ≡ a.val [MOD q] ∧ c n)).card : ℂ) -
        ((s.filter (fun n => Nat.Coprime n q ∧ c n)).card : ℂ) / q.totient := by
  have h1 : ∀ n : ℕ, ((n : ZMod q) = a) ↔ n ≡ a.val [MOD q] := fun n => by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  have h2 : ∀ n : ℕ, IsUnit (n : ZMod q) ↔ Nat.Coprime n q := fun n => ZMod.isUnit_iff_coprime n q
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold dw
  simp only [h1, h2]
  by_cases hc : c n <;> by_cases ha : n ≡ a.val [MOD q] <;> by_cases hu : n.Coprime q <;> simp [hc, ha, hu]

open SieveBrun SieveLeaf in
/-- The fundamental lemma's relative error is nonnegative. -/
theorem gapsum_nonneg (w : ℝ) (J q : ℕ) (k : Fin J → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) :
    0 ≤ ∑ j, esym (T w J j) (g q) (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) := by
  have hg0 : ∀ i, ∀ p ∈ T w J i, 0 ≤ g q p := fun i p _ => g_nonneg q p
  have hg1 : ∀ i, ∀ p ∈ T w J i, g q p ≤ 1 := fun i p hp => g_le_one (prime_of_mem_T hp).one_lt.le
  refine Finset.sum_nonneg fun j _ => mul_nonneg (esym_nonneg (hg0 j) _) (Finset.prod_nonneg fun i _ => ?_)
  exact le_trans (Finset.prod_nonneg fun p hp => sub_nonneg.2 (hg1 i p hp))
    (trunc_bounds (hg0 i) (hg1 i) (hk i) (hk1 i)).2

open SieveBrun SieveLeaf in
/-- **A leaf's difference.** For `a` a unit, `d > 0` with every prime factor at least `w ≥ 1`, and the ranges of
`SieveLeaf.T` with `w^{2^{−J}} ≤ 2`: the `n ∈ (N₁, N₂]` with `d ∣ n` and no prime factor below `w` have
`|A − B/φ(q)|` at most twice the fundamental lemma's error, `X·Σ_j e_{k_j}(T_j) ∏_{i≠j} trunc_{k_i}(T_i) +
(J + 1)∏_j Σ_{i ≤ k_j} C(|T_j|, i)`, `X = (N₂ − N₁)/(dq)`, for even `k_j ≥ 1`. -/
theorem leaf_diff {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {d N₁ N₂ w : ℕ} (hd : 0 < d) (hw : 1 ≤ w)
    (hdw : ∀ p : ℕ, p.Prime → p ∣ d → w ≤ p) {J : ℕ} (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hN : N₁ ≤ N₂)
    (k : Fin J → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) :
    ‖∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0)‖ ≤
      2 * (((N₂ : ℝ) - N₁) / (d * q) * ∑ j, esym (T w J j) (g q) (k j) *
          ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) +
        (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have hX0 : (0 : ℝ) ≤ ((N₂ : ℝ) - N₁) / (d * q) := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    positivity
  have hR0 : (0 : ℝ) ≤ (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ) := by
    positivity
  have hE0 := gapsum_nonneg (w : ℝ) J q k hk hk1
  by_cases hcop : Nat.Coprime d q
  · rw [sum_dw_eq]
    have ha' : Nat.Coprime a.val q := (ZMod.isUnit_iff_coprime a.val q).1 (by rw [ZMod.natCast_zmod_val]; exact ha)
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hdw' : ∀ p : ℕ, p.Prime → p ∣ d → (w : ℝ) ≤ p := fun p hp hpd => by exact_mod_cast hdw p hp hpd
    have hA := leaf_A hq ha' hd hcop hw' hdw' hJ hN k hk hk1
    have hB := leaf_B hq hd hcop hw' hdw' hJ hN k hk hk1
    rw [Nat.ceil_natCast] at hA hB
    set A := (#{n ∈ Ioc N₁ N₂ | n ≡ a.val [MOD q] ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hAdef
    set B := (#{n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hBdef
    have hAeq : ((Ioc N₁ N₂).filter (fun n => n ≡ a.val [MOD q] ∧ (d ∣ n ∧ rough w n))).card = A := rfl
    have hBeq : ((Ioc N₁ N₂).filter (fun n => Nat.Coprime n q ∧ (d ∣ n ∧ rough w n))).card = B := rfl
    rw [hAeq, hBeq]
    have hreal : ((A : ℂ) - (B : ℂ) / q.totient) = (((A : ℝ) - (B : ℝ) / q.totient : ℝ) : ℂ) := by push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    set M := ∏ j, ∏ p ∈ T w J j, (1 - g q p)
    have htri : |(A : ℝ) - (B : ℝ) / q.totient| ≤
        |(A : ℝ) - ((N₂ : ℝ) - N₁) / (d * q) * M| + |(B : ℝ) / q.totient - ((N₂ : ℝ) - N₁) / (d * q) * M| := by
      have := abs_sub ((A : ℝ) - ((N₂ : ℝ) - N₁) / (d * q) * M) ((B : ℝ) / q.totient - ((N₂ : ℝ) - N₁) / (d * q) * M)
      have e : (A : ℝ) - (B : ℝ) / q.totient = ((A : ℝ) - ((N₂ : ℝ) - N₁) / (d * q) * M) -
          ((B : ℝ) / q.totient - ((N₂ : ℝ) - N₁) / (d * q) * M) := by ring
      rw [e]; exact this
    have hA' : |(A : ℝ) - ((N₂ : ℝ) - N₁) / (d * q) * M| ≤ ((N₂ : ℝ) - N₁) / (d * q) *
        ∑ j, esym (T w J j) (g q) (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) +
        (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ) := by
      exact hA
    have hB' : |(B : ℝ) / q.totient - ((N₂ : ℝ) - N₁) / (d * q) * M| ≤ ((N₂ : ℝ) - N₁) / (d * q) *
        ∑ j, esym (T w J j) (g q) (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) +
        (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ) := by
      exact hB
    linarith
  · have hzero : ∀ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0) = 0 := by
      intro n _
      by_cases hn : d ∣ n ∧ rough w n
      · have hnc : ¬ Nat.Coprime n q := fun h => hcop (Nat.Coprime.coprime_dvd_left hn.1 h)
        have hnu : ¬ IsUnit (n : ZMod q) := fun h => hnc ((ZMod.isUnit_iff_coprime n q).1 h)
        have hna : (n : ZMod q) ≠ a := fun h => hnu (h ▸ ha)
        simp [dw, hn, hnu, hna]
      · simp [hn]
    rw [Finset.sum_eq_zero hzero, norm_zero]
    have := mul_nonneg hX0 hE0
    linarith

end SieveDiff
