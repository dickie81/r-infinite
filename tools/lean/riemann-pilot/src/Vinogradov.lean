/-
# Vinogradov's mean value theorem: foundations (round 194)

Plain statement.
* `J s k N` counts the pairs `(x, y)` of `s`-tuples from `{1, …, N}` whose power sums agree in
  every degree `1, …, k`: `x₁ʲ + … + x_sʲ = y₁ʲ + … + y_sʲ` for `j = 1..k`. This is Vinogradov's
  mean value `∫|Σ_{n≤N} e(α₁n + … + α_k nᵏ)|^{2s} dα` (by orthogonality; not formalised here).
* Always `N^s ≤ J ≤ N^{2s}` (`J_ge`, `J_le`), and more equations mean fewer solutions (`J_anti`).
* **The rigid range `s ≤ k`** (`agree_iff`): the power sums in degrees `1..k` pin down the tuple
  up to rearrangement (Newton's identities, then Vieta). Hence `J s k N ≤ s!·N^s`
  (`J_le_diag`): only the rearrangements count.

The theorem itself (Bourgain–Demeter–Guth 2016; Wooley 2016 for `k = 3`, 2019 in general):
`J s k N ≤ C·N^{s+ε} + C·N^{2s − k(k+1)/2 + ε}`. That is NOT proved here. The classical
weaker form (Vinogradov; Karatsuba's p-adic iteration) already suffices for the
Korobov–Vinogradov growth bound. It is the target of the next rounds.
-/
import Mathlib

open Finset MvPolynomial

namespace Vinogradov

open scoped Classical

/-- Power sums of `x` and `y` agree in degrees `1..k`. -/
def Agree (k : ℕ) {s : ℕ} (x y : Fin s → ℕ) : Prop :=
  ∀ j ∈ Icc 1 k, ∑ i, x i ^ j = ∑ i, y i ^ j

/-- The box `{1, …, N}^s`. -/
def box (s N : ℕ) : Finset (Fin s → ℕ) := Fintype.piFinset fun _ => Icc 1 N

/-- Vinogradov's mean value, as a count of solutions. -/
noncomputable def J (s k N : ℕ) : ℕ :=
  ((box s N ×ˢ box s N).filter fun p => Agree k p.1 p.2).card

lemma card_box (s N : ℕ) : (box s N).card = N ^ s := by
  simp [box, Fintype.card_piFinset]

theorem J_le (s k N : ℕ) : J s k N ≤ N ^ (2 * s) := by
  unfold J
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_box, ← pow_add, two_mul]

/-- The diagonal `x = y` always solves the system. -/
theorem J_ge (s k N : ℕ) : N ^ s ≤ J s k N := by
  rw [← card_box s N]
  unfold J
  refine card_le_card_of_injOn (fun x => (x, x)) ?_ ?_
  · intro x hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hx⟩, fun j _ => rfl⟩
  · intro a _ b _ h
    exact (Prod.ext_iff.mp h).1

theorem J_anti (s N : ℕ) {k k' : ℕ} (h : k ≤ k') : J s k' N ≤ J s k N := by
  unfold J
  apply card_le_card
  intro p hp
  rw [mem_filter] at hp ⊢
  refine ⟨hp.1, fun j hj => hp.2 j ?_⟩
  rw [mem_Icc] at hj ⊢; omega

/-! ## Newton's identities: power sums determine the elementary symmetric functions -/

theorem esymm_eq_of_psum {s : ℕ} (x y : Fin s → ℚ)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ n, n ≤ s → (univ.val.map x).esymm n = (univ.val.map y).esymm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Multiset.esymm]
  have key : ∀ z : Fin s → ℚ, (n : ℚ) * (univ.val.map z).esymm n = (-1) ^ (n + 1) *
      ∑ a ∈ antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (univ.val.map z).esymm a.1 * ∑ i, z i ^ a.2 := by
    intro z
    have := congrArg (aeval z) (MvPolynomial.mul_esymm_eq_sum (Fin s) ℚ n)
    simpa [aeval_esymm_eq_multiset_esymm, psum, map_sum, map_mul, map_pow] using this
  have hsum : (∑ a ∈ antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (univ.val.map x).esymm a.1 * ∑ i, x i ^ a.2) =
      ∑ a ∈ antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (univ.val.map y).esymm a.1 * ∑ i, y i ^ a.2 := by
    apply sum_congr rfl
    intro a ha
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    rw [ih a.1 ha.2 (by omega), h a.2 (by omega) (by omega)]
  have hx := key x
  have hy := key y
  rw [hsum] at hx
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact mul_left_cancel₀ hn0 (hx.trans hy.symm)

/-- **Vieta:** equal power sums in degrees `1..s` force equal multisets of values. -/
theorem map_eq_of_psum {s : ℕ} (x y : Fin s → ℚ)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    univ.val.map x = univ.val.map y := by
  have hc : Multiset.card (univ.val.map x) = s := by simp
  have hc' : Multiset.card (univ.val.map y) = s := by simp
  have hp : ((univ.val.map x).map fun t => Polynomial.X - Polynomial.C t).prod =
      ((univ.val.map y).map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hc, hc']
    apply sum_congr rfl
    intro j hj
    rw [esymm_eq_of_psum x y h j (by rw [mem_range] at hj; omega)]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

/-- **The rigid range.** For `s ≤ k`, the power sums in degrees `1..k` agree exactly when `y`
is a rearrangement of `x`. -/
theorem agree_iff {s k : ℕ} (hs : s ≤ k) (x y : Fin s → ℕ) :
    Agree k x y ↔ univ.val.map x = univ.val.map y := by
  constructor
  · intro h
    have hq := map_eq_of_psum (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) (fun j h1 h2 => by
      have := h j (mem_Icc.mpr ⟨h1, h2.trans hs⟩)
      exact_mod_cast this)
    have ex : univ.val.map (fun i => (x i : ℚ)) = (univ.val.map x).map Nat.cast :=
      (Multiset.map_map _ _ _).symm
    have ey : univ.val.map (fun i => (y i : ℚ)) = (univ.val.map y).map Nat.cast :=
      (Multiset.map_map _ _ _).symm
    rw [ex, ey] at hq
    exact Multiset.map_injective Nat.cast_injective hq
  · intro h j _
    rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
    have ex : univ.val.map (fun i => x i ^ j) = (univ.val.map x).map (· ^ j) := by
      rw [Multiset.map_map]; rfl
    have ey : univ.val.map (fun i => y i ^ j) = (univ.val.map y).map (· ^ j) := by
      rw [Multiset.map_map]; rfl
    rw [ex, ey, h]

lemma map_eq_iff_perm {s : ℕ} (x y : Fin s → ℕ) :
    univ.val.map x = univ.val.map y ↔ List.ofFn y ∈ (List.ofFn x).permutations := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe, List.mem_permutations,
    List.perm_comm]

/-- **Rigid range count:** for `s ≤ k`, `J s k N ≤ s!·N^s`. -/
theorem J_le_diag {s k : ℕ} (hs : s ≤ k) (N : ℕ) : J s k N ≤ s.factorial * N ^ s := by
  unfold J
  set S := (box s N ×ˢ box s N).filter fun p => Agree k p.1 p.2 with hS
  have hfib : ∀ x ∈ S.image Prod.fst, (S.filter fun p => p.1 = x).card ≤ s.factorial := by
    intro x _
    calc (S.filter fun p => p.1 = x).card
        ≤ ((List.ofFn x).permutations.toFinset).card := by
          refine card_le_card_of_injOn (fun p => List.ofFn p.2) ?_ ?_
          · intro p hp
            rw [coe_filter, Set.mem_ofPred_eq, hS, mem_filter] at hp
            have h1 := (agree_iff hs p.1 p.2).mp hp.1.2
            rw [hp.2] at h1
            rw [Finset.mem_coe, List.mem_toFinset]
            exact (map_eq_iff_perm x p.2).mp h1
          · intro p hp q hq hpq
            rw [coe_filter] at hp hq
            have e := List.ofFn_injective hpq
            exact Prod.ext (hp.2.trans hq.2.symm) e
      _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
      _ = s.factorial := by rw [List.length_permutations, List.length_ofFn]
  have himg : (S.image Prod.fst).card ≤ N ^ s := by
    rw [← card_box s N]
    apply card_le_card
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    rw [hS, mem_filter, mem_product] at hp
    exact hp.1.1
  calc S.card ≤ s.factorial * (S.image Prod.fst).card := card_le_mul_card_image S _ hfib
    _ ≤ s.factorial * N ^ s := Nat.mul_le_mul_left _ himg

/-! ## Translation invariance -/

/-- **Shifting every coordinate by `h` preserves the system** (binomial theorem): the degree-`j`
power sum of `x + h` is a fixed combination of those of `x` in degrees `0..j`. This affine
invariance drives every proof of the mean value theorem. -/
theorem agree_shift {s k : ℕ} (x y : Fin s → ℤ) (h : ℤ)
    (hA : ∀ j ∈ Icc 1 k, ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ j ∈ Icc 1 k, ∑ i, (x i + h) ^ j = ∑ i, (y i + h) ^ j := by
  intro j hj
  rw [mem_Icc] at hj
  have expand : ∀ z : Fin s → ℤ, ∑ i, (z i + h) ^ j =
      ∑ m ∈ range (j + 1), (∑ i, z i ^ m) * h ^ (j - m) * (j.choose m : ℤ) := by
    intro z
    simp_rw [add_pow, Finset.sum_mul]
    exact Finset.sum_comm
  rw [expand x, expand y]
  apply sum_congr rfl
  intro m hm
  rw [mem_range] at hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · rw [hA m (mem_Icc.mpr ⟨hpos, by omega⟩)]

end Vinogradov
