/-
# Vinogradov's mean value theorem: foundations (round 194)

Plain statement.
* `J s k N` counts the pairs `(x, y)` of `s`-tuples from `{1, …, N}` whose power sums agree in
  every degree `1, …, k`: `x₁ʲ + … + x_sʲ = y₁ʲ + … + y_sʲ` for `j = 1..k`. This is Vinogradov's
  mean value `∫|Σ_{n≤N} e(α₁n + … + α_k nᵏ)|^{2s} dα` (`J_eq_integral_norm`, round 195).
* Always `N^s ≤ J ≤ N^{2s}` (`J_ge`, `J_le`), and more equations mean fewer solutions (`J_anti`).
* **The rigid range `s ≤ k`** (`agree_iff`): the power sums in degrees `1..k` pin down the tuple
  up to rearrangement (Newton's identities, then Vieta). Hence `J s k N ≤ s!·N^s`
  (`J_le_diag`): only the rearrangements count.
* **Adding a variable costs at most `N²`** (`J_succ_le`, round 195). The shifted count
  `#{f x = f y + w}` never exceeds the unshifted one (`shiftCount_le`: `2ab ≤ a² + b²`, which is
  Cauchy–Schwarz in counting form).

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

/-! ## Step I.2: adding a variable costs at most `N²` -/

/-- Shifted pair count: `#{(x, y) ∈ P² : f x = f y + w}`. -/
noncomputable def shiftCount {α β : Type*} [AddCommGroup β] (P : Finset α) (f : α → β) (w : β) :
    ℕ := ((P ×ˢ P).filter fun p => f p.1 = f p.2 + w).card

/-- Pairs `(x, y) ∈ A × B` with `f x = f y + w`, counted along the fibres of `f` over any
`U ⊇ f(A)` (round 334: `shiftCount_eq_sum` and `VinoSplit.pairCount_eq_sum` are its cases). -/
lemma shiftCount₂_eq_sum {α β : Type*} [AddCommGroup β] (A B : Finset α) (f : α → β) (w : β)
    (U : Finset β) (hU : ∀ x ∈ A, f x ∈ U) :
    ((A ×ˢ B).filter fun p => f p.1 = f p.2 + w).card =
      ∑ v ∈ U, (A.filter fun x => f x = v).card * (B.filter fun x => f x = v - w).card := by
  rw [card_eq_sum_card_fiberwise (f := fun p => f p.1) (t := U)]
  · apply sum_congr rfl
    intro v _
    rw [← card_product]
    congr 1
    ext p
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h2, by rw [← h4, h3]; abel⟩
    · rintro ⟨⟨h1, h4⟩, h2, h5⟩
      exact ⟨⟨⟨h1, h2⟩, by rw [h4, h5]; abel⟩, h4⟩
  · intro p hp
    have hp' := mem_coe.mp hp
    rw [mem_filter, mem_product] at hp'
    exact mem_coe.mpr (hU _ hp'.1.1)

lemma shiftCount_eq_sum {α β : Type*} [AddCommGroup β] (P : Finset α) (f : α → β) (w : β) :
    shiftCount P f w = ∑ v ∈ P.image f,
      (P.filter fun x => f x = v).card * (P.filter fun x => f x = v - w).card :=
  shiftCount₂_eq_sum P P f w _ fun _ => mem_image_of_mem f

/-- **Cauchy–Schwarz in counting form:** the shifted count never beats the unshifted one. -/
theorem shiftCount_le {α β : Type*} [AddCommGroup β] (P : Finset α) (f : α → β) (w : β) :
    shiftCount P f w ≤ shiftCount P f 0 := by
  set r : β → ℕ := fun v => (P.filter fun x => f x = v).card with hr
  set V := P.image f
  have h0 : shiftCount P f 0 = ∑ v ∈ V, r v ^ 2 := by
    rw [shiftCount_eq_sum]; apply sum_congr rfl; intro v _; simp [hr, sq]
  have hzero : ∀ u ∉ V, r u = 0 := by
    intro u hu
    simp only [hr, card_eq_zero, filter_eq_empty_iff]
    intro x hx hfx
    exact hu (hfx ▸ mem_image_of_mem f hx)
  have hshift : ∑ v ∈ V, r (v - w) ^ 2 ≤ ∑ v ∈ V, r v ^ 2 := by
    have e : ∑ v ∈ V, r (v - w) ^ 2 = ∑ u ∈ V.image (· - w), r u ^ 2 := by
      rw [sum_image (fun a _ b _ h => sub_left_injective h)]
    rw [e]
    calc ∑ u ∈ V.image (· - w), r u ^ 2 ≤ ∑ u ∈ V.image (· - w) ∪ V, r u ^ 2 :=
          sum_le_sum_of_subset subset_union_left
      _ = ∑ u ∈ V, r u ^ 2 := by
          symm
          apply sum_subset subset_union_right
          intro u _ hu
          simp [hzero u hu]
  rw [shiftCount_eq_sum, h0]
  have hamgm : ∀ v ∈ V, r v * r (v - w) * 2 ≤ r v ^ 2 + r (v - w) ^ 2 := by
    intro v _
    zify
    nlinarith [sq_nonneg ((r v : ℤ) - r (v - w))]
  have hsum := sum_le_sum hamgm
  rw [← sum_mul, sum_add_distrib] at hsum
  change ∑ v ∈ V, r v * r (v - w) ≤ ∑ v ∈ V, r v ^ 2
  omega

/-- The power-sum vector `(Σ xᵢ, Σ xᵢ², …, Σ xᵢᵏ)`, in `ℤᵏ`. -/
def pv (k : ℕ) {s : ℕ} (x : Fin s → ℕ) : Fin k → ℤ := fun j => ((∑ i, x i ^ (j.val + 1) : ℕ) : ℤ)

lemma agree_iff_pv {s k : ℕ} (x y : Fin s → ℕ) : Agree k x y ↔ pv k x = pv k y := by
  constructor
  · intro h
    funext j
    simp only [pv]
    exact_mod_cast h (j.val + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro h j hj
    rw [mem_Icc] at hj
    have := congrFun h ⟨j - 1, by omega⟩
    simp only [pv, show j - 1 + 1 = j by omega] at this
    exact_mod_cast this

lemma J_eq_shiftCount (s k N : ℕ) : J s k N = shiftCount (box s N) (pv k) 0 := by
  unfold J shiftCount
  congr 1
  ext p
  simp only [mem_filter, agree_iff_pv, add_zero]

/-- **Step I.2.** `J_{s+1,k}(N) ≤ N² · J_{s,k}(N)`. -/
theorem J_succ_le (s k N : ℕ) : J (s + 1) k N ≤ N ^ 2 * J s k N := by
  set S := (box (s + 1) N ×ˢ box (s + 1) N).filter fun p => Agree k p.1 p.2 with hS
  set ν : ℕ → Fin k → ℤ := fun a j => ((a ^ (j.val + 1) : ℕ) : ℤ) with hν
  have hpv : ∀ x : Fin (s + 1) → ℕ, pv k x = ν (x 0) + pv k (Fin.tail x) := by
    intro x; funext j
    simp [pv, hν, Fin.sum_univ_succ, Fin.tail]
  have hfib : ∀ ab ∈ Icc 1 N ×ˢ Icc 1 N,
      (S.filter fun p => (p.1 0, p.2 0) = ab).card ≤ J s k N := by
    intro ab _
    rw [J_eq_shiftCount]
    refine le_trans ?_ (shiftCount_le (box s N) (pv k) (ν ab.2 - ν ab.1))
    unfold shiftCount
    refine card_le_card_of_injOn (fun p => (Fin.tail p.1, Fin.tail p.2)) ?_ ?_
    · intro p hp
      rw [coe_filter, Set.mem_ofPred_eq, hS, mem_filter, mem_product] at hp
      obtain ⟨⟨⟨hx, hy⟩, hag⟩, hab⟩ := hp
      have ha : p.1 0 = ab.1 := congrArg Prod.fst hab
      have hb : p.2 0 = ab.2 := congrArg Prod.snd hab
      rw [agree_iff_pv, hpv, hpv, ha, hb] at hag
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [box, Fintype.mem_piFinset] at hx ⊢; exact fun i => hx i.succ
      · rw [box, Fintype.mem_piFinset] at hy ⊢; exact fun i => hy i.succ
      · rw [← sub_eq_zero] at hag ⊢; rw [← hag]; abel
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_ofPred_eq] at hp hq
      simp only [Prod.mk.injEq] at hpq
      have h2 : p.2 0 = q.2 0 := by
        have := congrArg Prod.snd (hp.2.trans hq.2.symm); exact this
      have h1' : p.1 0 = q.1 0 := by
        have := congrArg Prod.fst (hp.2.trans hq.2.symm); exact this
      refine Prod.ext ?_ ?_
      · rw [← Fin.cons_self_tail p.1, ← Fin.cons_self_tail q.1, hpq.1, h1']
      · rw [← Fin.cons_self_tail p.2, ← Fin.cons_self_tail q.2, hpq.2, h2]
  unfold J
  rw [← hS, card_eq_sum_card_fiberwise (f := fun p => (p.1 0, p.2 0)) (t := Icc 1 N ×ˢ Icc 1 N)]
  · calc ∑ ab ∈ Icc 1 N ×ˢ Icc 1 N, (S.filter fun p => (p.1 0, p.2 0) = ab).card
        ≤ ∑ _ab ∈ Icc 1 N ×ˢ Icc 1 N, J s k N := sum_le_sum hfib
      _ = N ^ 2 * J s k N := by rw [sum_const, card_product, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
  · intro p hp
    rw [coe_filter, Set.mem_ofPred_eq, mem_product] at hp
    obtain ⟨⟨hx, hy⟩, _⟩ := hp
    rw [box, Fintype.mem_piFinset] at hx hy
    exact mem_coe.mpr (mem_product.mpr ⟨hx 0, hy 0⟩)

/-! ## Step I.1: orthogonality — the count is the moment of a Weyl sum -/

section Orthogonality

open Complex MeasureTheory

/-- `e(t) = exp(2πit)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * t)

lemma ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; push_cast; ring_nf

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee; rw [← Complex.exp_sum]; push_cast; rw [Finset.mul_sum]

lemma conj_ee (t : ℝ) : (starRingEnd ℂ) (ee t) = ee (-t) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [show (2 : ℂ) * Real.pi * I * t = ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma integral_ee_int (m : ℤ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, ee (m * t) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm; simp [ee_zero]
  · have hc : (2 * Real.pi * I * m : ℂ) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, Complex.I_ne_zero]
    have e : ∀ t : ℝ, ee (m * t) = Complex.exp ((2 * Real.pi * I * m) * t) := by
      intro t; unfold ee; push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * I * m * (1 : ℝ)) = 1 := by
      rw [show (2 : ℂ) * Real.pi * I * m * ((1 : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]; simp

/-- The unit torus `(0,1]^k` with Lebesgue measure. -/
noncomputable def torus (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ioc (0 : ℝ) 1)

instance (k : ℕ) : IsFiniteMeasure (torus k) := by unfold torus; infer_instance

/-- Orthogonality on the torus: `∫ e(m·α) dα = [m = 0]`. -/
lemma integral_torus {k : ℕ} (m : Fin k → ℤ) :
    ∫ α, ee (∑ j, (m j : ℝ) * α j) ∂torus k = if m = 0 then 1 else 0 := by
  simp_rw [ee_sum]
  unfold torus
  rw [integral_fintype_prod_eq_prod (f := fun j t => ee ((m j : ℝ) * t))]
  simp_rw [integral_ee_int]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  congr 1
  exact propext ⟨fun h => funext h, fun h j => congrFun h j⟩

/-- The Weyl sum `Σ_{n ≤ N} e(α₁n + α₂n² + … + α_k nᵏ)`. -/
noncomputable def wsum (k N : ℕ) (α : Fin k → ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, ee (∑ j : Fin k, α j * (n : ℝ) ^ (j.val + 1))

lemma wsum_pow (s k N : ℕ) (α : Fin k → ℝ) :
    wsum k N α ^ s = ∑ x ∈ box s N, ee (∑ j, (pv k x j : ℝ) * α j) := by
  have h1 : wsum k N α ^ s = ∏ _i : Fin s, wsum k N α := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, wsum, Finset.prod_univ_sum]
  apply sum_congr rfl
  intro x _
  rw [← ee_sum]
  congr 1
  simp only [pv]
  push_cast
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  ring

lemma integrable_ee {k : ℕ} (g : (Fin k → ℝ) → ℝ) (hg : Continuous g) :
    Integrable (fun α => ee (g α)) (torus k) :=
  Integrable.of_bound (continuous_ee.comp hg).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => (norm_ee _).le)

/-- The generating function of a finite set `X` of points `φ x ∈ ℤᵏ` (from `VinoHolder.lean` since
round 334). -/
noncomputable def E {β : Type*} {k : ℕ} (X : Finset β) (φ : β → Fin k → ℤ) (α : Fin k → ℝ) : ℂ :=
  ∑ x ∈ X, ee (∑ j, (φ x j : ℝ) * α j)

/-- **Orthogonality for any finite set.** `∫ |E_X|² = #{(x, y) ∈ X² : φ x = φ y}` (from
`VinoHolder.lean` since round 334). -/
theorem count_eq_integral {β : Type*} {k : ℕ} (X : Finset β) (φ : β → Fin k → ℤ) :
    ((((X ×ˢ X).filter fun q => φ q.1 = φ q.2).card : ℕ) : ℝ) =
      ∫ α, ‖E X φ α‖ ^ 2 ∂torus k := by
  have hc : ((((X ×ˢ X).filter fun q => φ q.1 = φ q.2).card : ℕ) : ℂ) =
      ∫ α, E X φ α * (starRingEnd ℂ) (E X φ α) ∂torus k := by
    have hexp : ∀ α, E X φ α * (starRingEnd ℂ) (E X φ α) =
        ∑ x ∈ X, ∑ y ∈ X, ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j) := by
      intro α
      rw [E, map_sum, Finset.sum_mul_sum]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      rw [conj_ee, ← ee_add]
      congr 1
      push_cast
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply sum_congr rfl; intro j _; ring
    simp_rw [hexp]
    have hint : ∀ x y : β, Integrable
        (fun α => ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j)) (torus k) := fun x y =>
      integrable_ee _ (by fun_prop)
    rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hint x y))]
    simp_rw [integral_finsetSum _ (fun y _ => hint _ y)]
    have e : ∀ x y : β, ∫ α, ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j) ∂torus k =
        if φ x = φ y then 1 else 0 := by
      intro x y
      rw [show (fun α : Fin k → ℝ => ee (∑ j, ((φ x j - φ y j : ℤ) : ℝ) * α j)) =
        fun α => ee (∑ j, (((φ x - φ y) j : ℤ) : ℝ) * α j) by rfl, integral_torus]
      simp only [sub_eq_zero]
    simp_rw [e]
    rw [← Finset.sum_product', Finset.sum_boole]
  have e2 : ∀ α, E X φ α * (starRingEnd ℂ) (E X φ α) = ((‖E X φ α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e2, integral_complex_ofReal] at hc
  exact_mod_cast hc

/-- **Step I.1 (orthogonality).** `J_{s,k}(N) = ∫_{(0,1]^k} |Σ_{n ≤ N} e(α₁n + … + α_k nᵏ)|^{2s} dα`:
`count_eq_integral` at `X = box s N`, `φ = pv k` (round 334). -/
theorem J_eq_integral_norm (s k N : ℕ) :
    (J s k N : ℝ) = ∫ α, ‖wsum k N α‖ ^ (2 * s) ∂torus k := by
  have h := count_eq_integral (box s N) (pv k)
  simp only [E, ← wsum_pow, norm_pow, ← pow_mul, mul_comm s 2] at h
  rw [J_eq_shiftCount, shiftCount, ← h]
  simp only [add_zero]

/-- **Step I.1 (orthogonality), complex form.** `J = ∫ f^s · conj(f)^s` over the torus (from
`J_eq_integral_norm` since round 334). -/
theorem J_eq_integral (s k N : ℕ) :
    (J s k N : ℂ) = ∫ α, wsum k N α ^ s * (starRingEnd ℂ) (wsum k N α) ^ s ∂torus k := by
  have e : ∀ α, wsum k N α ^ s * (starRingEnd ℂ) (wsum k N α) ^ s =
      ((‖wsum k N α‖ ^ (2 * s) : ℝ) : ℂ) := by
    intro α
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp_rw [e, integral_complex_ofReal]
  exact_mod_cast J_eq_integral_norm s k N

end Orthogonality

end Vinogradov
