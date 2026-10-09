/-
# Vinogradov's mean value theorem, step I.3b: the good/bad split (round 200)

Plain statement (`stepA`). With `n = k + s` variables per side, call a tuple *bad* if its
coordinates occupy fewer than `k` residue classes mod `p`, and *good* otherwise. Then
  `J_{k+s,k}(P) ≤ 2·T_BB + 16·(k+s)^{2k}·G`,
where `T_BB` counts agreeing pairs of bad tuples and `G` is the conditioned count of
round 199 (`Gfull`).

Proof.
* Split `T` by whether `x` is good; swap `x` and `y` to bound the bad part:
  `T ≤ 2·T(x good) + T_BB`.
* A good tuple has an injective `k`-subtuple `ι` with distinct residues (`exists_inj`), so
  `T(x good) ≤ Σ_ι T_ι`.
* Cauchy–Schwarz in counting form (`pairCount_sq_le`): `T_ι² ≤ G_ι·T`.
* A permutation carrying the first `k` slots to `ι` (`exists_perm`) gives `G_ι ≤ G`.
-/
import VinoHolder

open Finset

namespace VinoSplit

open Vinogradov VinoIter VinoHolder

/-- Agreeing pairs from `A × B`. -/
def pairCount {β : Type*} {k : ℕ} (A B : Finset β) (φ : β → Fin k → ℤ) : ℕ :=
  ((A ×ˢ B).filter fun q => φ q.1 = φ q.2).card

section counting
variable {β : Type*} {k : ℕ} (φ : β → Fin k → ℤ)

lemma pairCount_eq_sum (A B : Finset β) (U : Finset (Fin k → ℤ)) (hU : A.image φ ⊆ U) :
    pairCount A B φ = ∑ v ∈ U, (A.filter fun x => φ x = v).card * (B.filter fun x => φ x = v).card := by
  have h := shiftCount₂_eq_sum A B φ 0 U (fun _ hx => hU (mem_image_of_mem φ hx))
  simp only [add_zero, sub_zero] at h
  unfold pairCount
  convert h

/-- **Cauchy–Schwarz in counting form.** `pairCount(A,B)² ≤ pairCount(A,A)·pairCount(B,B)`. -/
lemma pairCount_sq_le [DecidableEq β] (A B : Finset β) :
    pairCount A B φ ^ 2 ≤ pairCount A A φ * pairCount B B φ := by
  set U := A.image φ ∪ B.image φ
  rw [pairCount_eq_sum φ A B U subset_union_left, pairCount_eq_sum φ A A U subset_union_left,
    pairCount_eq_sum φ B B U subset_union_right]
  have := sum_mul_sq_le_sq_mul_sq U (fun v => (A.filter fun x => φ x = v).card)
    (fun v => (B.filter fun x => φ x = v).card)
  simpa [sq] using this

lemma pairCount_mono {A A' B B' : Finset β} (hA : A ⊆ A') (hB : B ⊆ B') :
    pairCount A B φ ≤ pairCount A' B' φ :=
  card_le_card (filter_subset_filter _ (product_subset_product hA hB))

lemma pairCount_split (A B : Finset β) (c : β → Prop) [DecidablePred c] :
    pairCount A B φ = pairCount (A.filter c) B φ + pairCount (A.filter fun x => ¬ c x) B φ := by
  unfold pairCount
  rw [← card_filter_add_card_filter_not (fun q : β × β => c q.1)]
  congr 1 <;> congr 1 <;> ext q <;> simp only [mem_filter, mem_product] <;> tauto

lemma pairCount_swap_le (A B : Finset β) : pairCount A B φ ≤ pairCount B A φ := by
  unfold pairCount
  refine card_le_card_of_injOn Prod.swap ?_ (fun a _ b _ h => Prod.swap_injective h)
  intro q hq
  have hq' := mem_coe.mp hq
  rw [mem_filter, mem_product] at hq'
  exact mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨hq'.1.2, hq'.1.1⟩, hq'.2.symm⟩)

lemma pairCount_biUnion_le [DecidableEq β] {ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Finset β)
    (B : Finset β) : pairCount (I.biUnion A) B φ ≤ ∑ i ∈ I, pairCount (A i) B φ := by
  unfold pairCount
  calc ((I.biUnion A ×ˢ B).filter fun q => φ q.1 = φ q.2).card
      ≤ (I.biUnion fun i => (A i ×ˢ B).filter fun q => φ q.1 = φ q.2).card := by
        apply card_le_card
        intro q hq
        rw [mem_filter, mem_product, mem_biUnion] at hq
        obtain ⟨⟨⟨i, hi, hqa⟩, hqb⟩, hag⟩ := hq
        exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_product.mpr ⟨hqa, hqb⟩, hag⟩⟩
    _ ≤ _ := card_biUnion_le

end counting

/-- An injection `Fin k → Fin n` extends a given one to a permutation. -/
lemma exists_perm {n k : ℕ} (ι₀ ι : Fin k → Fin n) (h0 : Function.Injective ι₀)
    (hι : Function.Injective ι) : ∃ σ : Equiv.Perm (Fin n), ∀ i, σ (ι₀ i) = ι i := by
  classical
  let e := (Equiv.ofInjective ι₀ h0).symm.trans (Equiv.ofInjective ι hι)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (ι₀ i) ⟨i, rfl⟩]
  simp [e, Equiv.ofInjective_symm_apply]

/-- A tuple meeting at least `k` residue classes has an injective `k`-subtuple with distinct
residues. -/
lemma exists_inj {n k p : ℕ} (x : Fin n → ℕ)
    (h : k ≤ (univ.image fun i => (x i : ZMod p)).card) :
    ∃ ι : Fin k → Fin n, Function.Injective ι ∧ Function.Injective (fun i => (x (ι i) : ZMod p)) := by
  classical
  obtain ⟨t, ht, htc⟩ := exists_subset_card_eq h
  have hpre : ∀ r : t, ∃ i, (x i : ZMod p) = r := by
    intro r
    obtain ⟨i, _, hi⟩ := mem_image.mp (ht r.2)
    exact ⟨i, hi⟩
  choose f hf using hpre
  let e : Fin k ≃ t := (t.equivFin.trans (finCongr htc)).symm
  have hinj : Function.Injective (fun j => (x (f (e j)) : ZMod p)) := by
    intro a b hab
    simp only [hf] at hab
    exact e.injective (Subtype.ext hab)
  exact ⟨fun j => f (e j), hinj.of_comp (f := fun i => (x i : ZMod p)), hinj⟩

/-- Bad tuples: fewer than `k` residue classes mod `p`. -/
def isBad (k p : ℕ) {n : ℕ} (x : Fin n → ℕ) : Prop :=
  (univ.image fun i => (x i : ZMod p)).card < k

instance (k p : ℕ) {n : ℕ} : DecidablePred (isBad k p (n := n)) := fun x => by
  unfold isBad; infer_instance

/-- Tuples whose `ι`-subtuple has distinct residues. -/
def Aι (P p : ℕ) {n k : ℕ} (ι : Fin k → Fin n) : Finset (Fin n → ℕ) :=
  (box n P).filter fun x => Function.Injective fun i => (x (ι i) : ZMod p)

/-- The bad-bad count. -/
def TBB (k s P p : ℕ) : ℕ :=
  pairCount ((box (k + s) P).filter (isBad k p)) ((box (k + s) P).filter (isBad k p)) (pv k)

lemma G_ι_le {k s P p : ℕ} (ι : Fin k → Fin (k + s)) (hι : Function.Injective ι) :
    pairCount (Aι P p ι) (Aι P p ι) (pv k) ≤ Gfull k s P p := by
  obtain ⟨σ, hσ⟩ := exists_perm (Fin.castAdd s) ι (Fin.castAdd_injective k s) hι
  have hpv : ∀ x : Fin (k + s) → ℕ, pv k (x ∘ σ) = pv k x := by
    intro x; funext j; simp only [pv, Function.comp]
    congr 1
    exact Equiv.sum_comp σ (fun i => x i ^ (j.val + 1))
  have hsplit : ∀ x : Fin (k + s) → ℕ, pv k x =
      pv k (fun i => x (Fin.castAdd s i)) + pv k (fun i => x (Fin.natAdd k i)) := by
    intro x; funext j; simp only [pv, Pi.add_apply, Fin.sum_univ_add]; push_cast; ring
  unfold pairCount Gfull
  refine card_le_card_of_injOn (fun q =>
    (((fun i => q.1 (σ (Fin.castAdd s i))), (fun i => q.1 (σ (Fin.natAdd k i)))),
     ((fun i => q.2 (σ (Fin.castAdd s i))), (fun i => q.2 (σ (Fin.natAdd k i)))))) ?_ ?_
  · intro q hq
    have hq' := mem_coe.mp hq
    simp only [Aι, mem_filter, mem_product] at hq'
    obtain ⟨⟨⟨hx, hxd⟩, hy, hyd⟩, hag⟩ := hq'
    rw [Vinogradov.box, Fintype.mem_piFinset] at hx hy
    apply mem_coe.mpr
    simp only [Dk, mem_filter, mem_product]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Vinogradov.box, Fintype.mem_piFinset]; exact fun i => hx _
    · intro a b hab; simp only [hσ] at hab; exact hxd hab
    · rw [Vinogradov.box, Fintype.mem_piFinset]; exact fun i => hx _
    · rw [Vinogradov.box, Fintype.mem_piFinset]; exact fun i => hy _
    · intro a b hab; simp only [hσ] at hab; exact hyd hab
    · rw [Vinogradov.box, Fintype.mem_piFinset]; exact fun i => hy _
    · have e1 := hsplit (q.1 ∘ σ)
      have e2 := hsplit (q.2 ∘ σ)
      rw [hpv] at e1 e2
      simp only [Function.comp] at e1 e2
      rw [← e1, ← e2]; exact hag
  · intro q _ r _ hqr
    simp only [Prod.mk.injEq] at hqr
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hqr
    have key : ∀ x y : Fin (k + s) → ℕ,
        (fun i => x (σ (Fin.castAdd s i))) = (fun i => y (σ (Fin.castAdd s i))) →
        (fun i => x (σ (Fin.natAdd k i))) = (fun i => y (σ (Fin.natAdd k i))) → x = y := by
      intro x y ha hb
      have : x ∘ σ = y ∘ σ := by
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · exact congrFun ha a
        · exact congrFun hb b
      funext i
      have := congrFun this (σ.symm i)
      simpa using this
    exact Prod.ext (key _ _ h1 h2) (key _ _ h3 h4)

/-- **Step A.** `J_{k+s,k}(P) ≤ 2·T_BB + 16·(k+s)^{2k}·G`. -/
theorem stepA (k s P p : ℕ) :
    J (k + s) k P ≤ 2 * TBB k s P p + 16 * (k + s) ^ (2 * k) * Gfull k s P p := by
  set n := k + s
  set B := box n P
  set T := pairCount B B (pv k) with hT
  have hJ : J n k P = T := by
    rw [J_eq_shiftCount, hT, pairCount, shiftCount]
    congr 1; ext q; simp [B]
  rw [hJ]
  set Bg := B.filter fun x => ¬ isBad k p x
  set Bb := B.filter (isBad k p)
  -- T ≤ 2·T(good) + T_BB
  have h1 : T = pairCount Bb B (pv k) + pairCount Bg B (pv k) :=
    pairCount_split (pv k) B B (isBad k p)
  have h2 : pairCount Bb B (pv k) = pairCount Bb Bb (pv k) + pairCount Bb Bg (pv k) := by
    rw [show pairCount Bb B (pv k) = pairCount B Bb (pv k) from
      le_antisymm (pairCount_swap_le _ _ _) (pairCount_swap_le _ _ _)]
    rw [pairCount_split (pv k) B Bb (isBad k p)]
    rw [show B.filter (isBad k p) = Bb from rfl,
      show pairCount (B.filter fun x => ¬ isBad k p x) Bb (pv k) = pairCount Bb Bg (pv k) from
        le_antisymm (pairCount_swap_le _ _ _) (pairCount_swap_le _ _ _)]
  have h3 : pairCount Bb Bg (pv k) ≤ pairCount Bg B (pv k) :=
    (pairCount_swap_le _ _ _).trans (pairCount_mono _ subset_rfl (filter_subset _ _))
  have hsplitT : T ≤ 2 * pairCount Bg B (pv k) + TBB k s P p := by
    have : TBB k s P p = pairCount Bb Bb (pv k) := rfl
    omega
  -- good tuples are covered by the `Aι`
  set Inj := (univ : Finset (Fin k → Fin n)).filter Function.Injective
  have hcover : Bg ⊆ Inj.biUnion (fun ι => Aι P p ι) := by
    intro x hx
    rw [mem_filter] at hx
    have hk : k ≤ (univ.image fun i => (x i : ZMod p)).card := by
      unfold isBad at hx; omega
    obtain ⟨ι, hι, hd⟩ := exists_inj x hk
    exact mem_biUnion.mpr ⟨ι, mem_filter.mpr ⟨mem_univ _, hι⟩, mem_filter.mpr ⟨hx.1, hd⟩⟩
  have hgood : pairCount Bg B (pv k) ≤ ∑ ι ∈ Inj, pairCount (Aι P p ι) B (pv k) :=
    (pairCount_mono _ hcover subset_rfl).trans (pairCount_biUnion_le _ _ _ _)
  -- Cauchy–Schwarz for each ι
  set G := Gfull k s P p
  have hι : ∀ ι ∈ Inj, pairCount (Aι P p ι) B (pv k) ^ 2 ≤ G * T := by
    intro ι hιm
    rw [mem_filter] at hιm
    exact (pairCount_sq_le _ _ _).trans (Nat.mul_le_mul_right _ (G_ι_le ι hιm.2))
  have hInj : Inj.card ≤ n ^ k := by
    refine (card_filter_le _ _).trans ?_
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  set Tg := pairCount Bg B (pv k)
  have hTg2 : Tg ^ 2 ≤ Inj.card ^ 2 * (G * T) := by
    have hcs := sum_mul_sq_le_sq_mul_sq Inj (fun ι => pairCount (Aι P p ι) B (pv k)) (fun _ => 1)
    simp only [mul_one, one_pow, sum_const, smul_eq_mul] at hcs
    have hs2 : ∑ ι ∈ Inj, pairCount (Aι P p ι) B (pv k) ^ 2 ≤ Inj.card * (G * T) := by
      calc ∑ ι ∈ Inj, pairCount (Aι P p ι) B (pv k) ^ 2 ≤ ∑ _ι ∈ Inj, G * T := sum_le_sum hι
        _ = Inj.card * (G * T) := by rw [sum_const, smul_eq_mul]
    calc Tg ^ 2 ≤ (∑ ι ∈ Inj, pairCount (Aι P p ι) B (pv k)) ^ 2 := Nat.pow_le_pow_left hgood 2
      _ ≤ (∑ ι ∈ Inj, pairCount (Aι P p ι) B (pv k) ^ 2) * Inj.card := hcs
      _ ≤ Inj.card * (G * T) * Inj.card := Nat.mul_le_mul_right _ hs2
      _ = Inj.card ^ 2 * (G * T) := by ring
  -- conclude
  by_cases hc : T ≤ 2 * TBB k s P p
  · omega
  · rw [not_le] at hc
    have hT4 : T < 4 * Tg := by omega
    have hTpos : 0 < T := by omega
    have hsq : T * T < 16 * (Inj.card ^ 2 * G) * T := by
      have : T * T < (4 * Tg) * (4 * Tg) := Nat.mul_lt_mul'' hT4 hT4
      nlinarith [hTg2]
    have hlt : T < 16 * (Inj.card ^ 2 * G) := Nat.lt_of_mul_lt_mul_right hsq
    have hInj2 : Inj.card ^ 2 ≤ n ^ (2 * k) :=
      calc Inj.card ^ 2 ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hInj 2
        _ = n ^ (2 * k) := by rw [← pow_mul, mul_comm]
    have : 16 * (Inj.card ^ 2 * G) ≤ 16 * n ^ (2 * k) * G := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hInj2)
    omega

end VinoSplit
