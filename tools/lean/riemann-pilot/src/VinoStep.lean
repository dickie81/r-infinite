/-
# Vinogradov's mean value theorem, step I.3b: the conditioned count (round 197)

Plain statement (`cond_count`). Fix a prime `p > k` with `P ≤ p^k`, a shift `a`, and a
`k`-tuple `u'`. The `k`-tuples `u ∈ [1,P]^k` satisfy both:
* the residues of `u − a` mod `p` are distinct;
* `Σ(uᵢ−a)^j ≡ Σ(u'ᵢ−a)^j (mod p^j)` for `j = 1..k`.
They number at most `k!·p^{k(k−1)/2}`.

This is Step C of `frontier/vmvt/KARATSUBA_SPEC.md`. The proof has three parts.
* Newton's identities over `ZMod p` (`p > k`, `map_eq_of_psum_field`): the residues of
  `u − a` rearrange those of `u' − a`, so there are at most `k!` residue vectors
  (`card_multiset_fibre_le`).
* For each residue vector, Linnik's lemma in integer form (`linnikZ`) gives at most
  `p^{k(k−1)/2}` tuples.
* `P ≤ p^k` makes `u ↦ u − a (mod p^k)` injective.
-/
import Vinogradov
import VinoPadic

open Finset MvPolynomial

namespace VinoStep

/-! ## Newton's identities over a field of large characteristic -/

theorem esymm_eq_of_psum_field {F : Type*} [Field F] {s : ℕ}
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ s → (n : F) ≠ 0) (x y : Fin s → F)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ n, n ≤ s → (univ.val.map x).esymm n = (univ.val.map y).esymm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Multiset.esymm]
  have key : ∀ z : Fin s → F, (n : F) * (univ.val.map z).esymm n = (-1) ^ (n + 1) *
      ∑ a ∈ antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (univ.val.map z).esymm a.1 * ∑ i, z i ^ a.2 := by
    intro z
    have := congrArg (aeval z) (MvPolynomial.mul_esymm_eq_sum (Fin s) F n)
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
  exact mul_left_cancel₀ (hchar n hpos hn) (hx.trans hy.symm)

theorem map_eq_of_psum_field {F : Type*} [Field F] {s : ℕ}
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ s → (n : F) ≠ 0) (x y : Fin s → F)
    (h : ∀ j, 1 ≤ j → j ≤ s → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    univ.val.map x = univ.val.map y := by
  have hc : Multiset.card (univ.val.map x) = s := by simp
  have hc' : Multiset.card (univ.val.map y) = s := by simp
  have hp : ((univ.val.map x).map fun t => Polynomial.X - Polynomial.C t).prod =
      ((univ.val.map y).map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hc, hc']
    apply sum_congr rfl
    intro j hj
    rw [esymm_eq_of_psum_field hchar x y h j (by rw [mem_range] at hj; omega)]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

lemma natCast_ne_zero_zmod {p k : ℕ} (hpk : k < p) :
    ∀ n : ℕ, 1 ≤ n → n ≤ k → (n : ZMod p) ≠ 0 := by
  intro n h1 h2 h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- At most `k!` tuples share a given multiset of values. -/
lemma card_multiset_fibre_le {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (b' : Fin k → α) :
    (univ.filter fun b : Fin k → α => univ.val.map b = univ.val.map b').card ≤ k.factorial := by
  calc (univ.filter fun b : Fin k → α => univ.val.map b = univ.val.map b').card
      ≤ ((List.ofFn b').permutations.toFinset).card := by
        refine card_le_card_of_injOn (fun b => List.ofFn b) ?_ ?_
        · intro b hb
          rw [coe_filter, Set.mem_ofPred_eq] at hb
          rw [mem_coe, List.mem_toFinset, List.mem_permutations]
          have h := hb.2
          rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h
          exact h
        · intro b _ c _ h
          exact List.ofFn_injective h
    _ ≤ (List.ofFn b').permutations.length := List.toFinset_card_le _
    _ = k.factorial := by rw [List.length_permutations, List.length_ofFn]

/-! ## Linnik's lemma for integer tuples -/

lemma card_residue_le_int (p k j : ℕ) (c : ℤ) (hp : 0 < p) (hjk : j ≤ k) :
    ((Ico (0 : ℤ) ((p : ℤ) ^ k)).filter fun v => (p : ℤ) ^ j ∣ v - c).card ≤ p ^ (k - j) := by
  have hpj : (0 : ℤ) < (p : ℤ) ^ j := by positivity
  have hsplit : (p : ℤ) ^ k = (p : ℤ) ^ j * (p : ℤ) ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjk]
  calc ((Ico (0 : ℤ) ((p : ℤ) ^ k)).filter fun v => (p : ℤ) ^ j ∣ v - c).card
      ≤ (Ico (0 : ℤ) ((p : ℤ) ^ (k - j))).card := by
        refine card_le_card_of_injOn (fun v => v / (p : ℤ) ^ j) ?_ ?_
        · intro v hv
          rw [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hv
          rw [mem_coe, mem_Ico]
          constructor
          · exact Int.ediv_nonneg hv.1.1 hpj.le
          · rw [Int.ediv_lt_iff_lt_mul hpj, mul_comm, ← hsplit]; exact hv.1.2
        · intro v hv w hw hvw
          rw [coe_filter, Set.mem_ofPred_eq] at hv hw
          have hm : v % (p : ℤ) ^ j = w % (p : ℤ) ^ j := by
            have hcv : c ≡ v [ZMOD (p : ℤ) ^ j] := (Int.modEq_iff_dvd).mpr hv.2
            have hcw : c ≡ w [ZMOD (p : ℤ) ^ j] := (Int.modEq_iff_dvd).mpr hw.2
            exact hcv.symm.trans hcw
          simp only at hvw
          rw [← Int.mul_ediv_add_emod v ((p : ℤ) ^ j), ← Int.mul_ediv_add_emod w ((p : ℤ) ^ j), hvw, hm]
    _ = p ^ (k - j) := by rw [Int.card_Ico, sub_zero, ← Nat.cast_pow, Int.toNat_natCast]

/-- **Linnik's lemma, integer form.** On any finite set of integer `k`-tuples that is injective
mod `p^k`, the tuples in a fixed distinct residue class mod `p` with `Σ xᵢʲ ≡ c_j (mod p^j)`
(`j = 1..k`) number at most `p^{k(k−1)/2}`. -/
theorem linnikZ {k p : ℕ} (hp : p.Prime) (hpk : k < p) (X : Finset (Fin k → ℤ))
    (hX : ∀ x ∈ X, ∀ y ∈ X, (∀ i, (p : ℤ) ^ k ∣ y i - x i) → x = y)
    (b : Fin k → ZMod p) (hb : Function.Injective b) (c : ℕ → ℤ) :
    (X.filter fun x => (∀ i, (x i : ZMod p) = b i) ∧
        ∀ j ∈ Icc 1 k, (p : ℤ) ^ j ∣ ∑ i, x i ^ j - c j).card ≤ p ^ (k * (k - 1) / 2) := by
  rw [← VinoPadic.linnik_exponent]
  have hp0 : 0 < p := hp.pos
  have hpk0 : (0 : ℤ) < (p : ℤ) ^ k := by positivity
  set T := Fintype.piFinset fun e : Fin k =>
    (Ico (0 : ℤ) ((p : ℤ) ^ k)).filter fun v => (p : ℤ) ^ ((e : ℕ) + 1) ∣ v - c ((e : ℕ) + 1)
    with hT
  have hTcard : T.card ≤ ∏ e : Fin k, p ^ (k - (e + 1)) := by
    rw [hT, Fintype.card_piFinset]
    exact Finset.prod_le_prod fun e _ => card_residue_le_int p k _ _ hp0 (by omega)
  refine le_trans ?_ hTcard
  refine card_le_card_of_injOn (fun x e => (∑ i, x i ^ ((e : ℕ) + 1)) % (p : ℤ) ^ k) ?_ ?_
  · intro x hx
    rw [coe_filter, Set.mem_ofPred_eq] at hx
    rw [mem_coe, hT, Fintype.mem_piFinset]
    intro e
    rw [mem_filter, mem_Ico]
    refine ⟨⟨Int.emod_nonneg _ hpk0.ne', Int.emod_lt_of_pos _ hpk0⟩, ?_⟩
    have hc := hx.2.2 ((e : ℕ) + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hdk : (p : ℤ) ^ ((e : ℕ) + 1) ∣ (p : ℤ) ^ k := pow_dvd_pow _ (by omega)
    have e1 : (∑ i, x i ^ ((e : ℕ) + 1)) % (p : ℤ) ^ k - c ((e : ℕ) + 1) =
        (∑ i, x i ^ ((e : ℕ) + 1) - c ((e : ℕ) + 1)) -
          (p : ℤ) ^ k * ((∑ i, x i ^ ((e : ℕ) + 1)) / (p : ℤ) ^ k) := by
      rw [Int.emod_def]; ring
    rw [e1]
    exact dvd_sub hc (hdk.mul_right _)
  · intro x hx y hy hxy
    rw [coe_filter, Set.mem_ofPred_eq] at hx hy
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; funext i; exact i.elim0
    have hdx : Function.Injective fun i => (x i : ZMod p) := by
      have : (fun i => (x i : ZMod p)) = b := funext hx.2.1
      rw [this]; exact hb
    have h1 : ∀ i, (p : ℤ) ∣ y i - x i := fun i =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ((hx.2.1 i).trans (hy.2.1 i).symm)
    have hsum : ∀ j ∈ Icc 1 k, (p : ℤ) ^ k ∣ ∑ i, y i ^ j - ∑ i, x i ^ j := by
      intro j hj
      rw [mem_Icc] at hj
      have := congrFun hxy ⟨j - 1, by omega⟩
      simp only [show j - 1 + 1 = j by omega] at this
      exact Int.ModEq.dvd this
    exact hX x hx.1 y hy.1 (VinoPadic.rigid hp hpk hk x y hdx h1 hsum)

/-! ## Step C: the conditioned count -/

/-- **Conditioned count (Step C).** For a prime `p > k` with `P ≤ p^k`, a shift `a` and a
`k`-tuple `u'`: the `u ∈ [1,P]^k` with `u − a` distinct mod `p` and
`Σ(uᵢ−a)^j ≡ Σ(u'ᵢ−a)^j (mod p^j)` for `j = 1..k` number at most `k!·p^{k(k−1)/2}`. -/
theorem cond_count {k p P : ℕ} (hp : p.Prime) (hpk : k < p) (hP : P ≤ p ^ k) (a : ℤ)
    (u' : Fin k → ℕ) :
    ((Vinogradov.box k P).filter fun u =>
        Function.Injective (fun i => (((u i : ℤ) - a : ℤ) : ZMod p)) ∧
        ∀ j ∈ Icc 1 k, (p : ℤ) ^ j ∣
          ∑ i, ((u i : ℤ) - a) ^ j - ∑ i, ((u' i : ℤ) - a) ^ j).card ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  set S := (Vinogradov.box k P).filter fun u =>
    Function.Injective (fun i => (((u i : ℤ) - a : ℤ) : ZMod p)) ∧
    ∀ j ∈ Icc 1 k, (p : ℤ) ^ j ∣ ∑ i, ((u i : ℤ) - a) ^ j - ∑ i, ((u' i : ℤ) - a) ^ j with hS
  set β : (Fin k → ℕ) → (Fin k → ZMod p) := fun u i => (((u i : ℤ) - a : ℤ) : ZMod p) with hβ
  set b' := β u' with hb'
  have himg : S.image β ⊆ univ.filter (fun b => univ.val.map b = univ.val.map b') := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hb
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    apply map_eq_of_psum_field (natCast_ne_zero_zmod hpk)
    intro j h1 h2
    have hu' := (mem_filter.mp hu).2.2 j (mem_Icc.mpr ⟨h1, h2⟩)
    have hd : (p : ℤ) ∣ ∑ i, ((u i : ℤ) - a) ^ j - ∑ i, ((u' i : ℤ) - a) ^ j :=
      (dvd_pow_self (p : ℤ) (by omega)).trans hu'
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr hd
    simp only [hb', hβ]
    push_cast at this ⊢
    exact this.symm
  have hfib : ∀ b ∈ S.image β, (S.filter fun u => β u = b).card ≤ p ^ (k * (k - 1) / 2) := by
    intro b hb
    obtain ⟨u0, hu0, hub⟩ := mem_image.mp hb
    have hbinj : Function.Injective b := hub ▸ (mem_filter.mp hu0).2.1
    set X := (Vinogradov.box k P).image (fun u i => (u i : ℤ) - a) with hXdef
    have hPk : (P : ℤ) ≤ (p : ℤ) ^ k := by exact_mod_cast hP
    have hX : ∀ x ∈ X, ∀ y ∈ X, (∀ i, (p : ℤ) ^ k ∣ y i - x i) → x = y := by
      intro x hx y hy h
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      funext i
      have hui := Fintype.mem_piFinset.mp hu i
      have hvi := Fintype.mem_piFinset.mp hv i
      rw [mem_Icc] at hui hvi
      have hui' : (1 : ℤ) ≤ u i ∧ (u i : ℤ) ≤ P := ⟨by exact_mod_cast hui.1, by exact_mod_cast hui.2⟩
      have hvi' : (1 : ℤ) ≤ v i ∧ (v i : ℤ) ≤ P := ⟨by exact_mod_cast hvi.1, by exact_mod_cast hvi.2⟩
      have h0 : ((v i : ℤ) - a) - ((u i : ℤ) - a) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd (h i)
        rw [abs_lt]; constructor <;> linarith
      linarith
    calc (S.filter fun u => β u = b).card
        ≤ (X.filter fun x => (∀ i, (x i : ZMod p) = b i) ∧
            ∀ j ∈ Icc 1 k, (p : ℤ) ^ j ∣ ∑ i, x i ^ j - ∑ i, ((u' i : ℤ) - a) ^ j).card := by
          refine card_le_card_of_injOn (fun u i => (u i : ℤ) - a) ?_ ?_
          · intro u hu
            rw [coe_filter, Set.mem_ofPred_eq, hS, mem_filter] at hu
            rw [coe_filter, Set.mem_ofPred_eq]
            refine ⟨mem_image_of_mem _ hu.1.1, fun i => ?_, hu.1.2.2⟩
            exact congrFun hu.2 i
          · intro u _ v _ h
            funext i
            have := congrFun h i
            simp only at this
            exact_mod_cast (sub_left_inj.mp this)
      _ ≤ p ^ (k * (k - 1) / 2) :=
          linnikZ hp hpk X hX b hbinj (fun j => ∑ i, ((u' i : ℤ) - a) ^ j)
  calc S.card ≤ p ^ (k * (k - 1) / 2) * (S.image β).card := card_le_mul_card_image S _ hfib
    _ ≤ p ^ (k * (k - 1) / 2) * k.factorial :=
        Nat.mul_le_mul_left _ ((card_le_card himg).trans (card_multiset_fibre_le b'))
    _ = k.factorial * p ^ (k * (k - 1) / 2) := mul_comm _ _

end VinoStep
