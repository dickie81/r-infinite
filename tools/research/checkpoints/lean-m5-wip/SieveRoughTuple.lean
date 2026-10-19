import Mathlib

open Finset

namespace SieveRoughTuple

/-- The non-increasing `n`-tuples of primes at least `z` with product at most `Y`. -/
def tuples (z Y n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => (Finset.range (Y + 1)).filter Nat.Prime)).filter
    (fun x => (∀ i j : Fin n, i ≤ j → x j ≤ x i) ∧ (∀ i, z ≤ x i) ∧ ∏ i, x i ≤ Y)

/-- A non-increasing tuple of primes is its product's prime factors in decreasing order. -/
theorem ofFn_eq {n : ℕ} {x : Fin n → ℕ} (hx : Antitone x) (hp : ∀ i, (x i).Prime) :
    List.ofFn x = ((∏ i, x i).primeFactorsList).reverse := by
  have h1 : (List.ofFn x).SortedGE := List.sortedGE_ofFn_iff.2 hx
  have h2 : ((∏ i, x i).primeFactorsList).reverse.SortedGE := (Nat.primeFactorsList_sorted _).reverse
  refine List.Perm.eq_of_sortedGE h1 h2 ?_
  refine (Nat.primeFactorsList_unique (by rw [List.prod_ofFn]) (fun p hp' => ?_)).trans
    (List.reverse_perm _).symm
  rw [List.mem_ofFn] at hp'
  obtain ⟨i, rfl⟩ := hp'
  exact hp i

/-- **Rough numbers as tuples of primes.** For `z ≥ 2` and `Y < z^{K+1}`, a sum over the `k ∈ [2, Y]` with no prime
factor below `z` is the
sum over the non-increasing tuples of at most `K` primes, each at least `z`, of product at most `Y`. -/
theorem sum_rough_eq {z Y : ℕ} (hz : 2 ≤ z) {M : Type*} [AddCommMonoid M] (F : ℕ → M) (K : ℕ)
    (hK : Y < z ^ (K + 1)) :
    ∑ k ∈ (Finset.Icc 2 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k), F k =
      ∑ n ∈ Finset.Icc 1 K, ∑ x ∈ tuples z Y n, F (∏ i, x i) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun k => (⟨(k.primeFactorsList.reverse).length, (k.primeFactorsList.reverse).get⟩ :
      Σ n, Fin n → ℕ)) (fun σ => ∏ i, σ.2 i) ?_ ?_ ?_ ?_ ?_
  · -- into the tuples
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk2, hkY⟩, hrough⟩ := hk
    set l := k.primeFactorsList with hl
    have hk0 : k ≠ 0 := by omega
    have hmem : ∀ p ∈ l.reverse, p.Prime ∧ z ≤ p ∧ p ≤ Y := by
      intro p hp
      rw [List.mem_reverse] at hp
      have hpp := Nat.prime_of_mem_primeFactorsList hp
      refine ⟨hpp, ?_, le_trans (Nat.le_of_mem_primeFactorsList hp) hkY⟩
      by_contra h
      exact hrough p (not_le.1 h) hpp (Nat.dvd_of_mem_primeFactorsList hp)
    have hprod : l.prod = k := Nat.prod_primeFactorsList hk0
    rw [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 1 ≤ l.reverse.length
      rw [List.length_reverse]
      by_contra h
      have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hl, Nat.primeFactorsList_eq_nil] at hnil
      omega
    · show l.reverse.length ≤ K
      rw [List.length_reverse]
      have hpow : z ^ l.length ≤ l.prod := List.pow_length_le_prod l z fun p hp =>
        (hmem p (List.mem_reverse.2 hp)).2.1
      rw [hprod] at hpow
      have : z ^ l.length < z ^ (K + 1) := lt_of_le_of_lt hpow (lt_of_le_of_lt hkY hK)
      have := (Nat.pow_lt_pow_iff_right (by omega)).1 this
      omega
    · show l.reverse.get ∈ tuples z Y l.reverse.length
      rw [tuples, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun t => ?_, fun i j hij => ?_, fun t => (hmem _ (List.get_mem _ _)).2.1, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        have := hmem _ (List.get_mem l.reverse t)
        exact ⟨by omega, this.1⟩
      · exact (Nat.primeFactorsList_sorted k).reverse hij
      · have : ∏ i, l.reverse.get i = k := by
          rw [← List.prod_ofFn, List.ofFn_get, List.prod_reverse, hprod]
        rw [this]
        exact hkY
  · -- back to the rough numbers
    intro σ hσ
    rw [Finset.mem_sigma, Finset.mem_Icc] at hσ
    obtain ⟨⟨hn1, -⟩, hx⟩ := hσ
    rw [tuples, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hbox, -, hz', hY⟩ := hx
    have hpr : ∀ i, (σ.2 i).Prime := fun i => (Finset.mem_filter.1 (hbox i)).2
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, hY⟩, fun p hpz hp hpd => ?_⟩
    · have h0 : σ.2 ⟨0, by omega⟩ ∣ ∏ i, σ.2 i := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      have hpos : 0 < ∏ i, σ.2 i := Finset.prod_pos fun i _ => (hpr i).pos
      exact le_trans (hpr _).two_le (Nat.le_of_dvd hpos h0)
    · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hpd
      rw [(Nat.prime_dvd_prime_iff_eq hp (hpr i)).1 hi] at hpz
      exact absurd (hz' i) (not_le.2 hpz)
  · -- the product of the factors
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    show ∏ i, (k.primeFactorsList.reverse).get i = k
    rw [← List.prod_ofFn, List.ofFn_get, List.prod_reverse, Nat.prod_primeFactorsList (by omega)]
  · -- the factors of the product
    intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨-, hx⟩ := hσ
    rw [tuples, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hbox, hanti, -, -⟩ := hx
    have hpr : ∀ i, (σ.2 i).Prime := fun i => (Finset.mem_filter.1 (hbox i)).2
    have h := ofFn_eq (x := σ.2) (fun i j hij => hanti i j hij) hpr
    have h2 : List.ofFn ((∏ i, σ.2 i).primeFactorsList.reverse.get) = List.ofFn σ.2 := by
      rw [List.ofFn_get, h]
    exact List.ofFn_inj'.1 h2
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    show F k = F (∏ i, (k.primeFactorsList.reverse).get i)
    rw [← List.prod_ofFn, List.ofFn_get, List.prod_reverse, Nat.prod_primeFactorsList (by omega)]

end SieveRoughTuple
