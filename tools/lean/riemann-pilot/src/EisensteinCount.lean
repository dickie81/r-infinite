import EisensteinSymbol
import QuadIdeals

/-! # S1, part 2a: the ideal Möbius sums `m(n) = Σ_{N𝔞=n} μ(𝔞)` on `ℤ[ω]` (round 283)

`mI n = Σ_{N𝔞 = n} μ(𝔞)` (Mathlib's `UniqueFactorizationMonoid.moebius` on the ideals of `𝓞 ℚ(ζ₃)`,
summed over the finitely many ideals of norm `n`, `ofNorm n`). The target of S1 part 2 is
`mI n = μ_K(n)`, the coefficients of `1/(ζ·L(·, χ₋₃))` used by S0. This file proves the two
structural halves:

* **Multiplicativity** (`mI_mul`): for coprime `a, b ≥ 1`, `I ↦ (I + a·𝓞, I + b·𝓞)` is a bijection
  from the ideals of norm `ab` to pairs of ideals of norms `a` and `b`, with inverse the product
  (`ofNorm_mul`, `injOn_mul`), and `μ` is multiplicative on the coprime pairs (`isRelPrime_of_norm`).
* **Prime powers** (`mI_prime_pow`): `m(p^k) = Σ (−1)^{|T|}` over the sets `T` of prime factors of
  `p·𝓞` with `Π_{P∈T} N(P) = p^k`. Squarefree ideals of norm `p^k` are exactly the products of
  distinct prime factors of `p·𝓞` (`finset_prod_spec`, `mem_pFactors_of_mem`), and
  `μ(Π_{P∈T} P) = (−1)^{|T|}` (`moebius_finset_prod`).
* **The three patterns** (`pFactors_cases`): `p·𝓞` has one prime factor, of norm `p²`, or two
  (with multiplicity) of norm `p`, since `N(p·𝓞) = p²` (`finrank_O`, `prod_norm_pFactors`).

Not yet here: which pattern occurs for each `p` (split for `p ≡ 1`, inert for `p ≡ 2 (mod 3)`,
ramified at `3`), the values of `μ_K(p^k)`, and the assembled identity `mI n = μ_K(n)`.

Round 514 (STRUCTURAL-REVIEW §9.3, U5): round 485's `QuadIdeals` proves the ideals of each norm, their
multiplicativity, the prime factors of `p·𝓞` and their three patterns for every quadratic field, with
round 283's proofs. They are now its instances at `K = ℚ(ζ₃)` (`finrank_K`), and the proofs here are removed
with the three lemmas only they used (`mul_sup_span_eq`, `norm_sup_span_dvd`, `sup_mul_sup_eq`). The ideal
Möbius function `mI` and its lemmas stay: `QuadIdeals` has none.
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Eis

/-- `ℚ(ζ₃)` has degree `2`. -/
theorem finrank_K : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank (k := 3) K]
  rfl

/-- The ideals of norm `n` (finitely many for `n ≥ 1`): `QuadIdeals.ofNorm` for `ℚ(ζ₃)`. -/
noncomputable def ofNorm (n : ℕ) : Finset (Ideal (𝓞 K)) := QuadIdeals.ofNorm n

theorem mem_ofNorm {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ ofNorm n ↔ absNorm I = n := QuadIdeals.mem_ofNorm

/-- `m(n) = Σ_{N𝔞 = n} μ(𝔞)`. -/
noncomputable def mI (n : ℕ) : ℤ := ∑ I ∈ ofNorm n, moebius I

/-- The norm of `a·𝓞 K` is a power of `a`. -/
theorem absNorm_natCast_span (a : ℕ) :
    absNorm (span {(a : 𝓞 K)}) = a ^ Module.finrank ℤ (𝓞 K) := Ideal.absNorm_span_natCast a

theorem natCast_span_le (I : Ideal (𝓞 K)) : span {((absNorm I : ℕ) : 𝓞 K)} ≤ I :=
  QuadIdeals.natCast_span_le I

/-- Coprime rational integers generate coprime ideals. -/
theorem span_sup_span_eq_top {a b : ℕ} (hab : a.Coprime b) :
    span {(a : 𝓞 K)} ⊔ span {(b : 𝓞 K)} = ⊤ :=
  QuadIdeals.span_sup_span_eq_top hab

section Mult

variable {a b : ℕ}

theorem isRelPrime_of_norm {J L : Ideal (𝓞 K)} (hab : a.Coprime b) (hJ : absNorm J = a)
    (hL : absNorm L = b) : IsRelPrime J L := by
  apply IsCoprime.isRelPrime
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_sup_span_eq_top hab]
  exact sup_le_sup (hJ ▸ natCast_span_le J) (hL ▸ natCast_span_le L)

theorem ofNorm_mul (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    ofNorm (a * b) = (ofNorm a ×ˢ ofNorm b).image fun p => p.1 * p.2 :=
  QuadIdeals.ofNorm_mul hab ha hb

theorem injOn_mul (hab : a.Coprime b) :
    Set.InjOn (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2) ↑(ofNorm a ×ˢ ofNorm b) :=
  QuadIdeals.injOn_mul hab

/-- **`m(n) = Σ_{N𝔞=n} μ(𝔞)` is multiplicative.** -/
theorem mI_mul (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) : mI (a * b) = mI a * mI b := by
  rw [mI, ofNorm_mul hab ha hb, Finset.sum_image (injOn_mul hab), mI, mI, Finset.sum_mul_sum,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun J hJ => Finset.sum_congr rfl fun L hL => ?_
  exact (isRelPrime_of_norm hab (mem_ofNorm.1 hJ) (mem_ofNorm.1 hL)).moebius_mul

end Mult

section PrimePowers

theorem finrank_O : Module.finrank ℤ (𝓞 K) = 2 := QuadIdeals.finrank_O finrank_K

theorem absNorm_natCast_span_sq (a : ℕ) : absNorm (span {(a : 𝓞 K)}) = a ^ 2 :=
  QuadIdeals.absNorm_natCast_span_sq finrank_K a

/-- The prime factors of `p·𝓞 K`: `QuadIdeals.pFactors` for `ℚ(ζ₃)`. -/
noncomputable def pFactors (p : ℕ) : Multiset (Ideal (𝓞 K)) := QuadIdeals.pFactors p

theorem span_natCast_ne_bot {p : ℕ} (hp : p ≠ 0) : span {(p : 𝓞 K)} ≠ ⊥ :=
  QuadIdeals.span_natCast_ne_bot hp

theorem mem_pFactors {p : ℕ} (hp : p ≠ 0) {P : Ideal (𝓞 K)} :
    P ∈ pFactors p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := QuadIdeals.mem_pFactors hp

theorem prod_pFactors {p : ℕ} (hp : p ≠ 0) : (pFactors p).prod = span {(p : 𝓞 K)} :=
  QuadIdeals.prod_pFactors hp

/-- The norms of the prime factors of `p·𝓞 K` multiply to `p²`. -/
theorem prod_norm_pFactors {p : ℕ} (hp : p ≠ 0) : ((pFactors p).map absNorm).prod = p ^ 2 :=
  QuadIdeals.prod_norm_pFactors finrank_K hp

/-- A prime factor of `p·𝓞 K` has norm `p` or `p²`. -/
theorem norm_of_mem_pFactors {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    absNorm P = p ∨ absNorm P = p ^ 2 := QuadIdeals.norm_of_mem_pFactors finrank_K hp hP

/-- The Möbius function of a product of distinct nonzero primes. -/
theorem moebius_finset_prod {T : Finset (Ideal (𝓞 K))} (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    moebius (∏ P ∈ T, P) = (-1) ^ T.card := by
  have hprime : ∀ P ∈ T.val, Prime P := fun P hP => Ideal.prime_of_isPrime (hT P hP).2 (hT P hP).1
  have he : (∏ P ∈ T, P) = T.val.prod := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  have hnf : normalizedFactors (∏ P ∈ T, P) = T.val := by
    rw [he]; exact normalizedFactors_prod_of_prime hprime
  have h0 : (∏ P ∈ T, P) ≠ 0 := by
    rw [he]; exact Multiset.prod_ne_zero fun h => (hT ⊥ h).2 rfl
  have hsq : Squarefree (∏ P ∈ T, P) := by
    rw [squarefree_iff_nodup_normalizedFactors h0, hnf]; exact T.nodup
  rw [hsq.moebius_eq, factors_eq_normalizedFactors, hnf, Finset.card_val]

/-- The prime factors of `p·𝓞 K`: one of norm `p²`, or two (with multiplicity) of norm `p`. -/
theorem pFactors_cases {p : ℕ} (hp : p.Prime) :
    (∃ P, pFactors p = {P} ∧ absNorm P = p ^ 2) ∨
      (Multiset.card (pFactors p) = 2 ∧ ∀ P ∈ pFactors p, absNorm P = p) :=
  QuadIdeals.pFactors_cases finrank_K hp

end PrimePowers


/-- A product of distinct nonzero primes is squarefree, with exactly those prime factors. -/
theorem finset_prod_spec {T : Finset (Ideal (𝓞 K))} (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    Squarefree (∏ P ∈ T, P) ∧ normalizedFactors (∏ P ∈ T, P) = T.val := by
  have hprime : ∀ P ∈ T.val, Prime P := fun P hP => Ideal.prime_of_isPrime (hT P hP).2 (hT P hP).1
  have he : (∏ P ∈ T, P) = T.val.prod := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  have hnf : normalizedFactors (∏ P ∈ T, P) = T.val := by
    rw [he]; exact normalizedFactors_prod_of_prime hprime
  have h0 : (∏ P ∈ T, P) ≠ 0 := by
    rw [he]; exact Multiset.prod_ne_zero fun h => (hT ⊥ h).2 rfl
  exact ⟨by rw [squarefree_iff_nodup_normalizedFactors h0, hnf]; exact T.nodup, hnf⟩

/-- The prime factors of an ideal of norm `p^k` divide `p·𝓞 K`. -/
theorem mem_pFactors_of_mem {p k : ℕ} (hp : p.Prime) {I P : Ideal (𝓞 K)} (hI : absNorm I = p ^ k)
    (hP : P ∈ normalizedFactors I) : P ∈ pFactors p :=
  QuadIdeals.mem_pFactors_of_mem hp hI hP

/-- **`m(p^k)` as a signed count of sets of prime factors of `p`.** -/
theorem mI_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mI (p ^ k) = ∑ T ∈ (pFactors p).toFinset.powerset with ∏ P ∈ T, absNorm P = p ^ k,
      (-1 : ℤ) ^ T.card := by
  classical
  have hprimes : ∀ T ∈ (pFactors p).toFinset.powerset, ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := by
    intro T hT P hP
    have hPf : P ∈ pFactors p := Multiset.mem_toFinset.1 (Finset.mem_powerset.1 hT hP)
    refine ⟨((mem_pFactors hp.ne_zero).1 hPf).1, fun h => ?_⟩
    have := ((mem_pFactors hp.ne_zero).1 hPf).2
    rw [h, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  -- the non-squarefree ideals contribute nothing
  rw [mI, ← Finset.sum_filter_add_sum_filter_not (ofNorm (p ^ k)) Squarefree]
  rw [Finset.sum_eq_zero (s := (ofNorm (p ^ k)).filter (fun I => ¬ Squarefree I))
    (fun I hI => moebius_of_not_squarefree (Finset.mem_filter.1 hI).2), add_zero]
  symm
  refine Finset.sum_nbij' (fun T => ∏ P ∈ T, P) (fun I => (normalizedFactors I).toFinset)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter] at hT ⊢
    obtain ⟨hsq, -⟩ := finset_prod_spec (hprimes T hT.1)
    refine ⟨mem_ofNorm.2 ?_, hsq⟩
    rw [map_prod]; exact hT.2
  · intro I hI
    simp only [Finset.mem_filter, mem_ofNorm] at hI ⊢
    refine ⟨Finset.mem_powerset.2 fun P hP => Multiset.mem_toFinset.2
      (mem_pFactors_of_mem hp hI.1 (Multiset.mem_toFinset.1 hP)), ?_⟩
    have hI0 : I ≠ 0 := fun h => by
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.1.symm
    have hnd := (squarefree_iff_nodup_normalizedFactors hI0).1 hI.2
    rw [← map_prod, Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
      hnd.dedup, Ideal.prod_normalizedFactors_eq_self hI0, hI.1]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    rw [(finset_prod_spec (hprimes T hT.1)).2, Finset.val_toFinset]
  · intro I hI
    simp only [Finset.mem_filter, mem_ofNorm] at hI
    have hI0 : I ≠ 0 := fun h => by
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.1.symm
    have hnd := (squarefree_iff_nodup_normalizedFactors hI0).1 hI.2
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
      Ideal.prod_normalizedFactors_eq_self hI0]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    rw [moebius_finset_prod (hprimes T hT.1)]

end Eis

#print axioms Eis.finrank_K
#print axioms Eis.absNorm_natCast_span
#print axioms Eis.span_sup_span_eq_top
#print axioms Eis.ofNorm_mul
#print axioms Eis.injOn_mul
#print axioms Eis.mI_mul
#print axioms Eis.finrank_O
#print axioms Eis.prod_norm_pFactors
#print axioms Eis.norm_of_mem_pFactors
#print axioms Eis.moebius_finset_prod
#print axioms Eis.pFactors_cases
#print axioms Eis.finset_prod_spec
#print axioms Eis.mem_pFactors_of_mem
#print axioms Eis.mI_prime_pow
