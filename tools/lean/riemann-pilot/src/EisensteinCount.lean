import EisensteinSymbol

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
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Eis

/-- The ideals of norm `n` (finitely many for `n ≥ 1`). -/
noncomputable def ofNorm (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset

theorem mem_ofNorm {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ ofNorm n ↔ absNorm I = n := by
  simp [ofNorm]

/-- `m(n) = Σ_{N𝔞 = n} μ(𝔞)`. -/
noncomputable def mI (n : ℕ) : ℤ := ∑ I ∈ ofNorm n, moebius I

/-- The norm of `a·𝓞 K` is a power of `a`. -/
theorem absNorm_natCast_span (a : ℕ) :
    absNorm (span {(a : 𝓞 K)}) = a ^ Module.finrank ℤ (𝓞 K) := by
  have h := Ideal.absNorm_algebraMap (R := ℤ) (S := 𝓞 K) (I := span {(a : ℤ)})
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at h
  rw [h, Ideal.absNorm_span_singleton]
  simp

theorem natCast_span_le (I : Ideal (𝓞 K)) : span {((absNorm I : ℕ) : 𝓞 K)} ≤ I :=
  Ideal.span_singleton_absNorm_le I

/-- Coprime rational integers generate coprime ideals. -/
theorem span_sup_span_eq_top {a b : ℕ} (hab : a.Coprime b) :
    span {(a : 𝓞 K)} ⊔ span {(b : 𝓞 K)} = ⊤ := by
  rw [eq_top_iff_one]
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, x * a + y * b = 1 := by
    have := Nat.gcd_eq_gcd_ab a b
    rw [hab.gcd_eq_one] at this
    exact ⟨a.gcdA b, a.gcdB b, by rw [mul_comm _ (a : ℤ), mul_comm _ (b : ℤ)]; exact_mod_cast this.symm⟩
  have : (1 : 𝓞 K) = (x : 𝓞 K) * a + (y : 𝓞 K) * b := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hxy.symm
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

section Mult

variable {a b : ℕ}

theorem mul_sup_span_eq {J L : Ideal (𝓞 K)} (hab : a.Coprime b) (hJ : absNorm J = a)
    (hL : absNorm L = b) : J * L ⊔ span {(a : 𝓞 K)} = J := by
  have haJ : span {(a : 𝓞 K)} ≤ J := hJ ▸ natCast_span_le J
  have hbL : span {(b : 𝓞 K)} ≤ L := hL ▸ natCast_span_le L
  have hLa : L ⊔ span {(a : 𝓞 K)} = ⊤ := by
    rw [eq_top_iff, ← span_sup_span_eq_top hab.symm]
    exact sup_le_sup_right hbL _
  apply le_antisymm (sup_le Ideal.mul_le_left haJ)
  calc J = J * ⊤ := (Ideal.mul_top J).symm
    _ = J * (L ⊔ span {(a : 𝓞 K)}) := by rw [hLa]
    _ = J * L ⊔ J * span {(a : 𝓞 K)} := Ideal.mul_sup J L _
    _ ≤ J * L ⊔ span {(a : 𝓞 K)} := sup_le_sup_left Ideal.mul_le_right _

theorem isRelPrime_of_norm {J L : Ideal (𝓞 K)} (hab : a.Coprime b) (hJ : absNorm J = a)
    (hL : absNorm L = b) : IsRelPrime J L := by
  apply IsCoprime.isRelPrime
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_sup_span_eq_top hab]
  exact sup_le_sup (hJ ▸ natCast_span_le J) (hL ▸ natCast_span_le L)

theorem norm_sup_span_dvd {I : Ideal (𝓞 K)} (hab : a.Coprime b) (hI : absNorm I = a * b) :
    absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a := by
  have h1 : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a * b := hI ▸ absNorm_dvd_absNorm_of_le le_sup_left
  have h2 : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a ^ Module.finrank ℤ (𝓞 K) :=
    absNorm_natCast_span a ▸ absNorm_dvd_absNorm_of_le le_sup_right
  have hc : (absNorm (I ⊔ span {(a : 𝓞 K)})).Coprime b :=
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left _ hab)
  exact hc.dvd_of_dvd_mul_right h1

theorem sup_mul_sup_eq {I : Ideal (𝓞 K)} (hab : a.Coprime b) (hI : absNorm I = a * b) :
    (I ⊔ span {(a : 𝓞 K)}) * (I ⊔ span {(b : 𝓞 K)}) = I := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hI]
    exact natCast_span_le I
  · calc I = I * ⊤ := (Ideal.mul_top I).symm
      _ = I * (span {(a : 𝓞 K)} ⊔ span {(b : 𝓞 K)}) := by rw [span_sup_span_eq_top hab]
      _ = I * span {(a : 𝓞 K)} ⊔ I * span {(b : 𝓞 K)} := Ideal.mul_sup _ _ _
      _ ≤ _ := sup_le
          (by rw [mul_comm]; exact Ideal.mul_mono le_sup_right le_sup_left)
          (Ideal.mul_mono le_sup_left le_sup_right)

theorem ofNorm_mul (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    ofNorm (a * b) = (ofNorm a ×ˢ ofNorm b).image fun p => p.1 * p.2 := by
  ext I
  simp only [mem_ofNorm, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · intro hI
    set J := I ⊔ span {(a : 𝓞 K)}
    set L := I ⊔ span {(b : 𝓞 K)}
    have hJL : J * L = I := sup_mul_sup_eq hab hI
    have hJ : absNorm J ∣ a := norm_sup_span_dvd hab hI
    have hL : absNorm L ∣ b := by
      have := norm_sup_span_dvd hab.symm (I := I) (by rw [hI, mul_comm])
      exact this
    have hprod : absNorm J * absNorm L = a * b := by rw [← map_mul, hJL, hI]
    obtain ⟨x, hx⟩ := hJ
    obtain ⟨y, hy⟩ := hL
    have hJ0 : absNorm J ≠ 0 := by rintro h; rw [h, zero_mul] at hx; omega
    have hL0 : absNorm L ≠ 0 := by rintro h; rw [h, zero_mul] at hy; omega
    have hxy : x * y = 1 := by
      have : absNorm J * absNorm L * (x * y) = absNorm J * absNorm L * 1 := by
        calc absNorm J * absNorm L * (x * y) = (absNorm J * x) * (absNorm L * y) := by ring
          _ = a * b := by rw [← hx, ← hy]
          _ = absNorm J * absNorm L * 1 := by rw [mul_one, hprod]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero hJ0 hL0)) this
    have hx1 : x = 1 := Nat.eq_one_of_mul_eq_one_right hxy
    have hy1 : y = 1 := Nat.eq_one_of_mul_eq_one_left hxy
    exact ⟨J, L, ⟨by rw [hx, hx1, mul_one], by rw [hy, hy1, mul_one]⟩, hJL⟩
  · rintro ⟨J, L, ⟨hJ, hL⟩, rfl⟩
    rw [map_mul, hJ, hL]

theorem injOn_mul (hab : a.Coprime b) :
    Set.InjOn (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2) ↑(ofNorm a ×ˢ ofNorm b) := by
  rintro ⟨J, L⟩ h ⟨J', L'⟩ h' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_ofNorm] at h h'
  simp only at heq
  have e1 : J = J' := by
    rw [← mul_sup_span_eq hab h.1 h.2, ← mul_sup_span_eq hab h'.1 h'.2, heq]
  have e2 : L = L' := by
    rw [← mul_sup_span_eq hab.symm h.2 h.1, ← mul_sup_span_eq hab.symm h'.2 h'.1,
      mul_comm L, mul_comm L', heq]
  rw [e1, e2]

/-- **`m(n) = Σ_{N𝔞=n} μ(𝔞)` is multiplicative.** -/
theorem mI_mul (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) : mI (a * b) = mI a * mI b := by
  rw [mI, ofNorm_mul hab ha hb, Finset.sum_image (injOn_mul hab), mI, mI, Finset.sum_mul_sum,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun J hJ => Finset.sum_congr rfl fun L hL => ?_
  exact (isRelPrime_of_norm hab (mem_ofNorm.1 hJ) (mem_ofNorm.1 hL)).moebius_mul

end Mult

section PrimePowers

theorem finrank_O : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank (k := 3) K]
  rfl

theorem absNorm_natCast_span_sq (a : ℕ) : absNorm (span {(a : 𝓞 K)}) = a ^ 2 := by
  rw [absNorm_natCast_span, finrank_O]

/-- The prime factors of `p·𝓞 K`. -/
noncomputable def pFactors (p : ℕ) : Multiset (Ideal (𝓞 K)) :=
  normalizedFactors (span {(p : 𝓞 K)})

theorem span_natCast_ne_bot {p : ℕ} (hp : p ≠ 0) : span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp

theorem mem_pFactors {p : ℕ} (hp : p ≠ 0) {P : Ideal (𝓞 K)} :
    P ∈ pFactors p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  rw [pFactors, Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hp), Ideal.span_singleton_le_iff_mem]

theorem prod_pFactors {p : ℕ} (hp : p ≠ 0) : (pFactors p).prod = span {(p : 𝓞 K)} :=
  Ideal.prod_normalizedFactors_eq_self (span_natCast_ne_bot hp)

/-- The norms of the prime factors of `p·𝓞 K` multiply to `p²`. -/
theorem prod_norm_pFactors {p : ℕ} (hp : p ≠ 0) : ((pFactors p).map absNorm).prod = p ^ 2 := by
  rw [← map_multiset_prod, prod_pFactors hp, absNorm_natCast_span_sq]

/-- A prime factor of `p·𝓞 K` has norm `p` or `p²`. -/
theorem norm_of_mem_pFactors {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    absNorm P = p ∨ absNorm P = p ^ 2 := by
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.ne_zero).1 hP
  have hd : absNorm P ∣ p ^ 2 := by
    rw [← absNorm_natCast_span_sq]
    exact absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  rcases (Nat.dvd_prime_pow hp).1 hd with ⟨i, hi, he⟩
  interval_cases i
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using he)) hPp.ne_top
  · left; simpa using he
  · right; exact he

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
      (Multiset.card (pFactors p) = 2 ∧ ∀ P ∈ pFactors p, absNorm P = p) := by
  have hp2 := hp.two_le
  have hprod := prod_norm_pFactors hp.ne_zero
  by_cases hbig : ∃ P ∈ pFactors p, absNorm P = p ^ 2
  · obtain ⟨P, hP, hPn⟩ := hbig
    left
    refine ⟨P, ?_, hPn⟩
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hP
    rw [ht, Multiset.map_cons, Multiset.prod_cons, hPn] at hprod
    have h1 : (t.map absNorm).prod = 1 := by
      have hp0 : 0 < p ^ 2 := by positivity
      nlinarith [Nat.eq_of_mul_eq_mul_left hp0 (hprod.trans (mul_one _).symm)]
    have ht0 : t = 0 := by
      by_contra hne
      obtain ⟨Q, hQ⟩ := Multiset.exists_mem_of_ne_zero hne
      have hQf : Q ∈ pFactors p := by rw [ht]; exact Multiset.mem_cons_of_mem hQ
      have hQ1 : absNorm Q ∣ 1 := h1 ▸ Multiset.dvd_prod (Multiset.mem_map_of_mem _ hQ)
      rcases norm_of_mem_pFactors hp hQf with h | h <;> rw [h] at hQ1
      · exact absurd (Nat.eq_one_of_dvd_one hQ1) hp.one_lt.ne'
      · have := Nat.eq_one_of_dvd_one hQ1; nlinarith
    rw [ht, ht0]; rfl
  · right
    push Not at hbig
    have hall : ∀ P ∈ pFactors p, absNorm P = p := fun P hP =>
      (norm_of_mem_pFactors hp hP).resolve_right (hbig P hP)
    refine ⟨?_, hall⟩
    have hrep : (pFactors p).map absNorm = Multiset.replicate (Multiset.card (pFactors p)) p := by
      rw [Multiset.eq_replicate]
      exact ⟨Multiset.card_map _ _, fun b hb => by
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hb; exact hall P hP⟩
    rw [hrep, Multiset.prod_replicate] at hprod
    exact Nat.pow_right_injective hp2 hprod

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
    (hP : P ∈ normalizedFactors I) : P ∈ pFactors p := by
  have hI0 : I ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.symm
  obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
  refine (mem_pFactors hp.ne_zero).2 ⟨hPp, ?_⟩
  have hk : ((p ^ k : ℕ) : 𝓞 K) ∈ P := hIP (hI ▸ natCast_span_le I (Ideal.mem_span_singleton_self _))
  push_cast at hk
  exact hPp.mem_of_pow_mem k hk

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
