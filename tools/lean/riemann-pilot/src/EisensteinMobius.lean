import EisensteinCount
import HalfPlaneS0

/-! # S1, part 2b: the splitting law in `ℤ[ω]` and `Σ_{N𝔞=n} μ(𝔞) = μ_K(n)` (round 284)

Round 283 proved that `m(n) = Σ_{N𝔞=n} μ(𝔞)` is multiplicative and, at prime powers, a signed count
of sets of prime factors of `p𝓞`. This file decides the splitting type of every rational prime and
concludes **`mI_eq_muK`**: `m(n) = μ_K(n)`, the coefficients of `1/(ζ(s)L(s, χ₋₃))` used by round 278's
S0. So sums over the ideals of `ℤ[ω]` (the family of round 282) and S0's `μ_K` are the same objects.

* **Counting** (`card_quot_le_of_ω_mem`): if `ω ≡ c (mod p𝓞)` for an integer `c`, then
  `|𝓞/p𝓞| ≤ p`, since every element is an integer polynomial in `ω` (`exists_eq_aeval_ω`). But
  `|𝓞/p𝓞| = p²` (`card_quot_natCast`).
* **Inert** (`inert_of_mod_two`): for `p ≡ 2 (mod 3)`, `p𝓞` is prime. A prime factor of norm `p`
  would contain `p` and have a residue field of `p` elements holding the primitive cube root of unity
  `ω mod P`, forcing `3 ∣ p − 1` (`three_dvd_of_norm_eq`).
* **Split** (`split_of_mod_one`): for `p ≡ 1 (mod 3)`, `p𝓞 = PQ` with `P ≠ Q` of norm `p`. Cauchy's
  theorem in `(ℤ/p)ˣ` gives `p ∣ a² + a + 1` (`exists_cube_root_mod`), so
  `(ω − a)(ω − a²) ∈ p𝓞` (`prod_sub_mem`) while neither factor is (the counting bound). That excludes
  `p𝓞` prime, and `p𝓞 = P²` too: the roots `a`, `a²` differ by the unit `a(1 − a)` mod `p`, so one
  factor is invertible mod `P` and the other would lie in `P² = p𝓞`.
* **Ramified** (`ramified_three`): `3𝓞 = (ω − 1)²`, with `N(ω − 1) = 3`.
* **Closed forms**: `m(p^k)` and `μ_K(p^k)` are both `1, −(1 + χ₋₃(p)), χ₋₃(p), 0, 0, …`
  (`mI_prime_pow_eq`, `muK_prime_pow`, via `signed_count` and the convolution `μ ⍟ χ₋₃μ`), and `μ_K`
  is multiplicative (`muK_mul`). Induction over coprime factorisations gives `mI_eq_muK`.
-/

open NumberField Ideal UniqueFactorizationMonoid Polynomial

namespace Eis

/-- Every element of `ℤ[ω]` is an integer polynomial in `ω`. -/
theorem exists_eq_aeval_ω (x : 𝓞 K) : ∃ f : ℤ[X], x = aeval ω f := by
  obtain ⟨f, hf⟩ := hζ.integralPowerBasis.exists_eq_aeval' x
  exact ⟨f, by rw [hf, IsPrimitiveRoot.integralPowerBasis_gen]; rfl⟩

theorem card_quot_natCast (p : ℕ) : Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [← absNorm_natCast_span_sq p, absNorm_apply, Submodule.cardQuot_apply]

/-- If `ω ≡ c (mod p)` for an integer `c`, then `𝓞/p𝓞` has at most `p` elements. -/
theorem card_quot_le_of_ω_mem {p : ℕ} (hp : p ≠ 0) {c : ℤ} (hc : ω - c ∈ span {(p : 𝓞 K)}) :
    Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)}) ≤ p := by
  set I := span {(p : 𝓞 K)}
  have hωc : Ideal.Quotient.mk I ω = Ideal.Quotient.mk I (c : 𝓞 K) := Ideal.Quotient.eq.2 hc
  have hint : ∀ m : ℤ, Ideal.Quotient.mk I (m : 𝓞 K) =
      Ideal.Quotient.mk I (((m % p).toNat : ℕ) : 𝓞 K) := by
    intro m
    rw [Ideal.Quotient.eq]
    have hnn : 0 ≤ m % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp)
    have e : (((m % p).toNat : ℕ) : ℤ) = m % p := Int.toNat_of_nonneg hnn
    have e2 : (p : ℤ) * (m / p) + m % p = m := Int.mul_ediv_add_emod m p
    have : (m : 𝓞 K) - (((m % p).toNat : ℕ) : 𝓞 K) = (p : 𝓞 K) * ((m / p : ℤ) : 𝓞 K) := by
      have h3 : ((((m % p).toNat : ℕ) : ℤ) : 𝓞 K) = ((m % p : ℤ) : 𝓞 K) := by rw [e]
      have h4 : (m : 𝓞 K) = (p : 𝓞 K) * ((m / p : ℤ) : 𝓞 K) + ((m % p : ℤ) : 𝓞 K) := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) e2.symm
      rw [h4, ← h3]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hlt : ∀ m : ℤ, (m % p).toNat < p := by
    intro m
    have := Int.emod_lt_of_pos m (by exact_mod_cast Nat.pos_of_ne_zero hp : (0 : ℤ) < p)
    omega
  have hsurj : Function.Surjective fun m : Fin p => Ideal.Quotient.mk I ((m : ℕ) : 𝓞 K) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨f, rfl⟩ := exists_eq_aeval_ω x
    have h1 : Ideal.Quotient.mk I (aeval ω f) = Ideal.Quotient.mk I ((f.eval c : ℤ) : 𝓞 K) := by
      calc Ideal.Quotient.mk I (aeval ω f)
          = aeval (Ideal.Quotient.mk I ω) f :=
            (Polynomial.aeval_algHom_apply (Ideal.Quotient.mk I).toIntAlgHom ω f).symm
        _ = aeval (Ideal.Quotient.mk I (c : 𝓞 K)) f := by rw [hωc]
        _ = Ideal.Quotient.mk I (aeval (c : 𝓞 K) f) :=
            Polynomial.aeval_algHom_apply (Ideal.Quotient.mk I).toIntAlgHom _ f
        _ = Ideal.Quotient.mk I ((f.eval c : ℤ) : 𝓞 K) := by
            congr 1
            rw [Polynomial.aeval_def, Polynomial.eval₂_at_intCast]; rfl
    exact ⟨⟨(f.eval c % p).toNat, hlt _⟩, by rw [h1, hint]⟩
  have : Fintype (𝓞 K ⧸ I) :=
    @Fintype.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot I (span_natCast_ne_bot hp))
  rw [Nat.card_eq_fintype_card]
  simpa using Fintype.card_le_of_surjective _ hsurj

section Splitting

theorem three_mem_of_lam_mem {P : Ideal (𝓞 K)} (h : ω - 1 ∈ P) : (3 : 𝓞 K) ∈ P := by
  have h2 : (ω - 1) ^ 2 ∈ P := P.pow_mem_of_mem h 2 (by norm_num)
  rw [lam_sq] at h2
  have : (3 : 𝓞 K) = -(-3 * ω) * ω ^ 2 := by linear_combination (-3 : 𝓞 K) * ω_cube
  rw [this]; exact P.mul_mem_right _ (P.neg_mem_iff.2 h2)

/-- Coprime rational integers in a proper ideal: impossible. -/
theorem not_coprime_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {a b : ℕ} (hab : a.Coprime b)
    (ha : (a : 𝓞 K) ∈ P) (hb : (b : 𝓞 K) ∈ P) : False := by
  apply hP
  rw [eq_top_iff, ← span_sup_span_eq_top hab]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ha) ((Ideal.span_singleton_le_iff_mem _).2 hb)

/-- **A prime factor of `p𝓞` of norm `p`, with `p ≠ 3`, forces `p ≡ 1 (mod 3)`**: its residue field
contains the primitive cube root of unity `ω mod P`. -/
theorem three_dvd_of_norm_eq {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {P : Ideal (𝓞 K)}
    (hP : P ∈ pFactors p) (hN : absNorm P = p) : 3 ∣ p - 1 := by
  classical
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.ne_zero).1 hP
  have hPb : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP; exact hp.ne_zero (by exact_mod_cast hpP)
  have : P.IsMaximal := hPp.isMaximal hPb
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← hN, absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  set e := Ideal.Quotient.mk P ω with he
  have he3 : e ^ 3 = 1 := mk_ω_cube P
  have he1 : e ≠ 1 := by
    intro h
    have hlam : ω - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← he, h, sub_self]
    exact not_coprime_mem hPp.ne_top ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
      hpP (by exact_mod_cast three_mem_of_lam_mem hlam)
  have he0 : e ≠ 0 := fun h => by rw [h, zero_pow (by norm_num)] at he3; exact zero_ne_one he3
  set u := Units.mk0 e he0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, he3])
  have hu1 : u ≠ 1 := fun h => he1 (by simpa [u] using congrArg Units.val h)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have := orderOf_dvd_card (x := u)
  rwa [hord, Fintype.card_units, hcard] at this


/-- For `p ≡ 1 (mod 3)` there is an integer `a` with `p ∣ a² + a + 1` (Cauchy's theorem in `(ℤ/p)ˣ`). -/
theorem exists_cube_root_mod {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 + a + 1 := by
  have := Fact.mk hp
  have h3 : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by intro h; rw [h, orderOf_one] at hg; norm_num at hg
  set x : ZMod p := (g : ZMod p)
  have hx3 : x ^ 3 = 1 := by simp [x, ← Units.val_pow_eq_pow_val, hg3]
  have hx1 : x ≠ 1 := fun h => hg1 (Units.ext h)
  have hx : x ^ 2 + x + 1 = 0 := by
    have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hx1)
  refine ⟨(x.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]; exact hx

/-- The integer analogue of `not_coprime_mem`. -/
theorem not_isCoprime_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {m n : ℤ} (hmn : IsCoprime m n)
    (hm : (m : 𝓞 K) ∈ P) (hn : (n : 𝓞 K) ∈ P) : False := by
  obtain ⟨x, y, hxy⟩ := hmn
  apply hP
  rw [eq_top_iff_one]
  have : (1 : 𝓞 K) = (x : 𝓞 K) * m + (y : 𝓞 K) * n := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hxy.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hn)

/-- `(ω − a)(ω − a²) ∈ p𝓞` when `p ∣ a² + a + 1`. -/
theorem prod_sub_mem {p : ℕ} {a t : ℤ} (ht : a ^ 2 + a + 1 = p * t) :
    (ω - a) * (ω - (a ^ 2 : ℤ)) ∈ span {(p : 𝓞 K)} := by
  have ht' : (a : 𝓞 K) ^ 2 + a + 1 = (p : 𝓞 K) * t := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) ht
  have : (ω - a) * (ω - (a ^ 2 : ℤ)) = (p : 𝓞 K) * ((t : 𝓞 K) * (a - 1 - ω)) := by
    push_cast
    linear_combination ω_sq_add + ((a : 𝓞 K) - 1 - ω) * ht'
  rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **Split**: for `p ≡ 1 (mod 3)`, `p𝓞` is the product of two distinct primes of norm `p`. -/
theorem split_of_mod_one {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ P Q : Ideal (𝓞 K), P ≠ Q ∧ pFactors p = {P, Q} ∧ absNorm P = p ∧ absNorm Q = p := by
  classical
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at h1
  have hp0 := hp.ne_zero
  have hcard := card_quot_natCast p
  have hp2 := hp.two_le
  obtain ⟨a, t, ht⟩ := exists_cube_root_mod hp h1
  have hmem := prod_sub_mem (a := a) (t := t) (p := p) ht
  -- no prime `P` contains `ω − a` or `ω − a²` together with `p𝓞 ≤ P²`-type collapse:
  have hnot : ∀ c : ℤ, ω - (c : 𝓞 K) ∉ span {(p : 𝓞 K)} := fun c hc => by
    have := card_quot_le_of_ω_mem hp0 hc
    rw [hcard] at this; nlinarith
  rcases pFactors_cases hp with ⟨P, hPf, -⟩ | ⟨hc2, hall⟩
  · -- inert: `p𝓞 = P` would be prime
    exfalso
    have hspan : span {(p : 𝓞 K)} = P := by rw [← prod_pFactors hp0, hPf, Multiset.prod_singleton]
    have hPp : P.IsPrime := ((mem_pFactors hp0).1 (by rw [hPf]; exact Multiset.mem_singleton_self P)).1
    rw [hspan] at hmem hnot
    rcases hPp.mem_or_mem hmem with h | h
    · exact hnot a h
    · exact hnot (a ^ 2) h
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc2
    have hPf : P ∈ pFactors p := by rw [hPQ]; simp
    have hQf : Q ∈ pFactors p := by rw [hPQ]; simp
    refine ⟨P, Q, ?_, hPQ, hall P hPf, hall Q hQf⟩
    -- ramified: `p𝓞 = P²` is impossible
    rintro rfl
    have hspan : span {(p : 𝓞 K)} = P * P := by
      rw [← prod_pFactors hp0, hPQ]; simp
    obtain ⟨hPp, hpP⟩ := (mem_pFactors hp0).1 hPf
    have hPb : P ≠ ⊥ := fun h => by
      rw [h, Ideal.mem_bot] at hpP; exact hp0 (by exact_mod_cast hpP)
    have hPm : P.IsMaximal := hPp.isMaximal hPb
    have hmemP : (ω - a) * (ω - (a ^ 2 : ℤ)) ∈ P := by
      rw [hspan] at hmem; exact Ideal.mul_le_left hmem
    -- the two roots differ by a unit modulo `P`
    have hpa : ¬ (p : ℤ) ∣ a * (1 - a) := by
      intro hd
      rcases (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd hd with h | h
      · have : (p : ℤ) ∣ 1 := by
          have := dvd_sub (Dvd.intro t ht.symm) (dvd_mul_of_dvd_left h (a + 1))
          ring_nf at this ⊢; simpa using this
        exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
      · have : (p : ℤ) ∣ 3 := by
          have := dvd_sub (Dvd.intro t ht.symm) (dvd_mul_of_dvd_left h (-(a + 2)))
          ring_nf at this ⊢; simpa using this
        have h3 : p ∣ 3 := by exact_mod_cast this
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
    have hcop : IsCoprime (a * (1 - a)) (p : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.2 hpa).symm
    -- one root lies in `P`, the other does not
    have key : ∀ b b' : ℤ, ω - (b : 𝓞 K) ∈ P → (b : 𝓞 K) - b' = (a * (1 - a) : ℤ) ∨ (b : 𝓞 K) - b' = -(a * (1 - a) : ℤ) →
        (ω - b) * (ω - b') ∈ P * P → False := by
      intro b b' hb hdiff hprod
      have hb' : ω - (b' : 𝓞 K) ∉ P := by
        intro hb'
        have hd : (b : 𝓞 K) - b' ∈ P := by
          have := P.sub_mem hb' hb; ring_nf at this ⊢; simpa [sub_eq_add_neg, add_comm] using this
        rcases hdiff with e | e <;> rw [e] at hd
        · exact not_isCoprime_mem hPp.ne_top hcop hd (by exact_mod_cast hpP)
        · exact not_isCoprime_mem hPp.ne_top hcop (P.neg_mem_iff.1 hd) (by exact_mod_cast hpP)
      -- invert `ω − b'` modulo `P`
      let := Ideal.Quotient.field P
      have hne : Ideal.Quotient.mk P (ω - b') ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P (ω - b'))⁻¹
      have hq : (ω - b') * y - 1 ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, mul_inv_cancel₀ hne, map_one, sub_self]
      have hsq : ω - (b : 𝓞 K) ∈ P * P := by
        have e : ω - (b : 𝓞 K) = (ω - b) * (ω - b') * y - (ω - b) * ((ω - b') * y - 1) := by ring
        rw [e]
        exact (P * P).sub_mem (Ideal.mul_mem_right _ _ hprod) (Ideal.mul_mem_mul hb hq)
      rw [← hspan] at hsq
      exact hnot b hsq
    have hprodPP : (ω - a) * (ω - (a ^ 2 : ℤ)) ∈ P * P := hspan ▸ hmem
    rcases hPp.mem_or_mem hmemP with h | h
    · exact key a (a ^ 2) h (Or.inl (by push_cast; ring)) hprodPP
    · refine key (a ^ 2) a h (Or.inr (by push_cast; ring)) ?_
      rw [show (ω - ((a ^ 2 : ℤ) : 𝓞 K)) * (ω - (a : 𝓞 K)) = (ω - a) * (ω - ((a ^ 2 : ℤ) : 𝓞 K)) by ring]
      exact hprodPP


/-- **Inert**: for `p ≡ 2 (mod 3)`, `p𝓞` is prime, of norm `p²`. -/
theorem inert_of_mod_two {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) :
    ∃ P, pFactors p = {P} ∧ absNorm P = p ^ 2 := by
  rcases pFactors_cases hp with h | ⟨hc2, hall⟩
  · exact h
  · exfalso
    obtain ⟨P, hP⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hc2]; norm_num)
    have hp3 : p ≠ 3 := by rintro rfl; norm_num at h2
    have := three_dvd_of_norm_eq hp hp3 hP (hall P hP)
    omega

/-- **Ramified**: `3𝓞 = (ω − 1)²`, and `N(ω − 1) = 3`. -/
theorem ramified_three :
    pFactors 3 = {span {ω - 1}, span {ω - 1}} ∧ absNorm (span {ω - 1} : Ideal (𝓞 K)) = 3 := by
  have hΛ : (span {ω - 1} : Ideal (𝓞 K)).IsPrime :=
    IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' 3 hζ
  have hω1 : ω - 1 ≠ 0 := by
    intro h
    have : ω = 1 := sub_eq_zero.1 h
    exact hζ.toInteger_isPrimitiveRoot.ne_one (by norm_num) this
  have hΛ0 : (span {ω - 1} : Ideal (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have h3 : span {((3 : ℕ) : 𝓞 K)} = (span {ω - 1} : Ideal (𝓞 K)) ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    refine ⟨-ωu, ?_⟩
    simp only [Units.val_neg, coe_ωu]
    push_cast
    linear_combination -lam_sq
  have hirr : Irreducible (span {ω - 1} : Ideal (𝓞 K)) :=
    (Ideal.prime_of_isPrime hΛ0 hΛ).irreducible
  refine ⟨?_, ?_⟩
  · rw [pFactors, h3, UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq]
    rfl
  · have h9 := absNorm_natCast_span_sq 3
    rw [h3, map_pow] at h9
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (by simpa using h9)

/-- If every prime factor of `p𝓞` has norm `p^f`, the signed count of `mI_prime_pow` is a
binomial coefficient. -/
theorem signed_count {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, absNorm P = p ^ f) (k : ℕ) :
    (∑ T ∈ S.powerset with ∏ P ∈ T, absNorm P = p ^ k, (-1 : ℤ) ^ T.card) =
      if f ∣ k then (-1) ^ (k / f) * (S.card.choose (k / f) : ℤ) else 0 := by
  classical
  have hnorm : ∀ T ∈ S.powerset, ∏ P ∈ T, absNorm P = p ^ (f * T.card) := by
    intro T hT
    rw [Finset.prod_congr rfl fun P hP => hS P (Finset.mem_powerset.1 hT hP), Finset.prod_const,
      ← pow_mul, mul_comm]
  have hiff : ∀ T ∈ S.powerset, (∏ P ∈ T, absNorm P = p ^ k) ↔ f * T.card = k := by
    intro T hT
    rw [hnorm T hT]
    exact (Nat.pow_right_injective hp.two_le).eq_iff
  rw [Finset.sum_filter, Finset.sum_congr rfl fun T hT => by rw [if_congr (hiff T hT) rfl rfl]]
  rw [← Finset.sum_filter]
  split_ifs with hdvd
  · obtain ⟨j, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ hf]
    have hset : S.powerset.filter (fun T => f * T.card = f * j) = S.powersetCard j := by
      rw [Finset.powersetCard_eq_filter]
      congr 1; ext T; exact (Nat.mul_right_inj hf.ne').trans Iff.rfl
    rw [hset, Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2],
      Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
  · rw [Finset.sum_eq_zero]
    intro T hT
    exact absurd ⟨T.card, (Finset.mem_filter.1 hT).2.symm⟩ hdvd

/-- `χ₋₃(p)` for a prime `p`, as an integer: `1`, `−1` or `0`. -/
def chiInt (p : ℕ) : ℤ := if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1

/-- **`m(p^k)` in closed form**: `1`, `−(1 + χ₋₃(p))`, `χ₋₃(p)`, then `0`. -/
theorem mI_prime_pow_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mI (p ^ k) = if k = 0 then 1 else if k = 1 then -(1 + chiInt p) else
      if k = 2 then chiInt p else 0 := by
  classical
  rw [mI_prime_pow hp]
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · -- `p = 3`, ramified
    have hp3 : p = 3 := by
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
    subst hp3
    obtain ⟨hf, hn⟩ := ramified_three
    rw [hf]
    have hfin : ({span {ω - 1}, span {ω - 1}} : Multiset (Ideal (𝓞 K))).toFinset = {span {ω - 1}} := by
      ext; simp
    rw [hfin, signed_count hp one_pos _ (by simpa using hn) k]
    simp only [Nat.one_dvd, ite_true, Nat.div_one, Finset.card_singleton, chiInt]
    rcases k with _ | _ | k
    · simp
    · simp
    · simp [Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]
  · -- split
    obtain ⟨P, Q, hPQ, hf, hPn, hQn⟩ := split_of_mod_one hp h1
    rw [hf]
    have hfin : ({P, Q} : Multiset (Ideal (𝓞 K))).toFinset = {P, Q} := by ext; simp
    rw [hfin, signed_count hp one_pos {P, Q} (by
      intro R hR; rcases Finset.mem_insert.1 hR with rfl | hR
      · simpa using hPn
      · rw [Finset.mem_singleton.1 hR]; simpa using hQn) k]
    simp only [Nat.one_dvd, ite_true, Nat.div_one, Finset.card_pair hPQ, chiInt, h1]
    rcases k with _ | _ | _ | k <;> simp [Nat.choose_eq_zero_of_lt]
  · -- inert
    obtain ⟨P, hf, hPn⟩ := inert_of_mod_two hp h2
    rw [hf, Multiset.toFinset_singleton, signed_count hp two_pos {P} (by simpa using hPn) k]
    simp only [Finset.card_singleton, chiInt, h2]
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp
    · have h2k : ¬ (k + 3 = 0) := by omega
      simp only [h2k, ite_false, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega]
      split_ifs with hd
      · obtain ⟨j, hj⟩ := hd
        have : 2 ≤ (k + 3) / 2 := by omega
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      · rfl

end Splitting

section MuK

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `χ₋₃(n)` agrees with `chiInt` at every `n`. -/
theorem chi3_eq_chiInt (n : ℕ) : PsiOmega.chi3 n = (chiInt n : ℂ) := by
  rw [PsiOmega.chi3_nat, PsiOmega.χ₃_nat, chiInt]

theorem chiInt_pow (p j : ℕ) : PsiOmega.chi3 ((p ^ j : ℕ) : ZMod 3) = (chiInt p : ℂ) ^ j := by
  rw [Nat.cast_pow, map_pow, chi3_eq_chiInt]

/-- The two convolution factors of `μ_K`, as arithmetic functions. -/
noncomputable def muA : ArithmeticFunction ℂ := toArithmeticFunction fun n => (μ n : ℂ)
noncomputable def muB : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n => PsiOmega.chi3 n * (μ n : ℂ)

theorem muK_eq : HalfPlaneS0.muK = ⇑(muA * muB) := rfl

theorem muA_apply {n : ℕ} (hn : n ≠ 0) : muA n = (μ n : ℂ) := by simp [muA, toArithmeticFunction, hn]
theorem muB_apply {n : ℕ} (hn : n ≠ 0) : muB n = PsiOmega.chi3 n * (μ n : ℂ) := by
  simp [muB, toArithmeticFunction, hn]

theorem muA_mult : muA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [muA, toArithmeticFunction], fun {m n} hm hn hmn => ?_⟩
  rw [muA_apply (mul_ne_zero hm hn), muA_apply hm, muA_apply hn,
    isMultiplicative_moebius.map_mul_of_coprime hmn]; push_cast; ring

theorem muB_mult : muB.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [muB, toArithmeticFunction], fun {m n} hm hn hmn => ?_⟩
  rw [muB_apply (mul_ne_zero hm hn), muB_apply hm, muB_apply hn,
    isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.cast_mul, map_mul]; push_cast; ring

theorem muK_mul {m n : ℕ} (hmn : m.Coprime n) :
    HalfPlaneS0.muK (m * n) = HalfPlaneS0.muK m * HalfPlaneS0.muK n := by
  rw [muK_eq]; exact (muA_mult.mul muB_mult).map_mul_of_coprime hmn

theorem moebius_pp {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (μ (p ^ i) : ℂ) = if i = 0 then 1 else if i = 1 then -1 else 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [moebius_apply_prime_pow hp hi.ne']
    split_ifs <;> simp_all

/-- **`μ_K(p^k)` in closed form.** -/
theorem muK_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    HalfPlaneS0.muK (p ^ k) = if k = 0 then 1 else if k = 1 then -(1 + (chiInt p : ℂ)) else
      if k = 2 then (chiInt p : ℂ) else 0 := by
  rw [muK_eq, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => muA a * muB b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ i ∈ Finset.range (k + 1), muA (p ^ i) * muB (p ^ k / p ^ i) =
      (if i = 0 then 1 else if i = 1 then -1 else 0) *
        ((chiInt p : ℂ) ^ (k - i) * (if k - i = 0 then 1 else if k - i = 1 then -1 else 0)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [Nat.pow_div hik hp.pos, muA_apply (pow_ne_zero _ hp.ne_zero),
      muB_apply (pow_ne_zero _ hp.ne_zero), chiInt_pow, moebius_pp hp, moebius_pp hp]
  rw [Finset.sum_congr rfl hterm]
  rcases k with _ | _ | _ | k
  · simp
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ]
  · rw [Finset.sum_eq_zero]
    · simp
    intro i hi
    have hik : i ≤ k + 3 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    by_cases h0 : i = 0
    · subst h0; simp
    by_cases h1 : i = 1
    · subst h1; simp
    simp [h0, h1]

/-- The ideals of norm `1` and `0`. -/
theorem mI_zero : mI 0 = 0 := by
  classical
  have : ofNorm 0 = {(⊥ : Ideal (𝓞 K))} := by
    ext I; simp [mem_ofNorm, Ideal.absNorm_eq_zero_iff]
  rw [mI, this, Finset.sum_singleton, ← Ideal.zero_eq_bot, moebius_zero]

theorem mI_one : mI 1 = 1 := by
  classical
  have : ofNorm 1 = {(⊤ : Ideal (𝓞 K))} := by
    ext I; simp [mem_ofNorm, Ideal.absNorm_eq_one_iff]
  rw [mI, this, Finset.sum_singleton, ← Ideal.one_eq_top, moebius_one]

/-- **S1 part 2: `Σ_{N𝔞=n} μ(𝔞) = μ_K(n)`.** The ideal Möbius sums of `ℤ[ω]` are the coefficients
of `1/(ζ(s)L(s, χ₋₃))` that S0 uses. -/
theorem mI_eq_muK (n : ℕ) : (mI n : ℂ) = HalfPlaneS0.muK n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [mI_prime_pow_eq hp, muK_prime_pow hp]
    split_ifs <;> simp
  | zero => rw [mI_zero, HalfPlaneS0.muK_zero]; simp
  | one =>
    rw [mI_one]
    have := muK_prime_pow (p := 2) Nat.prime_two 0
    simpa using this.symm
  | coprime a b ha hb hab iha ihb =>
    rw [mI_mul hab (by omega) (by omega), Int.cast_mul, iha, ihb, muK_mul hab]

end MuK

end Eis

#print axioms Eis.exists_eq_aeval_ω
#print axioms Eis.card_quot_natCast
#print axioms Eis.card_quot_le_of_ω_mem
#print axioms Eis.three_dvd_of_norm_eq
#print axioms Eis.exists_cube_root_mod
#print axioms Eis.prod_sub_mem
#print axioms Eis.split_of_mod_one
#print axioms Eis.inert_of_mod_two
#print axioms Eis.ramified_three
#print axioms Eis.signed_count
#print axioms Eis.mI_prime_pow_eq
#print axioms Eis.chi3_eq_chiInt
#print axioms Eis.muK_mul
#print axioms Eis.muK_prime_pow
#print axioms Eis.mI_zero
#print axioms Eis.mI_one
#print axioms Eis.mI_eq_muK
