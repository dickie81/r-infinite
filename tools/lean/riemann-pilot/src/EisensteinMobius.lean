import EisensteinCount
import HalfPlaneS0

/-! # S1, part 2b: the splitting law in `ℤ[ω]` and `Σ_{N𝔞=n} μ(𝔞) = μ_K(n)` (round 284)

Round 283 proved that `m(n) = Σ_{N𝔞=n} μ(𝔞)` is multiplicative and, at prime powers, a signed count
of sets of prime factors of `p𝓞`. This file decides the splitting type of every rational prime and
concludes **`mI_eq_muK`**: `m(n) = μ_K(n)`, the coefficients of `1/(ζ(s)L(s, χ₋₃))` used by round 278's
S0. So sums over the ideals of `ℤ[ω]` (the family of round 282) and S0's `μ_K` are the same objects.

* **Split and inert, from Mathlib's cyclotomic theory** (round 332; round 284 proved both by hand,
  through a counting bound on `𝓞/p𝓞` and cube roots of unity mod `p`). For `p ≠ 3` every prime
  factor of `p𝓞` has norm `p^{ord₃(p)}` (`absNorm_of_mem_pFactors`, from Mathlib's
  `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`) and multiplicity one
  (`count_pFactors_eq_one`, from `ramificationIdx_eq_of_not_dvd`). So `p ≡ 1 (mod 3)` gives
  `p𝓞 = PQ` with `P ≠ Q` of norm `p` (`split_of_mod_one`), and `p ≡ 2` makes `p𝓞` prime
  (`inert_of_mod_two`).
* **Ramified** (`ramified_three`): `3𝓞 = (ω − 1)²`, with `N(ω − 1) = 3`.
* **Closed forms**: `m(p^k)` and `μ_K(p^k)` are both `1, −(1 + χ₋₃(p)), χ₋₃(p), 0, 0, …`
  (`mI_prime_pow_eq`, `muK_prime_pow`, via `signed_count` and the convolution `μ ⍟ χ₋₃μ`), and `μ_K`
  is multiplicative (`muK_mul`). Induction over coprime factorisations gives `mI_eq_muK`.
* **Inclusion–exclusion and sums over multiples** (round 332): `1_{¬p(i) ∀ i∈S} =
  Σ_{T⊆S} (−1)^{|T|}·1_{p(i) ∀ i∈T}` in any commutative ring (`indicator_forall_not`), and
  `Σ_u 1_{d ∣ u}·g(u) = Σ_ℓ g(dℓ)` in a cancellative monoid with zero (`tsum_ite_dvd_eq`).
  `indicator_coprime`, `indicator_not_dvd`, `indicator_Pr`, `tsum_dvd_eq` and `tsum_ideal_dvd_eq` in
  later files are their instances.
-/

open NumberField Ideal UniqueFactorizationMonoid Polynomial

namespace Eis

/-- Every element of `ℤ[ω]` is an integer polynomial in `ω`. -/
theorem exists_eq_aeval_ω (x : 𝓞 K) : ∃ f : ℤ[X], x = aeval ω f := by
  obtain ⟨f, hf⟩ := hζ.integralPowerBasis.exists_eq_aeval' x
  exact ⟨f, by rw [hf, IsPrimitiveRoot.integralPowerBasis_gen]; rfl⟩

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

/-- A prime factor of `p𝓞` lies over `p`. -/
theorem liesOver_of_mem_pFactors {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have := Fact.mk hp
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.ne_zero).1 hP
  rw [Ideal.liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
  simpa using hpP

/-- **Norms from Mathlib's cyclotomic theory**: for `p ≠ 3`, every prime factor of `p𝓞` has norm
`p^{ord₃(p)}` (`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`, `Ideal.pow_inertiaDeg`). -/
theorem absNorm_of_mem_pFactors {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {P : Ideal (𝓞 K)}
    (hP : P ∈ pFactors p) : absNorm P = p ^ orderOf (p : ZMod 3) := by
  have := Fact.mk hp
  have := liesOver_of_mem_pFactors hp hP
  have : P.IsPrime := ((mem_pFactors hp.ne_zero).1 hP).1
  have hdvd : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  rw [← Ideal.pow_inertiaDeg p P,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 3) p K P hdvd]

/-- `p𝓞` is unramified at every prime factor when `p ≠ 3`. -/
theorem count_pFactors_eq_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {P : Ideal (𝓞 K)}
    (hP : P ∈ pFactors p) : (pFactors p).count P = 1 := by
  have := Fact.mk hp
  have := liesOver_of_mem_pFactors hp hP
  have : P.IsPrime := ((mem_pFactors hp.ne_zero).1 hP).1
  have hdvd : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = span {(p : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  have hne : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap]; exact span_natCast_ne_bot hp.ne_zero
  have h := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(p : ℤ)}) P hne
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (m := 3) p K P hdvd, hmap] at h
  exact h.symm

/-- **Split**: for `p ≡ 1 (mod 3)`, `p𝓞` is the product of two distinct primes of norm `p`. -/
theorem split_of_mod_one {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ P Q : Ideal (𝓞 K), P ≠ Q ∧ pFactors p = {P, Q} ∧ absNorm P = p ∧ absNorm Q = p := by
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at h1
  have hord : orderOf (p : ZMod 3) = 1 := by
    rw [orderOf_eq_one_iff]
    have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
    rw [this, h1]; rfl
  rcases pFactors_cases hp with ⟨P, hPf, hPn⟩ | ⟨hc2, hall⟩
  · exfalso
    have := absNorm_of_mem_pFactors hp hp3 (P := P) (by rw [hPf]; exact Multiset.mem_singleton_self P)
    rw [hPn, hord, pow_one] at this
    have h2 := hp.two_le
    nlinarith
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc2
    have hPf : P ∈ pFactors p := by rw [hPQ]; simp
    have hQf : Q ∈ pFactors p := by rw [hPQ]; simp
    refine ⟨P, Q, fun h => ?_, hPQ, hall P hPf, hall Q hQf⟩
    have := count_pFactors_eq_one hp hp3 hPf
    rw [hPQ, ← h] at this
    simp at this

/-- **Inert**: for `p ≡ 2 (mod 3)`, `p𝓞` is prime, of norm `p²`. -/
theorem inert_of_mod_two {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) :
    ∃ P, pFactors p = {P} ∧ absNorm P = p ^ 2 := by
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at h2
  rcases pFactors_cases hp with h | ⟨hc2, hall⟩
  · exact h
  · exfalso
    obtain ⟨P, hP⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hc2]; norm_num)
    have h1 := absNorm_of_mem_pFactors hp hp3 hP
    rw [hall P hP] at h1
    have hord : orderOf (p : ZMod 3) = 2 := by
      have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
      rw [this, h2]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by decide) (by decide)
    rw [hord] at h1
    have := hp.two_le
    nlinarith

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

section InclusionExclusion

open Classical in
/-- **Inclusion–exclusion** (round 332): in any commutative ring,
`1_{¬p(i) for all i ∈ S} = Σ_{T ⊆ S} (−1)^{|T|}·1_{p(i) for all i ∈ T}`, by expanding
`∏_{i∈S}(1 − 1_{p(i)})` with Mathlib's `Finset.prod_add`. `indicator_not_dvd`, `indicator_Pr` and
`indicator_coprime` are its instances. -/
theorem indicator_forall_not {ι R : Type*} [DecidableEq ι] [CommRing R] (S : Finset ι)
    (p : ι → Prop) :
    (if ∀ i ∈ S, ¬ p i then (1 : R) else 0) =
      ∑ T ∈ S.powerset, (-1 : R) ^ T.card * (if ∀ i ∈ T, p i then 1 else 0) := by
  have h1 : (if ∀ i ∈ S, ¬ p i then (1 : R) else 0) =
      ∏ i ∈ S, ((-1 : R) * (if p i then 1 else 0) + 1) := by
    by_cases h : ∀ i ∈ S, ¬ p i
    · rw [ite_eq_left h]; symm
      exact Finset.prod_eq_one fun i hi => by rw [ite_eq_right (h i hi)]; ring
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i, hi, hd⟩ := h
      symm
      exact Finset.prod_eq_zero hi (by rw [ite_eq_left hd]; ring)
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  by_cases h : ∀ i ∈ T, p i
  · rw [Finset.prod_eq_one fun i hi => ite_eq_left (h i hi), ite_eq_left h]
  · push Not at h
    obtain ⟨i, hi, hd⟩ := h
    rw [Finset.prod_eq_zero hi (ite_eq_right hd), ite_eq_right fun h' => hd (h' i hi)]

end InclusionExclusion

section DivisorSums

open Classical in
/-- **A sum over the multiples of `d`** (round 332): `Σ_u 1_{d ∣ u}·g(u) = Σ_ℓ g(dℓ)` for `d ≠ 0` in a
cancellative monoid with zero. `tsum_dvd_eq` and `tsum_ideal_dvd_eq` are its instances. -/
theorem tsum_ite_dvd_eq {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] (d : M) (hd : d ≠ 0)
    (g : M → ℂ) : ∑' u : M, (if d ∣ u then g u else 0) = ∑' ℓ : M, g (d * ℓ) := by
  have hinj : Function.Injective fun ℓ : M => d * ℓ := fun a b hab => mul_left_cancel₀ hd hab
  have hsupp : Function.support (fun u : M => if d ∣ u then g u else 0) ⊆
      Set.range fun ℓ : M => d * ℓ := by
    intro u hu
    by_contra hr
    apply hu
    show (if d ∣ u then g u else 0) = 0
    rw [ite_eq_right]
    rintro ⟨ℓ, rfl⟩
    exact hr ⟨ℓ, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun ℓ => ?_
  rw [ite_eq_left (dvd_mul_right d ℓ)]

end DivisorSums

end Eis

#print axioms Eis.exists_eq_aeval_ω
#print axioms Eis.liesOver_of_mem_pFactors
#print axioms Eis.absNorm_of_mem_pFactors
#print axioms Eis.count_pFactors_eq_one
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
#print axioms Eis.indicator_forall_not
#print axioms Eis.tsum_ite_dvd_eq
