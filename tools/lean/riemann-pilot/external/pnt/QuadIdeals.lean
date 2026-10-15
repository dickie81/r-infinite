/-
# Round 485: the ideals of a quadratic field of each norm, and its Dedekind zeta function

Imports Mathlib only.

Plain statement. Let `K` be a number field of degree `2`, and `a_K(n)` the number of ideals of `𝓞 K` of norm
`n`. Then `a_K` is multiplicative (`card_ofNorm_mul`). Every prime `p` splits (`p𝓞 = PQ` with `P ≠ Q` of norm
`p`), is inert (`p𝓞` prime, of norm `p²`) or ramifies (`p𝓞 = P²`) (`trichotomy`), and the number of ideals of
norm `p^k` is `k + 1`; `1` or `0` as `k` is even or odd; or `1`, respectively. So if `χ` is multiplicative
with `χ(p^k) = χ(p)^k` and `χ(p) = 1, −1, 0` as `p` splits, is inert or ramifies, then `a_K = χ * 1` (`rA_eq`).
If `a_K = c * 1` with `c(n) = χ(n)` for a Dirichlet character `χ`, then `ζ_K(s) = ζ(s)L(s, χ)` for `Re s > 1`
(`dedekindZeta_eq`), and if moreover `χ ≠ 1`, `L(1, χ)` is the residue of `ζ_K` at `1` in Mathlib's class
number formula (`LFunction_one_eq_residue`): `L(1, χ) = 2πh_K/(w_K√|D_K|)` for imaginary `K`
(`LFunction_one_eq_imag`), and the residue is `4R_K h_K/(w_K√D_K)` for real `K` (`residue_eq_real`).

* Multiplicativity is round 283's `Eis.ofNorm_mul` for `ℚ(ζ₃)`, here for every number field: for coprime
  `a, b ≥ 1`, `I ↦ (I + a𝓞, I + b𝓞)` is a bijection from the ideals of norm `ab` to the pairs of ideals of
  norms `a` and `b`, with inverse the product.
* The three patterns are round 283's `Eis.pFactors_cases` for every quadratic field: the norms of the prime
  factors of `p𝓞` multiply to `p²`.
* The counts at `p^k` are round 287's `Eis.card_ofNorm_split`, `Eis.card_ofNorm_inert` and
  `Eis.card_ofNorm_three`, from the pattern in place of the residue of `p` mod `3`.
* `dedekindZeta_eq`: Mathlib's `LSeries_convolution'`, `LSeries_one_eq_riemannZeta` and
  `DirichletCharacter.LFunction_eq_LSeries`. `LFunction_one_eq_residue`: `(s − 1)ζ(s) → 1`
  (`riemannZeta_residue_one`) and `L(·, χ)` is continuous at `1` (`χ ≠ 1`), against Mathlib's
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
* `regulator_eq_one`: unit rank `0` gives regulator `1`, the determinant of an empty matrix.
-/
import Mathlib

open NumberField Ideal UniqueFactorizationMonoid Filter Topology

namespace QuadIdeals

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ideals of norm `n` -/

/-- The ideals of norm `n` (finitely many for `n ≥ 1`). -/
noncomputable def ofNorm (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset

theorem mem_ofNorm {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ ofNorm n ↔ absNorm I = n := by
  simp [ofNorm]

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
  have : (1 : 𝓞 K) = (x : 𝓞 K) * a + (y : 𝓞 K) * b := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hxy.symm
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

theorem norm_sup_span_dvd {I : Ideal (𝓞 K)} (hab : a.Coprime b) (hI : absNorm I = a * b) :
    absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a := by
  have h1 : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a * b := hI ▸ absNorm_dvd_absNorm_of_le le_sup_left
  have h2 : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a ^ Module.finrank ℤ (𝓞 K) :=
    Ideal.absNorm_span_natCast (S := 𝓞 K) a ▸ absNorm_dvd_absNorm_of_le le_sup_right
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
    ofNorm (K := K) (a * b) = (ofNorm a ×ˢ ofNorm b).image fun p => p.1 * p.2 := by
  ext I
  simp only [mem_ofNorm, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · intro hI
    set J := I ⊔ span {(a : 𝓞 K)}
    set L := I ⊔ span {(b : 𝓞 K)}
    have hJL : J * L = I := sup_mul_sup_eq hab hI
    have hJ : absNorm J ∣ a := norm_sup_span_dvd hab hI
    have hL : absNorm L ∣ b := norm_sup_span_dvd hab.symm (I := I) (by rw [hI, mul_comm])
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
    Set.InjOn (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2)
      ((ofNorm (K := K) a ×ˢ ofNorm (K := K) b : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) :
        Set (Ideal (𝓞 K) × Ideal (𝓞 K))) := by
  rintro ⟨J, L⟩ h ⟨J', L'⟩ h' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_ofNorm] at h h'
  simp only at heq
  have e1 : J = J' := by
    rw [← mul_sup_span_eq hab h.1 h.2, ← mul_sup_span_eq hab h'.1 h'.2, heq]
  have e2 : L = L' := by
    rw [← mul_sup_span_eq hab.symm h.2 h.1, ← mul_sup_span_eq hab.symm h'.2 h'.1,
      mul_comm L, mul_comm L', heq]
  rw [e1, e2]

/-- **The number of ideals of norm `n` is multiplicative.** -/
theorem card_ofNorm_mul (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    (ofNorm (K := K) (a * b)).card = (ofNorm (K := K) a).card * (ofNorm (K := K) b).card := by
  rw [ofNorm_mul hab ha hb, Finset.card_image_of_injOn (injOn_mul hab), Finset.card_product]

theorem card_ofNorm_one : (ofNorm (K := K) 1).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨⊤, ?_⟩
  ext I
  rw [mem_ofNorm, Finset.mem_singleton, Ideal.absNorm_eq_one_iff]

end Mult

/-! ### The prime factors of `p𝓞` in a quadratic field -/

section PrimePowers

variable (hK : Module.finrank ℚ K = 2)
include hK

theorem finrank_O : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, hK]

theorem absNorm_natCast_span_sq (a : ℕ) : absNorm (span {(a : 𝓞 K)}) = a ^ 2 := by
  rw [Ideal.absNorm_span_natCast, finrank_O hK]

omit hK

/-- The prime factors of `p𝓞 K`. -/
noncomputable def pFactors (p : ℕ) : Multiset (Ideal (𝓞 K)) :=
  normalizedFactors (span {(p : 𝓞 K)})

theorem span_natCast_ne_bot {p : ℕ} (hp : p ≠ 0) : span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp

theorem mem_pFactors {p : ℕ} (hp : p ≠ 0) {P : Ideal (𝓞 K)} :
    P ∈ pFactors p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  rw [pFactors, Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hp),
    Ideal.span_singleton_le_iff_mem]

theorem pFactors_prime {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    P.IsPrime ∧ P ≠ ⊥ := by
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.ne_zero).1 hP
  refine ⟨hPp, fun h => ?_⟩
  rw [h, Ideal.mem_bot] at hpP
  exact hp.ne_zero (by exact_mod_cast hpP)

theorem prod_pFactors {p : ℕ} (hp : p ≠ 0) : (pFactors p).prod = span {(p : 𝓞 K)} :=
  Ideal.prod_normalizedFactors_eq_self (span_natCast_ne_bot hp)

include hK

/-- The norms of the prime factors of `p𝓞 K` multiply to `p²`. -/
theorem prod_norm_pFactors {p : ℕ} (hp : p ≠ 0) : ((pFactors (K := K) p).map absNorm).prod = p ^ 2 := by
  rw [← map_multiset_prod, prod_pFactors hp, absNorm_natCast_span_sq hK]

/-- A prime factor of `p𝓞 K` has norm `p` or `p²`. -/
theorem norm_of_mem_pFactors {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    absNorm P = p ∨ absNorm P = p ^ 2 := by
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.ne_zero).1 hP
  have hd : absNorm P ∣ p ^ 2 := by
    rw [← absNorm_natCast_span_sq hK]
    exact absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  rcases (Nat.dvd_prime_pow hp).1 hd with ⟨i, hi, he⟩
  interval_cases i
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using he)) hPp.ne_top
  · left; simpa using he
  · right; exact he

/-- The prime factors of `p𝓞 K`: one of norm `p²`, or two (with multiplicity) of norm `p`. -/
theorem pFactors_cases {p : ℕ} (hp : p.Prime) :
    (∃ P, pFactors (K := K) p = {P} ∧ absNorm P = p ^ 2) ∨
      (Multiset.card (pFactors (K := K) p) = 2 ∧ ∀ P ∈ pFactors (K := K) p, absNorm P = p) := by
  have hp2 := hp.two_le
  have hprod := prod_norm_pFactors hK hp.ne_zero
  by_cases hbig : ∃ P ∈ pFactors (K := K) p, absNorm P = p ^ 2
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
      have hQf : Q ∈ pFactors (K := K) p := by rw [ht]; exact Multiset.mem_cons_of_mem hQ
      have hQ1 : absNorm Q ∣ 1 := h1 ▸ Multiset.dvd_prod (Multiset.mem_map_of_mem _ hQ)
      rcases norm_of_mem_pFactors hK hp hQf with h | h <;> rw [h] at hQ1
      · exact absurd (Nat.eq_one_of_dvd_one hQ1) hp.one_lt.ne'
      · have := Nat.eq_one_of_dvd_one hQ1; nlinarith
    rw [ht, ht0]; rfl
  · right
    push Not at hbig
    have hall : ∀ P ∈ pFactors (K := K) p, absNorm P = p := fun P hP =>
      (norm_of_mem_pFactors hK hp hP).resolve_right (hbig P hP)
    refine ⟨?_, hall⟩
    have hrep : (pFactors (K := K) p).map absNorm =
        Multiset.replicate (Multiset.card (pFactors (K := K) p)) p := by
      rw [Multiset.eq_replicate]
      exact ⟨Multiset.card_map _ _, fun b hb => by
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hb; exact hall P hP⟩
    rw [hrep, Multiset.prod_replicate] at hprod
    exact Nat.pow_right_injective hp2 hprod

omit hK

/-- The prime factors of an ideal of norm `p^k` divide `p𝓞 K`. -/
theorem mem_pFactors_of_mem {p k : ℕ} (hp : p.Prime) {I P : Ideal (𝓞 K)} (hI : absNorm I = p ^ k)
    (hP : P ∈ normalizedFactors I) : P ∈ pFactors p := by
  have hI0 : I ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.symm
  obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
  refine (mem_pFactors hp.ne_zero).2 ⟨hPp, ?_⟩
  have hk : ((p ^ k : ℕ) : 𝓞 K) ∈ P := hIP (hI ▸ natCast_span_le I (Ideal.mem_span_singleton_self _))
  push_cast at hk
  exact hPp.mem_of_pow_mem k hk

end PrimePowers

/-! ### Split, inert and ramified primes -/

variable (K) in
/-- `p` splits: `p𝓞 = PQ` with `P ≠ Q`, both of norm `p`. -/
def Split (p : ℕ) : Prop :=
  ∃ P Q : Ideal (𝓞 K), P ≠ Q ∧ pFactors p = {P, Q} ∧ absNorm P = p ∧ absNorm Q = p

variable (K) in
/-- `p` is inert: `p𝓞` is prime, of norm `p²`. -/
def Inert (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), pFactors p = {P} ∧ absNorm P = p ^ 2

variable (K) in
/-- `p` ramifies: `p𝓞 = P²`, with `P` of norm `p`. -/
def Ramified (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), pFactors p = {P, P} ∧ absNorm P = p

/-- **Every prime splits, is inert or ramifies** in a quadratic field. -/
theorem trichotomy (hK : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    Split K p ∨ Inert K p ∨ Ramified K p := by
  rcases pFactors_cases hK hp with ⟨P, hf, hPn⟩ | ⟨hc, hall⟩
  · exact Or.inr (Or.inl ⟨P, hf, hPn⟩)
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc
    have hP : P ∈ pFactors (K := K) p := by rw [hPQ]; simp
    have hQ : Q ∈ pFactors (K := K) p := by rw [hPQ]; simp
    by_cases h : P = Q
    · subst h
      exact Or.inr (Or.inr ⟨P, hPQ, hall P hP⟩)
    · exact Or.inl ⟨P, Q, h, hPQ, hall P hP, hall Q hQ⟩

/-! ### The number of ideals of norm `p^k` -/

/-- An ideal all of whose prime factors equal `P` is a power of `P`. -/
theorem eq_pow_of_factors {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥) (h : ∀ Q ∈ normalizedFactors I, Q = P) :
    I = P ^ (normalizedFactors I).card := by
  have hrep : normalizedFactors I = Multiset.replicate (normalizedFactors I).card P :=
    Multiset.eq_replicate.2 ⟨rfl, h⟩
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, hrep]
  rw [Multiset.prod_replicate]

/-- An ideal all of whose prime factors are `P` or `Q` is `P^a Q^b`. -/
theorem eq_pow_mul_pow_of_factors {I P Q : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hPQ : P ≠ Q)
    (h : ∀ R ∈ normalizedFactors I, R = P ∨ R = Q) :
    I = P ^ (normalizedFactors I).count P * Q ^ (normalizedFactors I).count Q := by
  classical
  have hsplit : normalizedFactors I = Multiset.replicate ((normalizedFactors I).count P) P +
      Multiset.replicate ((normalizedFactors I).count Q) Q := by
    ext R
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hRP : R = P
    · subst hRP; rw [ite_eq_left rfl, ite_eq_right (Ne.symm hPQ), add_zero]
    by_cases hRQ : R = Q
    · subst hRQ; rw [ite_eq_right hPQ, ite_eq_left rfl, zero_add]
    rw [ite_eq_right (Ne.symm hRP), ite_eq_right (Ne.symm hRQ), add_zero, Multiset.count_eq_zero]
    intro hR
    rcases h R hR with h' | h'
    · exact hRP h'
    · exact hRQ h'
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, hsplit]
  rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate]

theorem ne_bot_of_norm {I : Ideal (𝓞 K)} {n : ℕ} (hn : n ≠ 0) (hI : absNorm I = n) : I ≠ ⊥ := by
  rintro rfl; rw [Ideal.absNorm_bot] at hI; exact hn hI.symm

theorem factors_pow_mul_pow {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hQ : Q.IsPrime) (hP0 : P ≠ ⊥)
    (hQ0 : Q ≠ ⊥) (a b : ℕ) :
    normalizedFactors (P ^ a * Q ^ b) = Multiset.replicate a P + Multiset.replicate b Q := by
  have hPi : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hQi : Irreducible Q := (Ideal.prime_of_isPrime hQ0 hQ).irreducible
  rw [normalizedFactors_mul (pow_ne_zero _ (by simpa using hP0)) (pow_ne_zero _ (by simpa using hQ0)),
    normalizedFactors_pow, normalizedFactors_pow, normalizedFactors_irreducible hPi,
    normalizedFactors_irreducible hQi, normalize_eq, normalize_eq, Multiset.nsmul_singleton,
    Multiset.nsmul_singleton]

/-- **Split**: `k + 1` ideals of norm `p^k`, the `P^a Q^{k−a}`. -/
theorem card_ofNorm_split {p : ℕ} (hp : p.Prime) (hs : Split K p) (k : ℕ) :
    (ofNorm (K := K) (p ^ k)).card = k + 1 := by
  classical
  obtain ⟨P, Q, hPQ, hf, hPn, hQn⟩ := hs
  have hPf : P ∈ pFactors (K := K) p := by rw [hf]; simp
  have hQf : Q ∈ pFactors (K := K) p := by rw [hf]; simp
  obtain ⟨hPp, hP0⟩ := pFactors_prime hp hPf
  obtain ⟨hQp, hQ0⟩ := pFactors_prime hp hQf
  have himg : ofNorm (K := K) (p ^ k) =
      (Finset.range (k + 1)).image (fun a => P ^ a * Q ^ (k - a)) := by
    ext I
    rw [mem_ofNorm, Finset.mem_image]
    constructor
    · intro hI
      have hI0 := ne_bot_of_norm (pow_ne_zero k hp.ne_zero) hI
      have hfac : ∀ R ∈ normalizedFactors I, R = P ∨ R = Q := fun R hR => by
        have := mem_pFactors_of_mem hp hI hR
        rw [hf] at this; simpa using this
      have hIe := eq_pow_mul_pow_of_factors hI0 hPQ hfac
      have hab : (normalizedFactors I).count P + (normalizedFactors I).count Q = k := by
        have h' := hI
        rw [hIe, map_mul, map_pow, map_pow, hPn, hQn, ← pow_add] at h'
        exact Nat.pow_right_injective hp.two_le h'
      refine ⟨(normalizedFactors I).count P, Finset.mem_range.2 (by omega), ?_⟩
      rw [show k - (normalizedFactors I).count P = (normalizedFactors I).count Q by omega]
      exact hIe.symm
    · rintro ⟨a, ha, rfl⟩
      have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
      rw [map_mul, map_pow, map_pow, hPn, hQn, ← pow_add, Nat.add_sub_cancel' hak]
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro a _ b _ hab
  have h := congrArg (fun I => (normalizedFactors I).count P) hab
  simp only [factors_pow_mul_pow hPp hQp hP0 hQ0, Multiset.count_add,
    Multiset.count_replicate_self, Multiset.count_replicate, ite_eq_right (Ne.symm hPQ),
    add_zero] at h
  exact h

/-- **Inert**: one ideal of norm `p^k` if `k` is even, none otherwise. -/
theorem card_ofNorm_inert {p : ℕ} (hp : p.Prime) (hi : Inert K p) (k : ℕ) :
    (ofNorm (K := K) (p ^ k)).card = if 2 ∣ k then 1 else 0 := by
  classical
  obtain ⟨P, hf, hPn⟩ := hi
  have hfac : ∀ {I : Ideal (𝓞 K)}, absNorm I = p ^ k → ∀ R ∈ normalizedFactors I, R = P :=
    fun {I} hI R hR => by
      have := mem_pFactors_of_mem hp hI hR
      rw [hf] at this; simpa using this
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Finset.card_eq_one]
    refine ⟨P ^ j, ?_⟩
    ext I
    rw [mem_ofNorm, Finset.mem_singleton]
    constructor
    · intro hI
      have hI0 := ne_bot_of_norm (pow_ne_zero _ hp.ne_zero) hI
      have hIe := eq_pow_of_factors hI0 (hfac hI)
      have h' := hI
      rw [hIe, map_pow, hPn, ← pow_mul] at h'
      have := Nat.pow_right_injective hp.two_le h'
      rw [hIe, show (normalizedFactors I).card = j by omega]
    · rintro rfl
      rw [map_pow, hPn, ← pow_mul]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro I hI
    rw [mem_ofNorm] at hI
    have hI0 := ne_bot_of_norm (pow_ne_zero _ hp.ne_zero) hI
    have hIe := eq_pow_of_factors hI0 (hfac hI)
    have h' := hI
    rw [hIe, map_pow, hPn, ← pow_mul] at h'
    exact hk ⟨_, (Nat.pow_right_injective hp.two_le h').symm⟩

/-- **Ramified**: one ideal of norm `p^k`, `P^k`. -/
theorem card_ofNorm_ramified {p : ℕ} (hp : p.Prime) (hr : Ramified K p) (k : ℕ) :
    (ofNorm (K := K) (p ^ k)).card = 1 := by
  classical
  obtain ⟨P, hf, hPn⟩ := hr
  rw [Finset.card_eq_one]
  refine ⟨P ^ k, ?_⟩
  ext I
  rw [mem_ofNorm, Finset.mem_singleton]
  constructor
  · intro hI
    have hI0 := ne_bot_of_norm (pow_ne_zero _ hp.ne_zero) hI
    have hfac : ∀ R ∈ normalizedFactors I, R = P := fun R hR => by
      have := mem_pFactors_of_mem hp hI hR
      rw [hf] at this; simpa using this
    have hIe := eq_pow_of_factors hI0 hfac
    have h' := hI
    rw [hIe, map_pow, hPn] at h'
    have := Nat.pow_right_injective hp.two_le h'
    rw [hIe, this]
  · rintro rfl
    rw [map_pow, hPn]

/-! ### `a_K = χ * 1` -/

section CountMult

open ArithmeticFunction

variable (K) in
/-- The number of ideals of norm `n`, as an arithmetic function. -/
noncomputable def rA : ArithmeticFunction ℤ := toArithmeticFunction fun n => ((ofNorm (K := K) n).card : ℤ)

theorem rA_apply {n : ℕ} (hn : n ≠ 0) : rA K n = (ofNorm (K := K) n).card := by
  simp [rA, toArithmeticFunction, hn]

theorem rA_mult : (rA K).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by rw [rA_apply one_ne_zero, card_ofNorm_one]; rfl,
    fun {m n} hm hn hmn => ?_⟩
  rw [rA_apply (mul_ne_zero hm hn), rA_apply hm, rA_apply hn,
    card_ofNorm_mul hmn (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)]
  push_cast; ring

theorem sum_neg_one_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j = if 2 ∣ k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), show j + j + 1 = 2 * j + 1 by ring, pow_succ,
        pow_mul]
      norm_num
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
        pow_mul]
      norm_num

/-- **The ideal count of a quadratic field.** If `χ` is multiplicative with `χ(p^k) = χ(p)^k`, and
`χ(p) = 1`, `−1` or `0` as `p` splits, is inert or ramifies, then the number of ideals of norm `n` is
`Σ_{d ∣ n} χ(d)`. -/
theorem rA_eq {χ : ArithmeticFunction ℤ} (hχ : χ.IsMultiplicative)
    (hpow : ∀ p k : ℕ, p.Prime → χ (p ^ k) = χ p ^ k)
    (htype : ∀ p : ℕ, p.Prime →
      (χ p = 1 ∧ Split K p) ∨ (χ p = -1 ∧ Inert K p) ∨ (χ p = 0 ∧ Ramified K p)) :
    rA K = χ * (zeta : ArithmeticFunction ℤ) := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ rA_mult _ (hχ.mul isMultiplicative_zeta.natCast)]
  intro p k hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, rA_apply (pow_ne_zero _ hp.ne_zero)]
  simp only [hpow _ _ hp]
  rcases htype p hp with ⟨h1, hs⟩ | ⟨h1, hi⟩ | ⟨h1, hr⟩
  · rw [card_ofNorm_split hp hs, h1]
    simp
  · rw [card_ofNorm_inert hp hi, h1, sum_neg_one_pow]
    split_ifs <;> simp
  · rw [card_ofNorm_ramified hp hr, h1, Finset.sum_range_succ']
    simp

end CountMult

/-! ### The Dedekind zeta function and its residue -/

section Zeta

/-- `ζ_K(s) = ζ(s)L(s, χ)` for `Re s > 1`, when the number of ideals of norm `n` is `Σ_{d∣n} χ(d)`. -/
theorem dedekindZeta_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {c : ArithmeticFunction ℤ}
    (hc : ∀ n : ℕ, χ n = (c n : ℂ)) (hrA : rA K = c * (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have hconv : ∀ n : ℕ, LSeries.convolution (fun m : ℕ ↦ χ m) 1 n = ∑ d ∈ n.divisors, (χ d : ℂ) := by
    intro n
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    exact Nat.sum_divisorsAntidiagonal (fun a _ ↦ (χ a : ℂ))
  have hcoef : ∀ n : ℕ, n ≠ 0 →
      ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℕ) : ℂ) =
        LSeries.convolution (fun m : ℕ ↦ χ m) 1 n := by
    intro n hn
    rw [hconv]
    have h1 : Nat.card {I : Ideal (𝓞 K) // absNorm I = n} = (ofNorm (K := K) n).card := by
      rw [ofNorm, ← Nat.card_eq_card_finite_toFinset]
      rfl
    have h2 : ((ofNorm (K := K) n).card : ℤ) = ∑ d ∈ n.divisors, c d := by
      rw [← rA_apply hn, hrA, ArithmeticFunction.coe_mul_zeta_apply]
    rw [h1, show (((ofNorm (K := K) n).card : ℕ) : ℂ) = (((ofNorm (K := K) n).card : ℤ) : ℂ) by
      push_cast; rfl, h2]
    push_cast
    exact Finset.sum_congr rfl fun d _ ↦ (hc d).symm
  rw [dedekindZeta, LSeries_congr (fun {n} hn ↦ hcoef n hn), LSeries_convolution'
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) (LSeriesSummable_one_iff.2 hs),
    LSeries_one_eq_riemannZeta hs, ← DirichletCharacter.LFunction_eq_LSeries χ hs, mul_comm]

/-- **`L(1, χ)` is the residue of `ζ_K` at `1`.** If `ζ_K(s) = ζ(s)L(s, χ)` for `Re s > 1` with `χ ≠ 1`, then
`L(1, χ)` equals Mathlib's `dedekindZeta_residue K`, the right side of the class number formula. -/
theorem LFunction_one_eq_residue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (h : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s) :
    DirichletCharacter.LFunction χ 1 = dedekindZeta_residue K := by
  have hres := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hof : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  -- the real line into the punctured neighbourhood of `1`
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hof ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h1
    have := Complex.ofReal_injective (h1.trans Complex.ofReal_one.symm)
    exact (ne_of_gt (Set.mem_Ioi.1 hs)) this
  have hz := riemannZeta_residue_one.comp hmap
  have hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    exact ((DirichletCharacter.differentiable_LFunction hχ).continuous.tendsto 1).comp hof
  have hprod := hz.mul hL
  rw [one_mul] at hprod
  have heq : (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) =ᶠ[𝓝[>] 1]
      ((fun s : ℂ ↦ (s - 1) * riemannZeta s) ∘ (fun s : ℝ ↦ (s : ℂ))) *
        fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [h s (by simpa using hs)]
    ring
  have hres' : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
    convert hres using 2
  exact tendsto_nhds_unique (hprod.congr' heq.symm) hres'

/-- The regulator of a number field of unit rank `0` is `1`. -/
theorem regulator_eq_one (h : Units.rank K = 0) : Units.regulator K = 1 := by
  classical
  have hE : IsEmpty (Fin (Units.rank K)) := by rw [h]; infer_instance
  have := (Units.equivFinRank K).symm.isEmpty
  rw [Units.regulator_eq_det', Matrix.det_isEmpty, abs_one]

/-- **The residue of `ζ_K` at `1` for an imaginary quadratic field**: `2πh_K/(w_K√|D_K|)`. -/
theorem residue_eq_imag (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    dedekindZeta_residue K =
      2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hc, hK] at h2
  have hc1 : InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hrank : Units.rank K = 0 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hc, hc1]
  rw [dedekindZeta_residue_def, hc, hc1, regulator_eq_one hrank]
  ring

/-- **The analytic class number formula for an imaginary quadratic field.** If `ζ_K(s) = ζ(s)L(s, χ)` for
`Re s > 1` with `χ ≠ 1`, then `L(1, χ) = 2πh_K/(w_K√|D_K|)`. -/
theorem LFunction_one_eq_imag (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (h : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s) :
    DirichletCharacter.LFunction χ 1 =
      ((2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) := by
  rw [LFunction_one_eq_residue χ hχ h, residue_eq_imag hK hc]

/-- **The residue of `ζ_K` at `1` for a real quadratic field**: `4R_K h_K/(w_K√D_K)`. -/
theorem residue_eq_real (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrComplexPlaces K = 0) :
    dedekindZeta_residue K =
      4 * Units.regulator K * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hc, hK] at h2
  have hr2 : InfinitePlace.nrRealPlaces K = 2 := by omega
  rw [dedekindZeta_residue_def, hc, hr2]
  ring

end Zeta

end QuadIdeals
