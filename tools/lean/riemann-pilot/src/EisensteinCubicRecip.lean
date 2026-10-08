import EisensteinCubicChar

/-! # S1, part 3b: cubic reciprocity on `ℤ[ω]` (round 290)

**`cub_recip`**: for coprime `a, b ∈ ℤ[ω]` with `a ≡ b ≡ 1 (mod 3)`, `(a/b)₃ = (b/a)₃`. Here
`(a/𝔟)₃ = Π_{P∣𝔟} χ_P(a)` over the prime factors with multiplicity (`cub`), with `χ_P` the `ℤ[ω]`-valued
cubic character of `EisensteinCubicChar.lean` (`chi3`: `0` unless `P` is maximal with `3 ∉ P`).

* **Primes** (`maximal_cases`): a maximal ideal prime to `3` is inert, `P = (q)` with `q ≡ 2 (mod 3)` and
  `N(P) = q²`, or of prime norm `p ≡ 1 (mod 3)` (round 284's splitting law).
* **Three cases from the Gauss-sum relation** (`chi3_fundamental`):
  - (A) `recip_inert`: a primary `π` of prime norm against an inert `q`, whose primary associate is `−q`.
    Rational integers prime to `q` are cubes modulo `q` (`chi3_natCast_inert`), and `N(Q) = q²`.
  - (B) `recip_split`: primary `π`, `ρ` of distinct prime norms `p`, `p'`. The relation for `(P, Q)` and for
    `(Q, P)` give `χ_Q(p)χ_Q(π) = χ_P(p')²` and `χ_P(p')χ_P(ρ) = χ_Q(p)²`, hence `χ_Q(π) = χ_P(ρ)`.
  - (D) `recip_inert_inert`: two inert primes, both symbols `1`.
* **Primary generators** (`pgen`): every maximal ideal prime to `3` has a unique primary generator
  (`exists_primary_of_maximal`, `primary_unique`), and a primary element is the product of the primary
  generators of its prime factors (`prod_pgen`). So the law at primes gives the law for elements
  (`cub_recip_of_prime`); at coprime norms it is `cub_recip_of_coprime_norm`.
* **(C) Conjugate primes** (`recip_conj`): for `P` of prime norm, `P̄ ≠ P` (`map_cj_ne`: otherwise its primary
  generator is real and `p` a square). With `T = −(π + π̄) ∈ ℤ`, `χ_P(π̄) = χ_P(T) = (π/T)₃` by the coprime-norm
  law, and `(π/T)₃ = (π̄/T)₃` is fixed by conjugation (`chi3_map_cj`, `mul_cj_eq_absNorm`), so it is `1`;
  so `χ_{P̄}(π) = χ_P(π̄) = 1`.
* **All primes** (`chi3_pgen_recip`): two distinct primes either have coprime norms or are conjugate.
-/

open NumberField Ideal Polynomial UniqueFactorizationMonoid

namespace Eis

/-! ### The cubic symbol at a prime, and the reciprocity cases -/

section Symbol3

open Classical in
/-- `χ_P(a)` with values in `ℤ[ω]`: `0` unless `P` is maximal and `3 ∉ P`. -/
noncomputable def chi3 (P : Ideal (𝓞 K)) (a : 𝓞 K) : 𝓞 K :=
  if h : P.IsMaximal ∧ (3 : 𝓞 K) ∉ P then
    haveI := h.1; cubChar P h.2 (Ideal.Quotient.mk P a)
  else 0

theorem chi3_eq {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) (a : 𝓞 K) :
    chi3 P a = cubChar P hP3 (Ideal.Quotient.mk P a) := by
  unfold chi3
  split_ifs with h
  · rfl
  · exact absurd ⟨hP, hP3⟩ h

theorem chi3_mul (P : Ideal (𝓞 K)) (a b : 𝓞 K) : chi3 P (a * b) = chi3 P a * chi3 P b := by
  unfold chi3
  split_ifs with h
  · have := h.1; rw [map_mul, map_mul]
  · simp

theorem chi3_of_mem {P : Ideal (𝓞 K)} {a : 𝓞 K} (ha : a ∈ P) : chi3 P a = 0 := by
  unfold chi3; split_ifs with h
  · have := h.1
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 ha, MulChar.map_zero]
  · rfl

theorem chi3_add_mem {P : Ideal (𝓞 K)} (a : 𝓞 K) {b : 𝓞 K} (hb : b ∈ P) :
    chi3 P (a + b) = chi3 P a := by
  unfold chi3; split_ifs with h
  · have := h.1
    rw [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hb, add_zero]
  · rfl

variable {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)
include hP3

theorem chi3_pow_three {a : 𝓞 K} (ha : a ∉ P) : chi3 P a ^ 3 = 1 := by
  rw [chi3_eq hP3]
  have hu : Ideal.Quotient.mk P a ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  simpa using (cubChar_spec P hP3 (Units.mk0 _ hu)).2

theorem chi3_one : chi3 P 1 = 1 := by rw [chi3_eq hP3, map_one, MulChar.map_one]

theorem chi3_neg_one : chi3 P (-1) = 1 := by
  have h1 : chi3 P (-1) ^ 3 = 1 := chi3_pow_three hP3 (fun h => hP.ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem_iff.2 h)))
  have h2 : chi3 P (-1) ^ 2 = 1 := by
    rw [sq, ← chi3_mul, neg_one_mul, neg_neg, chi3_one hP3]
  calc chi3 P (-1) = chi3 P (-1) ^ 3 := by rw [pow_succ, h2, one_mul]
    _ = 1 := h1

theorem chi3_neg (a : 𝓞 K) : chi3 P (-a) = chi3 P a := by
  rw [neg_eq_neg_one_mul, chi3_mul, chi3_neg_one hP3, one_mul]

omit hP3 in
theorem absNorm_eq_card : absNorm P = Fintype.card (𝓞 K ⧸ P) := by
  rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

omit hP hP3 in
theorem natCast_absNorm_mem : ((absNorm P : ℕ) : 𝓞 K) ∈ P :=
  natCast_span_le P (Ideal.mem_span_singleton_self _)

end Symbol3

/-! ### Maximal ideals prime to `3`: inert or split -/

section Cases

theorem maximal_cases (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) :
    (∃ q : ℕ, q.Prime ∧ q % 3 = 2 ∧ P = span {(q : 𝓞 K)} ∧ absNorm P = q ^ 2) ∨
      (∃ p : ℕ, p.Prime ∧ p % 3 = 1 ∧ absNorm P = p) := by
  classical
  obtain ⟨n, hp, hc⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))
  set p := ringChar (𝓞 K ⧸ P)
  have hpP : (p : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact ringChar.Nat.cast_ringChar
  have hPf : P ∈ pFactors p := (mem_pFactors hp.ne_zero).2 ⟨hP.isPrime, hpP⟩
  have hp3 : p ≠ 3 := by rintro h; rw [h] at hpP; exact hP3 (by exact_mod_cast hpP)
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 ≠ 0 := by
      intro h0
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  rcases hmod with h1 | h2
  · right
    obtain ⟨P1, P2, -, hpf, hN1, hN2⟩ := split_of_mod_one hp h1
    refine ⟨p, hp, h1, ?_⟩
    rw [hpf] at hPf
    rcases Multiset.mem_cons.1 hPf with rfl | h
    · exact hN1
    · rw [Multiset.mem_singleton.1 h]; exact hN2
  · left
    obtain ⟨P', hpf, hN⟩ := inert_of_mod_two hp h2
    have hPP' : P = P' := by rw [hpf] at hPf; exact Multiset.mem_singleton.1 hPf
    refine ⟨p, hp, h2, ?_, by rw [hPP', hN]⟩
    rw [← prod_pFactors hp.ne_zero, hpf, Multiset.prod_singleton, hPP']

/-- Rational integers prime to an inert `q` are cubes modulo `q`. -/
theorem chi3_natCast_inert {q : ℕ} (hq : q.Prime) (hq2 : q % 3 = 2) {Q : Ideal (𝓞 K)}
    [hQ : Q.IsMaximal] (hQq : Q = span {(q : 𝓞 K)}) (hNQ : absNorm Q = q ^ 2) {n : ℕ}
    (hn : ¬ q ∣ n) : chi3 Q (n : 𝓞 K) = 1 := by
  have hQ3 : (3 : 𝓞 K) ∉ Q := by
    intro h3
    exact not_coprime_mem hQ.ne_top ((Nat.coprime_primes Nat.prime_three hq).2 (by omega))
      (by exact_mod_cast h3) (by rw [hQq]; exact Ideal.mem_span_singleton_self _)
  have : Fact q.Prime := ⟨hq⟩
  have hqF : ((q : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem, hQq]
    exact Ideal.mem_span_singleton_self _
  have hch : CharP (𝓞 K ⧸ Q) q := (CharP.charP_iff_prime_eq_zero hq).2 hqF
  have hn0 : ((n : ℕ) : 𝓞 K ⧸ Q) ≠ 0 := fun h => hn ((CharP.cast_eq_zero_iff _ q n).1 h)
  have hfrob : ((n : ℕ) : 𝓞 K ⧸ Q) ^ q = n := by
    have := map_natCast (frobenius (𝓞 K ⧸ Q) q) n
    rwa [frobenius_def] at this
  have hq1 : ((n : ℕ) : 𝓞 K ⧸ Q) ^ (q - 1) = 1 := by
    have hq0 : 1 ≤ q := hq.one_lt.le
    have e : ((n : ℕ) : 𝓞 K ⧸ Q) ^ (q - 1) * n = 1 * n := by
      rw [← pow_succ, Nat.sub_add_cancel hq0, hfrob, one_mul]
    exact mul_right_cancel₀ hn0 e
  have hm3 : m3 Q = (q - 1) * ((q + 1) / 3) := by
    unfold m3
    rw [← absNorm_eq_card, hNQ]
    obtain ⟨k, hk⟩ : 3 ∣ q + 1 := by omega
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have e : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
      rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel]
    rw [this, hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3), mul_left_comm,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  rw [chi3_eq hQ3]
  have hu := cubChar_spec Q hQ3 (Units.mk0 _ hn0)
  rw [Units.val_mk0, hm3, pow_mul, hq1, one_pow] at hu
  rw [map_natCast]
  exact cube_eq_of_mk_eq Q hQ3 hu.2 (one_pow 3) (by rw [hu.1, map_one])

theorem three_not_mem_of_primary {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {π : 𝓞 K} (hπ : Primary π)
    (hPπ : P = span {π}) : (3 : 𝓞 K) ∉ P := by
  intro h3
  rw [hPπ, Ideal.mem_span_singleton] at h3
  have h1 : π ∣ π - 1 := h3.trans hπ
  have : π ∣ (1 : 𝓞 K) := by
    have := dvd_sub (dvd_refl π) h1; rwa [sub_sub_cancel] at this
  exact hP (by rw [hPπ, Ideal.span_singleton_eq_top]; exact isUnit_of_dvd_one this)

/-- The fundamental relation in terms of `chi3` and norms. -/
theorem chi3_fundamental {P Q : Ideal (𝓞 K)} [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (hP3 : (3 : 𝓞 K) ∉ P) (hQ3 : (3 : 𝓞 K) ∉ Q) {π : 𝓞 K} (hπ : Primary π) (hPπ : P = span {π})
    (hPQ : ((absNorm P : ℕ) : 𝓞 K) ∉ Q) :
    chi3 Q (-((absNorm P : ℕ) : 𝓞 K) * π) = chi3 P ((absNorm Q : ℕ) : 𝓞 K) ^ 2 := by
  rw [chi3_eq hQ3, chi3_eq hP3, absNorm_eq_card (P := P), absNorm_eq_card (P := Q), map_natCast]
  rw [absNorm_eq_card] at hPQ
  exact cubChar_fundamental P hP3 Q hQ3 hπ hPπ hPQ

/-- **Case (B)**: primary `π`, `ρ` of distinct prime norms. -/
theorem recip_split {P Q : Ideal (𝓞 K)} [hP : P.IsMaximal] [hQ : Q.IsMaximal] {π ρ : 𝓞 K}
    (hπ : Primary π) (hρ : Primary ρ) (hPπ : P = span {π}) (hQρ : Q = span {ρ}) {p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hpp' : p ≠ p') (hNP : absNorm P = p) (hNQ : absNorm Q = p') :
    chi3 Q π = chi3 P ρ := by
  have hP3 := three_not_mem_of_primary hP.ne_top hπ hPπ
  have hQ3 := three_not_mem_of_primary hQ.ne_top hρ hQρ
  have hcop : p.Coprime p' := (Nat.coprime_primes hp hp').2 hpp'
  have hpP : (p : 𝓞 K) ∈ P := hNP ▸ natCast_absNorm_mem
  have hpQ : (p' : 𝓞 K) ∈ Q := hNQ ▸ natCast_absNorm_mem
  have hpQ' : (p : 𝓞 K) ∉ Q := fun h => not_coprime_mem hQ.ne_top hcop h hpQ
  have hpP' : (p' : 𝓞 K) ∉ P := fun h => not_coprime_mem hP.ne_top hcop hpP h
  have h1 := chi3_fundamental hP3 hQ3 hπ hPπ (by rw [hNP]; exact hpQ')
  have h2 := chi3_fundamental hQ3 hP3 hρ hQρ (by rw [hNQ]; exact hpP')
  rw [hNP, hNQ, neg_mul, chi3_neg hQ3, chi3_mul] at h1
  rw [hNP, hNQ, neg_mul, chi3_neg hP3, chi3_mul] at h2
  have ha := chi3_pow_three hQ3 hpQ'
  have hc := chi3_pow_three hP3 hpP'
  linear_combination (-chi3 Q π) * ha + chi3 Q (p : 𝓞 K) ^ 2 * h1 + chi3 P ρ * hc -
    chi3 P (p' : 𝓞 K) ^ 2 * h2

/-- **Case (A)**: a primary `π` of prime norm against an inert `q` (primary associate `−q`). -/
theorem recip_inert {P Q : Ideal (𝓞 K)} [hP : P.IsMaximal] [hQ : Q.IsMaximal] {π : 𝓞 K}
    (hπ : Primary π) (hPπ : P = span {π}) {p q : ℕ} (hp : p.Prime) (hNP : absNorm P = p)
    (hq : q.Prime) (hq2 : q % 3 = 2) (hQq : Q = span {(q : 𝓞 K)}) (hNQ : absNorm Q = q ^ 2) :
    chi3 Q π = chi3 P (-(q : 𝓞 K)) := by
  have hP3 := three_not_mem_of_primary hP.ne_top hπ hPπ
  have hQ3 : (3 : 𝓞 K) ∉ Q := by
    intro h3
    exact not_coprime_mem hQ.ne_top ((Nat.coprime_primes Nat.prime_three hq).2 (by omega))
      (by exact_mod_cast h3) (by rw [hQq]; exact Ideal.mem_span_singleton_self _)
  have hpP : (p : 𝓞 K) ∈ P := hNP ▸ natCast_absNorm_mem
  have hqP : (q : 𝓞 K) ∉ P := by
    intro h
    have hle : Q ≤ P := by rw [hQq, Ideal.span_singleton_le_iff_mem]; exact h
    have := hQ.eq_of_le hP.ne_top hle
    rw [← this, hNQ] at hNP
    have := hp.one_lt
    have h2 : q ^ 2 = q * q := sq q
    have hq1 := hq.one_lt
    rw [← hNP] at hp
    exact Nat.not_prime_mul (by omega) (by omega) (h2 ▸ hp)
  have hpq : p ≠ q := by rintro rfl; exact hqP hpP
  have hpQ : (p : 𝓞 K) ∉ Q := fun h =>
    not_coprime_mem hQ.ne_top ((Nat.coprime_primes hp hq).2 hpq) h
      (by rw [hQq]; exact Ideal.mem_span_singleton_self _)
  have h1 := chi3_fundamental hP3 hQ3 hπ hPπ (by rw [hNP]; exact hpQ)
  rw [hNP, hNQ, neg_mul, chi3_neg hQ3, chi3_mul,
    chi3_natCast_inert hq hq2 hQq hNQ (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm),
    one_mul] at h1
  rw [h1, chi3_neg hP3, Nat.cast_pow, show chi3 P ((q : 𝓞 K) ^ 2) = chi3 P q * chi3 P q by
    rw [sq, chi3_mul], ← sq, ← pow_mul]
  have hc := chi3_pow_three hP3 hqP
  rw [show 2 * 2 = 3 + 1 by rfl, pow_succ, hc, one_mul]

/-- **Case (D)**: two inert primes. -/
theorem recip_inert_inert {Q Q' : Ideal (𝓞 K)} [hQ : Q.IsMaximal] [hQ' : Q'.IsMaximal] {q q' : ℕ}
    (hq : q.Prime) (hq2 : q % 3 = 2) (hQq : Q = span {(q : 𝓞 K)}) (hNQ : absNorm Q = q ^ 2)
    (hq' : q'.Prime) (hq2' : q' % 3 = 2) (hQq' : Q' = span {(q' : 𝓞 K)})
    (hNQ' : absNorm Q' = q' ^ 2) (hne : q ≠ q') :
    chi3 Q (-(q' : 𝓞 K)) = chi3 Q' (-(q : 𝓞 K)) := by
  have hQ3 : (3 : 𝓞 K) ∉ Q := by
    intro h3
    exact not_coprime_mem hQ.ne_top ((Nat.coprime_primes Nat.prime_three hq).2 (by omega))
      (by exact_mod_cast h3) (by rw [hQq]; exact Ideal.mem_span_singleton_self _)
  have hQ3' : (3 : 𝓞 K) ∉ Q' := by
    intro h3
    exact not_coprime_mem hQ'.ne_top ((Nat.coprime_primes Nat.prime_three hq').2 (by omega))
      (by exact_mod_cast h3) (by rw [hQq']; exact Ideal.mem_span_singleton_self _)
  rw [chi3_neg hQ3, chi3_neg hQ3', chi3_natCast_inert hq hq2 hQq hNQ
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hq').1 h)),
    chi3_natCast_inert hq' hq2' hQq' hNQ' (fun h => hne ((Nat.prime_dvd_prime_iff_eq hq' hq).1 h).symm)]

end Cases

/-! ### Primary generators of ideals and the cubic symbol `(a/𝔟)₃` -/

section PrimaryGen

theorem primary_unique {a b : 𝓞 K} (ha : Primary a) (hb : Primary b) (h : span {a} = span {b}) :
    a = b := by
  rw [Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have := ha.unit_eq_one (by rw [mul_comm, hu]; exact hb)
  rw [← hu, this, Units.val_one, mul_one]

open Classical in
/-- The primary generator of an ideal that has one (`1` otherwise). -/
noncomputable def pgen (I : Ideal (𝓞 K)) : 𝓞 K :=
  if h : ∃ a, Primary a ∧ span {a} = I then h.choose else 1

theorem pgen_spec {I : Ideal (𝓞 K)} (h : ∃ a, Primary a ∧ span {a} = I) :
    Primary (pgen I) ∧ span {pgen I} = I := by
  have e : pgen I = h.choose := by unfold pgen; simp [h]
  rw [e]; exact h.choose_spec

theorem pgen_eq {a : 𝓞 K} (ha : Primary a) : pgen (span {a}) = a :=
  primary_unique (pgen_spec ⟨a, ha, rfl⟩).1 ha (pgen_spec ⟨a, ha, rfl⟩).2

theorem lam_not_unit : ¬ IsUnit (ω - 1) := fun h => by
  have h3 : IsUnit (3 : 𝓞 K) := by
    have e : (3 : 𝓞 K) = (ω - 1) * (ω - 1) * (-(ω ^ 2)) := by
      linear_combination ω_sq_add + (ω - 2) * ω_cube
    rw [e]
    exact (h.mul h).mul (isUnit_iff_exists_inv.2 ⟨-ω, by linear_combination ω_cube⟩)
  exact not_three_dvd_one h3.dvd

/-- A maximal ideal prime to `3` has a primary generator. -/
theorem exists_primary_of_maximal (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) :
    ∃ a, Primary a ∧ span {a} = P := by
  have hlam : ¬ (ω - 1) ∣ Submodule.IsPrincipal.generator P := by
    intro h
    have hle : P ≤ span {ω - 1} := by
      rw [← Ideal.span_singleton_generator P, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]; exact h
    have hne : span {ω - 1} ≠ (⊤ : Ideal (𝓞 K)) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact lam_not_unit
    have heq := hP.eq_of_le hne hle
    apply hP3
    rw [heq, Ideal.mem_span_singleton]; exact lam_dvd_three
  obtain ⟨u, hu⟩ := exists_primary hlam
  exact ⟨u * Submodule.IsPrincipal.generator P, hu, by rw [Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_generator]⟩

theorem pgen_maximal (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) :
    Primary (pgen P) ∧ span {pgen P} = P :=
  pgen_spec (exists_primary_of_maximal P hP3)

/-- A prime ideal containing a primary element does not contain `3`. -/
theorem three_not_mem_of_primary_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {a : 𝓞 K} (ha : Primary a)
    (haP : a ∈ P) : (3 : 𝓞 K) ∉ P := by
  intro h3
  have h1 : a - 1 ∈ P := by
    obtain ⟨c, hc⟩ := ha
    rw [hc]; exact P.mul_mem_right _ h3
  exact hP ((Ideal.eq_top_iff_one _).2 (by simpa using P.sub_mem haP h1))

theorem primary_multiset_prod {m : Multiset (𝓞 K)} (h : ∀ x ∈ m, Primary x) : Primary m.prod := by
  induction m using Multiset.induction_on with
  | empty => simpa using primary_one
  | cons x m ih =>
    rw [Multiset.prod_cons]
    exact (h x (Multiset.mem_cons_self x m)).mul (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem isMaximal_of_mem_nf {I P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I) : P.IsMaximal := by
  have hPprime := prime_of_normalized_factor P hP
  exact (Ideal.isPrime_of_prime hPprime).isMaximal hPprime.ne_zero

/-- **A primary element is the product of the primary generators of its prime factors.** -/
theorem prod_pgen {a : 𝓞 K} (ha : Primary a) :
    ((normalizedFactors (span {a})).map pgen).prod = a := by
  have ha0 : a ≠ 0 := fun h => by
    have : (3 : 𝓞 K) ∣ 0 - 1 := h ▸ ha
    exact not_three_dvd_one (by simpa using this)
  have hspan0 : span {a} ≠ (⊥ : Ideal (𝓞 K)) := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hspec : ∀ P ∈ normalizedFactors (span {a}), Primary (pgen P) ∧ span {pgen P} = P := by
    intro P hP
    have := isMaximal_of_mem_nf hP
    have haP : a ∈ P := by
      have := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
      exact this (Ideal.mem_span_singleton_self a)
    exact pgen_maximal P (three_not_mem_of_primary_mem (IsMaximal.ne_top ‹_›) ha haP)
  apply primary_unique (primary_multiset_prod fun x hx => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx; exact (hspec P hP).1) ha
  rw [← Ideal.multiset_prod_span_singleton, Multiset.map_map]
  have : (normalizedFactors (span {a})).map ((fun x => span {x}) ∘ pgen) =
      (normalizedFactors (span {a})).map id :=
    Multiset.map_congr rfl fun P hP => (hspec P hP).2
  rw [this, Multiset.map_id, Ideal.prod_normalizedFactors_eq_self hspan0]

end PrimaryGen

section CubSymbol

/-- **The cubic residue symbol** `(a/𝔟)₃ = Π_{P∣𝔟} χ_P(a)` (prime factors with multiplicity), with
values in `ℤ[ω]`. -/
noncomputable def cub (a : 𝓞 K) (I : Ideal (𝓞 K)) : 𝓞 K :=
  ((normalizedFactors I).map fun P => chi3 P a).prod

theorem cub_prime {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (a : 𝓞 K) : cub a P = chi3 P a := by
  have hP0 : P ≠ ⊥ := ne_bot P
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP.isPrime).irreducible
  rw [cub, normalizedFactors_irreducible hirr, normalize_eq]
  simp

theorem chi3_multiset_prod {Q : Ideal (𝓞 K)} [Q.IsMaximal] (hQ3 : (3 : 𝓞 K) ∉ Q)
    (m : Multiset (𝓞 K)) : chi3 Q m.prod = (m.map (chi3 Q)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp [chi3_one hQ3]
  | cons x m ih => rw [Multiset.prod_cons, chi3_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/-- **Reciprocity from the prime case**: if `χ_Q(π_P) = χ_P(π_Q)` for every prime factor `P` of
`a` and `Q` of `b`, then `(a/b)₃ = (b/a)₃` for primary `a`, `b`. -/
theorem cub_recip_of_prime {a b : 𝓞 K} (ha : Primary a) (hb : Primary b)
    (H : ∀ P ∈ normalizedFactors (span {a}), ∀ Q ∈ normalizedFactors (span {b}),
      chi3 Q (pgen P) = chi3 P (pgen Q)) :
    cub a (span {b}) = cub b (span {a}) := by
  have h3 : ∀ {c : 𝓞 K}, Primary c → ∀ R ∈ normalizedFactors (span {c}), (3 : 𝓞 K) ∉ R := by
    intro c hc R hR
    have := isMaximal_of_mem_nf hR
    exact three_not_mem_of_primary_mem (IsMaximal.ne_top ‹_›)
      hc (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hR) (Ideal.mem_span_singleton_self c))
  unfold cub
  conv_lhs => rw [← prod_pgen ha]
  conv_rhs => rw [← prod_pgen hb]
  have e1 : (normalizedFactors (span {b})).map (fun Q => chi3 Q
      ((normalizedFactors (span {a})).map pgen).prod) =
      (normalizedFactors (span {b})).map (fun Q =>
        ((normalizedFactors (span {a})).map fun P => chi3 Q (pgen P)).prod) := by
    refine Multiset.map_congr rfl fun Q hQ => ?_
    have := isMaximal_of_mem_nf hQ
    rw [chi3_multiset_prod (h3 hb Q hQ), Multiset.map_map]; rfl
  have e2 : (normalizedFactors (span {a})).map (fun P => chi3 P
      ((normalizedFactors (span {b})).map pgen).prod) =
      (normalizedFactors (span {a})).map (fun P =>
        ((normalizedFactors (span {b})).map fun Q => chi3 P (pgen Q)).prod) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    have := isMaximal_of_mem_nf hP
    rw [chi3_multiset_prod (h3 ha P hP), Multiset.map_map]; rfl
  rw [e1, e2, Multiset.prod_map_prod_map]
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  congr 1
  exact Multiset.map_congr rfl fun Q hQ => H P hP Q hQ

end CubSymbol

section RecipCoprime

theorem primary_neg_natCast {q : ℕ} (hq2 : q % 3 = 2) : Primary (-(q : 𝓞 K)) := by
  obtain ⟨k, hk⟩ : 3 ∣ q + 1 := by omega
  refine ⟨-(k : 𝓞 K), ?_⟩
  have : ((q + 1 : ℕ) : 𝓞 K) = ((3 * k : ℕ) : 𝓞 K) := by rw [hk]
  push_cast at this
  linear_combination -this

theorem pgen_inert {P : Ideal (𝓞 K)} {q : ℕ} (hq2 : q % 3 = 2) (hPq : P = span {(q : 𝓞 K)}) :
    pgen P = -(q : 𝓞 K) := by
  rw [hPq, ← Ideal.span_singleton_neg]
  exact pgen_eq (primary_neg_natCast hq2)

/-- **Prime reciprocity for coprime norms**: `χ_Q(π_P) = χ_P(π_Q)`. -/
theorem chi3_pgen_recip_of_coprime {P Q : Ideal (𝓞 K)} [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (hP3 : (3 : 𝓞 K) ∉ P) (hQ3 : (3 : 𝓞 K) ∉ Q) (h : (absNorm P).Coprime (absNorm Q)) :
    chi3 Q (pgen P) = chi3 P (pgen Q) := by
  rcases maximal_cases P hP3 with ⟨q, hq, hq2, hPq, hNP⟩ | ⟨p, hp, hp1, hNP⟩ <;>
    rcases maximal_cases Q hQ3 with ⟨q', hq', hq2', hQq, hNQ⟩ | ⟨p', hp', hp1', hNQ⟩
  · rw [pgen_inert hq2 hPq, pgen_inert hq2' hQq]
    have hne : q ≠ q' := by
      rintro rfl
      rw [hNP, hNQ, Nat.coprime_self] at h
      have := hq.one_lt
      nlinarith
    exact recip_inert_inert hq' hq2' hQq hNQ hq hq2 hPq hNP hne.symm
  · obtain ⟨hρ, hQρ⟩ := pgen_maximal Q hQ3
    rw [pgen_inert hq2 hPq]
    exact (recip_inert hρ hQρ.symm hp' hNQ hq hq2 hPq hNP).symm
  · obtain ⟨hπ, hPπ⟩ := pgen_maximal P hP3
    rw [pgen_inert hq2' hQq]
    exact recip_inert hπ hPπ.symm hp hNP hq' hq2' hQq hNQ
  · obtain ⟨hπ, hPπ⟩ := pgen_maximal P hP3
    obtain ⟨hρ, hQρ⟩ := pgen_maximal Q hQ3
    have hne : p ≠ p' := by
      rintro rfl
      rw [hNP, hNQ, Nat.coprime_self] at h
      exact hp.one_lt.ne' h
    exact recip_split hπ hρ hPπ.symm hQρ.symm hp hp' hne hNP hNQ

theorem three_not_mem_nf {a : 𝓞 K} (ha : Primary a) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors (span {a})) : (3 : 𝓞 K) ∉ P := by
  have := isMaximal_of_mem_nf hP
  exact three_not_mem_of_primary_mem (IsMaximal.ne_top ‹_›) ha
    (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self a))

theorem absNorm_dvd_of_mem_nf {a : 𝓞 K} {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors (span {a})) :
    absNorm P ∣ absNorm (span {a}) :=
  absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP))

/-- **Cubic reciprocity for primary elements of coprime norms.** -/
theorem cub_recip_of_coprime_norm {a b : 𝓞 K} (ha : Primary a) (hb : Primary b)
    (h : (absNorm (span {a})).Coprime (absNorm (span {b}))) :
    cub a (span {b}) = cub b (span {a}) := by
  apply cub_recip_of_prime ha hb
  intro P hP Q hQ
  have := isMaximal_of_mem_nf hP
  have := isMaximal_of_mem_nf hQ
  exact chi3_pgen_recip_of_coprime (three_not_mem_nf ha hP) (three_not_mem_nf hb hQ)
    ((h.coprime_dvd_left (absNorm_dvd_of_mem_nf hP)).coprime_dvd_right (absNorm_dvd_of_mem_nf hQ))

end RecipCoprime

section Conjugate

/-- `x·x̄ = N(x)`. -/
theorem mul_cj_eq_absNorm (x : 𝓞 K) : x * cj x = ((absNorm (span {x}) : ℕ) : 𝓞 K) := by
  obtain ⟨m, n, rfl⟩ := exists_coords x
  set N0 := m ^ 2 - m * n + n ^ 2 with hN0def
  have hN0 : 0 ≤ N0 := by nlinarith [sq_nonneg (m - n), sq_nonneg m, sq_nonneg n]
  have hc : ((N0 : ℤ) : 𝓞 K) = ((N0.toNat : ℕ) : 𝓞 K) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hN0]
    rw [Int.cast_natCast]
  have e : absNorm (span {(m : 𝓞 K) + n * ω}) * absNorm (span {cj ((m : 𝓞 K) + n * ω)}) =
      absNorm (span {((m : 𝓞 K) + n * ω) * cj ((m : 𝓞 K) + n * ω)}) := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton]
  rw [absNorm_span_cj, mul_cj_coords, hc, absNorm_natCast_span_sq, ← sq] at e
  have h2 := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) e
  rw [mul_cj_coords, hc, h2]

variable {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)

omit hP in
include hP3 in
theorem three_not_mem_map_cj : (3 : 𝓞 K) ∉ P.map cj := by
  intro h
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨x, hx, hx3⟩ := h
  have : x = 3 := by rw [← cj_cj x, hx3, map_ofNat]
  exact hP3 (this ▸ hx)

include hP3 in
/-- **Conjugation equivariance**: `χ_{P̄}(ā) = conj(χ_P(a))`. -/
theorem chi3_map_cj (a : 𝓞 K) : chi3 (P.map cj) (cj a) = cj (chi3 P a) := by
  classical
  have hP3' := three_not_mem_map_cj hP3
  set P' := P.map cj
  by_cases ha : a ∈ P
  · rw [chi3_of_mem ha, chi3_of_mem (Ideal.mem_map_of_mem _ ha), map_zero]
  let e : 𝓞 K ⧸ P ≃+* 𝓞 K ⧸ P' := Ideal.quotientEquiv P P' cj rfl
  have he : ∀ x, e (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P' (cj x) := fun x => rfl
  have hcard : Fintype.card (𝓞 K ⧸ P') = Fintype.card (𝓞 K ⧸ P) :=
    (Fintype.card_congr e.toEquiv).symm
  have hm3 : m3 P' = m3 P := by unfold m3; rw [hcard]
  set y := Ideal.Quotient.mk P a
  have hy : y ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hey : e y ≠ 0 := by rwa [Ne, map_eq_zero_iff e e.injective]
  rw [chi3_eq hP3, chi3_eq hP3', ← he]
  have s1 := cubChar_spec P' hP3' (Units.mk0 (e y) hey)
  have s2 := cubChar_spec P hP3 (Units.mk0 y hy)
  rw [Units.val_mk0] at s1 s2
  apply cube_eq_of_mk_eq P' hP3' s1.2 (by rw [← map_pow, s2.2, map_one])
  rw [s1.1, hm3, ← he, ← map_pow, ← s2.1]

end Conjugate

section Recip

theorem map_cj_span (x : 𝓞 K) : (span {x}).map cj = span {cj x} := by
  rw [Ideal.map_span, Set.image_singleton]

theorem absNorm_span_intCast (t : ℤ) : absNorm (span {(t : 𝓞 K)}) = t.natAbs ^ 2 := by
  have e : span {(t : 𝓞 K)} = span {((t.natAbs : ℕ) : 𝓞 K)} := by
    rcases Int.natAbs_eq t with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Ideal.span_singleton_neg]; simp
  rw [e, absNorm_natCast_span_sq]

theorem one_add_two_ω_ne_zero : (1 + 2 * ω : 𝓞 K) ≠ 0 := by
  intro h
  have h3 : (3 : 𝓞 K) = 0 := by linear_combination (-(1 + 2 * ω) : 𝓞 K) * h + 4 * ω_sq_add
  have := congrArg ((↑) : 𝓞 K → K) h3
  norm_num at this

variable {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} (hp : p.Prime)
  (hNP : absNorm P = p)

include hP3 hp hNP in
/-- For `P` of prime norm, `P̄ ≠ P`: otherwise its primary generator is real and `p` a square. -/
theorem map_cj_ne : P.map cj ≠ P := by
  obtain ⟨hπ, hPπ⟩ := pgen_maximal P hP3
  intro h
  rw [← hPπ, map_cj_span] at h
  have hcj : cj (pgen P) = pgen P := primary_unique hπ.cj hπ h
  obtain ⟨m, n, hmn⟩ := exists_coords (pgen P)
  have hn : n = 0 := by
    have e : cj (pgen P) - pgen P = -(n : 𝓞 K) * (1 + 2 * ω) := by
      rw [hmn, cj_coords]; push_cast; ring
    rw [hcj, sub_self] at e
    rcases mul_eq_zero.1 e.symm with h1 | h1
    · exact_mod_cast neg_eq_zero.1 h1
    · exact absurd h1 one_add_two_ω_ne_zero
  have hpm : ((p : ℕ) : 𝓞 K) = ((m * m : ℤ) : 𝓞 K) := by
    rw [← hNP, ← hPπ, ← mul_cj_eq_absNorm, hcj, hmn, hn]; push_cast; ring
  have hpm' : (p : ℤ) = m * m := by exact_mod_cast hpm
  have hpa : p = m.natAbs * m.natAbs := by
    have := congrArg Int.natAbs hpm'
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  rw [hpa] at hp
  rcases Nat.prime_mul_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at h1; exact Nat.not_prime_one h1
  · rw [h2] at h1; exact Nat.not_prime_one h1

include hP3 hp hNP in
/-- **Case (C)**, conjugate primes: `χ_{P̄}(π) = χ_P(π̄)` (both are `1`). With `T = −(π + π̄) ∈ ℤ`,
`χ_P(π̄) = χ_P(T) = (π/T)₃` by the coprime-norm law, and `(π/T)₃ = (π̄/T)₃` is fixed by conjugation. -/
theorem recip_conj : chi3 (P.map cj) (pgen P) = chi3 P (pgen (P.map cj)) := by
  have hne := map_cj_ne hP3 hp hNP
  obtain ⟨hπ, hPπ⟩ := pgen_maximal P hP3
  have hpgen' : pgen (P.map cj) = cj (pgen P) := by
    have e : P.map cj = span {cj (pgen P)} := by
      conv_lhs => rw [← hPπ]
      rw [map_cj_span]
    rw [e]; exact pgen_eq hπ.cj
  rw [hpgen']
  generalize pgen P = π at hπ hPπ ⊢
  have hπc := hπ.cj
  have hP'π : P.map cj = span {cj π} := by rw [← hPπ, map_cj_span]
  obtain ⟨m, n, hmn⟩ := exists_coords π
  have hT : ((-(2 * m - n) : ℤ) : 𝓞 K) = -(π + cj (π)) := by
    rw [hmn, cj_coords]; push_cast; ring
  set T : ℤ := -(2 * m - n)
  have hTcj : cj (T : 𝓞 K) = T := map_intCast cj T
  have hTp : Primary (T : 𝓞 K) := by
    unfold Primary at hπ hπc ⊢
    rw [hT, show -(π + cj (π)) - 1 = -(π - 1) - (cj (π) - 1) - 3 by ring]
    exact dvd_sub (dvd_sub (dvd_neg.2 hπ) hπc) (dvd_refl 3)
  have hπP : π ∈ P := hPπ ▸ Ideal.mem_span_singleton_self _
  have hTP : (T : 𝓞 K) ∉ P := by
    intro h
    have hc : cj (π) ∈ P := by
      have hsum : π + cj (π) ∈ P := by
        have := P.neg_mem_iff.2 h; rwa [hT, neg_neg] at this
      have := P.sub_mem hsum hπP
      rwa [add_sub_cancel_left] at this
    apply hne
    have hle : P.map cj ≤ P := by rw [hP'π, Ideal.span_singleton_le_iff_mem]; exact hc
    exact Ideal.IsMaximal.eq_of_le inferInstance hP.ne_top hle
  have hcop : (absNorm (span {π})).Coprime (absNorm (span {(T : 𝓞 K)})) := by
    rw [hPπ, hNP, absNorm_span_intCast]
    apply Nat.Coprime.pow_right
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    apply hTP
    have hpP : ((p : ℕ) : 𝓞 K) ∈ P := hNP ▸ natCast_absNorm_mem
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 hd
    have : (T : 𝓞 K) = (p : 𝓞 K) * (c : 𝓞 K) := by rw [hc]; push_cast; ring
    rw [this]; exact P.mul_mem_right _ hpP
  have hcjπ : cj (π) = -(T : 𝓞 K) + -π := by rw [hT]; ring
  have e1 : chi3 P (cj (π)) = chi3 P T := by
    rw [hcjπ, chi3_add_mem _ (P.neg_mem_iff.2 hπP), chi3_neg hP3]
  have e2 : chi3 P T = cub (π) (span {(T : 𝓞 K)}) := by
    rw [cub_recip_of_coprime_norm hπ hTp hcop, hPπ, cub_prime]
  have hcop' : (absNorm (span {cj (π)})).Coprime (absNorm (span {(T : 𝓞 K)})) := by
    rwa [absNorm_span_cj]
  have e3 : chi3 (P.map cj) T = cub (cj (π)) (span {(T : 𝓞 K)}) := by
    rw [cub_recip_of_coprime_norm hπc hTp hcop', ← hP'π, cub_prime]
  have e4 : cub (cj (π)) (span {(T : 𝓞 K)}) = cub (π) (span {(T : 𝓞 K)}) := by
    unfold cub
    congr 1
    refine Multiset.map_congr rfl fun R hR => ?_
    have := isMaximal_of_mem_nf hR
    have hR3 := three_not_mem_nf hTp hR
    have hTR : (T : 𝓞 K) ∈ R :=
      Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hR) (Ideal.mem_span_singleton_self _)
    rw [hcjπ, add_comm, chi3_add_mem _ (R.neg_mem_iff.2 hTR), chi3_neg hR3]
  have hs : cj (chi3 P T) = chi3 P T := by
    rw [← chi3_map_cj hP3, hTcj, e3, e4, ← e2]
  have hs3 : chi3 P T ^ 3 = 1 := chi3_pow_three hP3 hTP
  have hs1 : chi3 P T = 1 := by
    have h2 : chi3 P T = chi3 P T ^ 2 := by rw [← cj_of_cube hs3, hs]
    linear_combination (1 + chi3 P T) * h2 + hs3
  have lhs : chi3 (P.map cj) (π) = cj (chi3 P (cj (π))) := by
    conv_lhs => rw [← cj_cj (π)]
    exact chi3_map_cj hP3 (cj (π))
  rw [lhs, e1, hs1, map_one]

omit hP hP3 hp hNP

/-- **Cubic reciprocity at primes**: `χ_Q(π_P) = χ_P(π_Q)` for distinct primes prime to `3`. -/
theorem chi3_pgen_recip {P Q : Ideal (𝓞 K)} [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (hP3 : (3 : 𝓞 K) ∉ P) (hQ3 : (3 : 𝓞 K) ∉ Q) (hPQ : P ≠ Q) :
    chi3 Q (pgen P) = chi3 P (pgen Q) := by
  by_cases hc : (absNorm P).Coprime (absNorm Q)
  · exact chi3_pgen_recip_of_coprime hP3 hQ3 hc
  rcases maximal_cases P hP3 with ⟨q, hq, hq2, hPq, hNP⟩ | ⟨p, hp, hp1, hNP⟩ <;>
    rcases maximal_cases Q hQ3 with ⟨q', hq', hq2', hQq, hNQ⟩ | ⟨p', hp', hp1', hNQ⟩
  · exfalso
    by_cases hqq : q = q'
    · subst hqq; exact hPQ (hPq.trans hQq.symm)
    · exact hc (by rw [hNP, hNQ]; exact ((Nat.coprime_primes hq hq').2 hqq).pow 2 2)
  · exfalso
    exact hc (by
      rw [hNP, hNQ]
      exact ((Nat.coprime_primes hq hp').2 (by rintro rfl; omega)).pow_left 2)
  · exfalso
    exact hc (by
      rw [hNP, hNQ]
      exact ((Nat.coprime_primes hp hq').2 (by rintro rfl; omega)).pow_right 2)
  · have hpp : p = p' := by
      by_contra hne
      exact hc (by rw [hNP, hNQ]; exact (Nat.coprime_primes hp hp').2 hne)
    subst hpp
    have hQ' : Q = P.map cj := by
      obtain ⟨hπ, hPπ⟩ := pgen_maximal P hP3
      have hpQ : ((p : ℕ) : 𝓞 K) ∈ Q := hNQ ▸ natCast_absNorm_mem
      rw [← hNP, ← hPπ, ← mul_cj_eq_absNorm] at hpQ
      rcases hQ.isPrime.mem_or_mem hpQ with h | h
      · exfalso; apply hPQ
        have hle : P ≤ Q := by rw [← hPπ, Ideal.span_singleton_le_iff_mem]; exact h
        exact hP.eq_of_le hQ.ne_top hle
      · have hle : P.map cj ≤ Q := by
          rw [← hPπ, map_cj_span, Ideal.span_singleton_le_iff_mem]; exact h
        exact (Ideal.IsMaximal.eq_of_le inferInstance hQ.ne_top hle).symm
    subst hQ'
    exact recip_conj hP3 hp hNP

/-- **Cubic reciprocity** on `ℤ[ω]`: for coprime `a ≡ b ≡ 1 (mod 3)`, `(a/b)₃ = (b/a)₃`. -/
theorem cub_recip {a b : 𝓞 K} (ha : Primary a) (hb : Primary b) (hab : IsCoprime a b) :
    cub a (span {b}) = cub b (span {a}) := by
  apply cub_recip_of_prime ha hb
  intro P hP Q hQ
  have := isMaximal_of_mem_nf hP
  have := isMaximal_of_mem_nf hQ
  refine chi3_pgen_recip (three_not_mem_nf ha hP) (three_not_mem_nf hb hQ) ?_
  rintro rfl
  have haP : a ∈ P :=
    Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self a)
  have hbP : b ∈ P :=
    Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ) (Ideal.mem_span_singleton_self b)
  obtain ⟨u, v, huv⟩ := hab
  apply IsMaximal.ne_top ‹P.IsMaximal›
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u haP) (P.mul_mem_left v hbP)

end Recip

end Eis

#print axioms Eis.maximal_cases
#print axioms Eis.chi3_natCast_inert
#print axioms Eis.chi3_fundamental
#print axioms Eis.recip_split
#print axioms Eis.recip_inert
#print axioms Eis.recip_inert_inert
#print axioms Eis.primary_unique
#print axioms Eis.exists_primary_of_maximal
#print axioms Eis.prod_pgen
#print axioms Eis.cub_recip_of_prime
#print axioms Eis.chi3_pgen_recip_of_coprime
#print axioms Eis.cub_recip_of_coprime_norm
#print axioms Eis.mul_cj_eq_absNorm
#print axioms Eis.chi3_map_cj
#print axioms Eis.map_cj_ne
#print axioms Eis.recip_conj
#print axioms Eis.chi3_pgen_recip
#print axioms Eis.cub_recip
