import EisensteinThetaAssembly

/-! # The quadratic large sieve, part 1: the norm and its symmetry (round 344)

S5e of round 312's plan, part 1 (round 343's S5e-1), after Goldmakher and Louvel's Theorem 1.1 and
Heath-Brown's 1995 proof.

* **The quadratic Gauss sum modulo `4`**: `P₂` depends only on `c` modulo `4` (`P2_add_four`), so
  the normalized sum `φ(c) = G₂(P₂(c), 0)` of round 297, with `S_c(1) = (|σc|/2)·φ(c)`
  (`sqSum_one_eq`), is a function of the class of `c` modulo `4` (`gq4`, `gq4_congr`).
* **Twisted quadratic sums of squarefree moduli** (`sqSum_prod_πP`): for `c = ∏_{P∈A} π_P` and `t`
  prime to `c`, `S_c(t) = (∏_{P∈A} ρ_P(t))·S_c(1)`, from round 298's `sqSum_mul_t` and
  `sqSum_prime`; and `S_c(1) ≠ 0` (`sqSum_prod_one_ne_zero`).
* **Quadratic reciprocity for admissible elements** (`QAdm`: primary, squarefree, norm prime to
  `6`): `(n/k)₂(k/n)₂·φ(k)φ(n) = 2φ(kn)` for coprime `k, n` (`sym2_recip_adm`); `(n/k)₂ = 0`
  otherwise (`sym2_eq_zero_of_not_coprime`); `(k/n)₂² = 1` for coprime `k, n`
  (`sym2_sq_of_coprime`).
* **The duality principle** (`duality`).
* **The norm over balls** (`QBound M N Δ`): rows `k` (the moduli) with `N(k) ≤ M`, columns `n`
  (the arguments) with `N(n) ≤ N`, `Σ_k |Σ_n a(n)(n/k)₂|² ≤ Δ Σ_n |a(n)|²`. Monotone by inclusion
  (`QBound.mono`), in place of Heath-Brown's Lemma 9.
* **Symmetry** (`QBound.symm`, Heath-Brown's Lemma 1): `QBound N M Δ → QBound M N (N((4))·Δ)`, the
  columns split by class modulo `4` and turned into rows by duality.
* **The trivial bound** (`qBound_trivial`): `QBound M N ((2κ+5)²MN)`, from round 310's ideal
  count (`card_adm_le`).
* **The exponent `(E_α)`** (`QExp`), and its transpose `B(M, N) ≪ (MN)^ε(N + M^α)`
  (`QExp.reverse`).
* **`quadLargeSieve_of_exp`**: `QExp 1 → QuadLargeSieve`. Odd columns are admissible
  (`coprime6_of_primary`); an even column is `−2x` with `x` admissible (`qadm_of_neg_two_mul`), and
  `(−2x/k)₂ = (−2/k)₂(x/k)₂`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- `P₂` depends only on `c` modulo `4`. -/
theorem P2_add_four (c u μ : 𝓞 K) : P2 (c + 4 * u) μ = P2 c μ := by
  obtain ⟨n, hn⟩ := exists_re_two_σO_div_δ3 (u * μ * μ)
  have h : Rq (c + 4 * u) μ / 2 = Rq c μ / 2 + n := by
    rw [Rq, Rq, ← hn]
    have : (c + 4 * u) * μ * μ = c * μ * μ + 4 * (u * μ * μ) := by ring
    rw [this, map_add, add_div, Complex.add_re, map_mul σO (4 : 𝓞 K) (u * μ * μ), map_ofNat]
    rw [show (4 : ℂ) * σO (u * μ * μ) / σO δ3 = 2 * (2 * σO (u * μ * μ) / σO δ3) by ring]
    have h2 : (2 * (2 * σO (u * μ * μ) / σO δ3)).re = 2 * (2 * σO (u * μ * μ) / σO δ3).re := by
      simp [Complex.mul_re]
    rw [h2]
    ring
  rw [P2, P2, h, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_neg_intCast,
    mul_one]

/-- The normalized quadratic Gauss sum `φ(c) = G₂(P₂(c), 0)`: `S_c(1) = (|σc|/2)·φ(c)`. -/
def gq4 (c : 𝓞 K) : ℂ := gaussTr 2 (P2 c) 0

theorem gq4_add_four (c u : 𝓞 K) : gq4 (c + 4 * u) = gq4 c := by
  unfold gq4
  congr 1
  funext μ
  exact P2_add_four c u μ

/-- `φ` is a function of the class modulo `4`. -/
theorem gq4_congr {c c' : 𝓞 K}
    (h : Ideal.Quotient.mk (span {(4 : 𝓞 K)}) c = Ideal.Quotient.mk (span {(4 : 𝓞 K)}) c') :
    gq4 c = gq4 c' := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have : c = c' + 4 * u := by linear_combination hu
  rw [this, gq4_add_four]

theorem sqSum_one_eq (c : 𝓞 K) (hc : c ≠ 0) : sqSum c 1 = ((‖σO c‖ / 2 : ℝ) : ℂ) * gq4 c := by
  rw [sqSum_one, quad_gauss c hc]; rfl

theorem two_not_mem_Pr (P : Pr) : (2 : 𝓞 K) ∉ span {πP P} := fun h =>
  h6Pr P (by
    have : (6 : 𝓞 K) = 3 * 2 := by norm_num
    rw [this]; exact Ideal.mul_mem_left _ _ h)

open Classical in
/-- The quadratic symbol modulo `∏_{P∈A} P` through the quadratic characters. -/
theorem sym2_idl (A : Finset Pr) (t : 𝓞 K) :
    sym2 t (idl A) = ∏ P ∈ A, quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) t) := by
  rw [sym2, sym6_idl, chiS, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0)]
  exact congrFun (congrArg DFunLike.coe (chi6_cube (span {πP P}) (h6Pr P))) _

theorem not_mem_Pr_of_ne {P Q : Pr} (h : P ≠ Q) : πP P ∉ span {πP Q} := by
  intro hm
  have hc := isCoprime_πP h
  exact not_isUnit_of_maximal (πP Q) (hc.isUnit_of_dvd' (Ideal.mem_span_singleton.1 hm) dvd_rfl)

theorem prod_not_mem {P : Pr} {A : Finset Pr} (hPA : P ∉ A) :
    ∏ Q ∈ A, πP Q ∉ span {πP P} := by
  have hprime : (span {πP P} : Ideal (𝓞 K)).IsPrime := (instMaxPr P).isPrime
  intro hm
  have := hprime
  obtain ⟨Q, hQ, hQm⟩ := Ideal.IsPrime.prod_mem_iff.1 hm
  exact not_mem_Pr_of_ne (P := Q) (Q := P) (fun e => hPA (e ▸ hQ)) hQm

open Classical in
/-- **The twisted quadratic sum of a squarefree modulus**: for `c = ∏_{P∈A} π_P` and `t` prime to
`c`, `S_c(t) = (∏_{P∈A} ρ_P(t))·S_c(1)`. -/
theorem sqSum_prod_πP (A : Finset Pr) (t : 𝓞 K) (ht : ∀ P ∈ A, t ∉ span {πP P}) :
    sqSum (∏ P ∈ A, πP P) t =
      (∏ P ∈ A, quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) t)) *
        sqSum (∏ P ∈ A, πP P) 1 := by
  induction A using Finset.induction_on generalizing t with
  | empty => simp [sqSum_one_left]
  | insert P A hPA ih =>
    rw [Finset.prod_insert hPA, Finset.prod_insert hPA]
    have hP0 : πP P ≠ 0 := ne_zero_of_maximal (πP P)
    have hA0 : ∏ Q ∈ A, πP Q ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun Q _ => ne_zero_of_maximal (πP Q)
    have hcop : IsCoprime (πP P) (∏ Q ∈ A, πP Q) :=
      IsCoprime.prod_right fun Q hQ => isCoprime_πP fun h => hPA (h ▸ hQ)
    have hprime : (span {πP P} : Ideal (𝓞 K)).IsPrime := (instMaxPr P).isPrime
    have hAP := prod_not_mem hPA
    have htP : t ∉ span {πP P} := ht P (Finset.mem_insert_self P A)
    have hta : t * ∏ Q ∈ A, πP Q ∉ span {πP P} := fun h =>
      (hprime.mem_or_mem h).elim htP hAP
    have ha : 1 * ∏ Q ∈ A, πP Q ∉ span {πP P} := by rwa [one_mul]
    have htA : ∀ Q ∈ A, t * πP P ∉ span {πP Q} := fun Q hQ h =>
      ((instMaxPr Q).isPrime.mem_or_mem h).elim (ht Q (Finset.mem_insert_of_mem hQ))
        (not_mem_Pr_of_ne fun e => hPA (e ▸ hQ))
    have h1A : ∀ Q ∈ A, 1 * πP P ∉ span {πP Q} := fun Q hQ => by
      rw [one_mul]; exact not_mem_Pr_of_ne fun e => hPA (e ▸ hQ)
    rw [sqSum_mul_t _ _ t hP0 hA0 hcop, sqSum_mul_t _ _ 1 hP0 hA0 hcop,
      sqSum_prime (πP P) (two_not_mem_Pr P) _ hta, sqSum_prime (πP P) (two_not_mem_Pr P) _ ha,
      ih (t * πP P) htA, ih (1 * πP P) h1A]
    simp only [one_mul, map_mul, Finset.prod_mul_distrib]
    ring

open Classical in
theorem quadR_ne_zero_of_not_mem (P : Pr) {t : 𝓞 K} (ht : t ∉ span {πP P}) :
    quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) t) ≠ 0 := by
  have hT : Ideal.Quotient.mk (span {πP P}) t ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [MulChar.ringHomComp_apply]
  rcases quadraticChar_dichotomy hT with h | h <;> rw [h] <;> simp

open Classical in
theorem gaussSum_quadR_ne_zero (P : Pr) :
    gaussSum (quadR (𝓞 K ⧸ span {πP P}) ℂ) (ψQ (πP P) (ne_zero_of_maximal (πP P))) ≠ 0 := by
  have hF := ringChar_ne_two_of_two (πP P) (two_not_mem_Pr P)
  have hρ1 : quadR (𝓞 K ⧸ span {πP P}) ℂ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
      (quadraticChar_ne_one hF)
  have hq : (quadR (𝓞 K ⧸ span {πP P}) ℂ).IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hsq := gaussSum_sq hρ1 hq (ψQ_isPrimitive (πP P))
  intro h0
  rw [h0, zero_pow two_ne_zero] at hsq
  have hm1' : (-1 : 𝓞 K) ∉ span {πP P} := fun h =>
    (instMaxPr P).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one.neg)
  have hm1 := quadR_ne_zero_of_not_mem P hm1'
  rw [map_neg, map_one] at hm1
  have hc : (Fintype.card (𝓞 K ⧸ span {πP P}) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_ne_zero hm1 hc hsq.symm

open Classical in
theorem sqSum_prod_one_ne_zero (A : Finset Pr) : sqSum (∏ P ∈ A, πP P) 1 ≠ 0 := by
  induction A using Finset.induction_on with
  | empty => simp [sqSum_one_left]
  | insert P A hPA ih =>
    rw [Finset.prod_insert hPA]
    have hP0 : πP P ≠ 0 := ne_zero_of_maximal (πP P)
    have hcop : IsCoprime (πP P) (∏ Q ∈ A, πP Q) :=
      IsCoprime.prod_right fun Q hQ => isCoprime_πP (by rintro rfl; exact hPA hQ)
    have hA : ∀ Q ∈ A, πP P ∉ span {πP Q} := fun Q hQ =>
      not_mem_Pr_of_ne (by rintro rfl; exact hPA hQ)
    rw [sqSum_mul_t _ _ 1 hP0 (prod_πP_ne_zero A) hcop, one_mul, one_mul,
      sqSum_prime (πP P) (two_not_mem_Pr P) _ (prod_not_mem hPA), sqSum_prod_πP A (πP P) hA]
    exact mul_ne_zero (mul_ne_zero (quadR_ne_zero_of_not_mem P (prod_not_mem hPA))
      (gaussSum_quadR_ne_zero P))
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun Q hQ => quadR_ne_zero_of_not_mem Q (hA Q hQ)) ih)

theorem gq4_prod_ne_zero (A : Finset Pr) : gq4 (∏ P ∈ A, πP P) ≠ 0 := by
  intro h
  apply sqSum_prod_one_ne_zero A
  rw [sqSum_one_eq _ (prod_πP_ne_zero A), h, mul_zero]

open Classical in
/-- **Quadratic reciprocity for squarefree moduli**: for disjoint sets of primes `A, B`, with
`m = ∏_{P∈A} π_P` and `n = ∏_{P∈B} π_P`, `(n/m)₂·(m/n)₂·φ(m)φ(n) = 2φ(mn)`. -/
theorem recip_prod (A B : Finset Pr) (hAB : Disjoint A B) :
    sym2 (∏ P ∈ B, πP P) (idl A) * sym2 (∏ P ∈ A, πP P) (idl B) *
      (gq4 (∏ P ∈ A, πP P) * gq4 (∏ P ∈ B, πP P)) =
      2 * gq4 ((∏ P ∈ A, πP P) * ∏ P ∈ B, πP P) := by
  have hm0 := prod_πP_ne_zero A
  have hn0 := prod_πP_ne_zero B
  have hcop : IsCoprime (∏ P ∈ A, πP P) (∏ P ∈ B, πP P) :=
    IsCoprime.prod_left fun P hP => IsCoprime.prod_right fun Q hQ =>
      isCoprime_πP (by rintro rfl; exact Finset.disjoint_left.1 hAB hP hQ)
  have hBA : ∀ P ∈ A, ∏ Q ∈ B, πP Q ∉ span {πP P} := fun P hP =>
    prod_not_mem (fun h => Finset.disjoint_left.1 hAB hP h)
  have hAB' : ∀ P ∈ B, ∏ Q ∈ A, πP Q ∉ span {πP P} := fun P hP =>
    prod_not_mem (fun h => Finset.disjoint_right.1 hAB hP h)
  have h1 := sqSum_mul_t _ _ 1 hm0 hn0 hcop
  rw [one_mul, one_mul, sqSum_prod_πP A _ hBA, sqSum_prod_πP B _ hAB', ← sym2_idl, ← sym2_idl,
    sqSum_one_eq _ (mul_ne_zero hm0 hn0), sqSum_one_eq _ hm0, sqSum_one_eq _ hn0, map_mul,
    norm_mul] at h1
  have hσm := σO_norm_ne_zero hm0
  have hσn := σO_norm_ne_zero hn0
  push_cast at h1
  have key : ((‖σO (∏ P ∈ A, πP P)‖ : ℂ) * ‖σO (∏ P ∈ B, πP P)‖ / 4) *
      (sym2 (∏ P ∈ B, πP P) (idl A) * sym2 (∏ P ∈ A, πP P) (idl B) *
        (gq4 (∏ P ∈ A, πP P) * gq4 (∏ P ∈ B, πP P))) =
      ((‖σO (∏ P ∈ A, πP P)‖ : ℂ) * ‖σO (∏ P ∈ B, πP P)‖ / 4) *
        (2 * gq4 ((∏ P ∈ A, πP P) * ∏ P ∈ B, πP P)) := by
    linear_combination (-1 : ℂ) * h1
  exact mul_left_cancel₀ (div_ne_zero (mul_ne_zero hσm hσn) (by norm_num)) key

/-- Admissible elements: primary, squarefree, of norm prime to `6`. -/
def QAdm (k : 𝓞 K) : Prop :=
  Primary k ∧ Squarefree (span {k}) ∧ (absNorm (span {k})).Coprime 6

theorem eq_prod_of_adm {k : 𝓞 K} (hk : QAdm k) :
    k = ∏ P ∈ primeSet (span {k}), πP P ∧ span {k} = idl (primeSet (span {k})) := by
  refine ⟨?_, (prod_primeSet hk.2.2 hk.2.1).symm⟩
  conv_lhs => rw [← pgen_eq hk.1]
  exact pgen_eq_prod hk.2.2 hk.2.1

theorem isCoprime_of_forall_not_mem {A : Finset Pr} {n : 𝓞 K}
    (h : ∀ P ∈ A, n ∉ span {πP P}) : IsCoprime (∏ P ∈ A, πP P) n := by
  refine IsCoprime.prod_left fun P hP => ?_
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  refine (instMaxPr P).out.2 _ (lt_of_le_of_ne le_sup_left fun he => h P hP ?_)
  rw [he]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self n)

open Classical in
/-- `(n/m)₂ = 0` unless `n` is prime to `m`. -/
theorem sym2_eq_zero_of_not_coprime {k n : 𝓞 K} (hk : QAdm k) (hcop : ¬ IsCoprime k n) :
    sym2 n (span {k}) = 0 := by
  obtain ⟨hk1, hk2⟩ := eq_prod_of_adm hk
  rw [hk2, sym2_idl]
  by_contra hne
  apply hcop
  rw [hk1]
  refine isCoprime_of_forall_not_mem fun P hP hm => hne ?_
  refine Finset.prod_eq_zero hP ?_
  rw [(Ideal.Quotient.eq_zero_iff_mem).2 hm, MulChar.map_zero]

theorem primeSet_disjoint {k n : 𝓞 K} (hcop : IsCoprime k n) :
    Disjoint (primeSet (span {k})) (primeSet (span {n})) := by
  refine Finset.disjoint_left.2 fun P hk hn => ?_
  have hkP : k ∈ P.1 := by
    have := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primeSet.1 hk))
    exact this (Ideal.mem_span_singleton_self k)
  have hnP : n ∈ P.1 := by
    have := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primeSet.1 hn))
    exact this (Ideal.mem_span_singleton_self n)
  obtain ⟨u, v, huv⟩ := hcop
  exact P.2.1.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.1.add_mem (P.1.mul_mem_left u hkP) (P.1.mul_mem_left v hnP)))

/-- **Quadratic reciprocity for admissible elements**: for `k, n` admissible and coprime,
`(n/k)₂·(k/n)₂·φ(k)φ(n) = 2φ(kn)`, and `φ(k) ≠ 0`. -/
theorem sym2_recip_adm {k n : 𝓞 K} (hk : QAdm k) (hn : QAdm n) (hcop : IsCoprime k n) :
    sym2 n (span {k}) * sym2 k (span {n}) * (gq4 k * gq4 n) = 2 * gq4 (k * n) := by
  obtain ⟨hk1, hk2⟩ := eq_prod_of_adm hk
  obtain ⟨hn1, hn2⟩ := eq_prod_of_adm hn
  have hd := primeSet_disjoint hcop
  rw [hk2, hn2]
  obtain ⟨A, hA⟩ : ∃ A, A = primeSet (span {k}) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = primeSet (span {n}) := ⟨_, rfl⟩
  rw [← hA, ← hB] at hd ⊢
  rw [← hA] at hk1
  rw [← hB] at hn1
  rw [hk1, hn1]
  exact recip_prod A B hd

theorem gq4_ne_zero_of_adm {k : 𝓞 K} (hk : QAdm k) : gq4 k ≠ 0 := by
  rw [(eq_prod_of_adm hk).1]
  exact gq4_prod_ne_zero _

open Classical in
/-- `(k/n)₂² = 1` for coprime admissible `k, n`. -/
theorem sym2_sq_of_coprime {k n : 𝓞 K} (hn : QAdm n) (hcop : IsCoprime k n) :
    sym2 k (span {n}) ^ 2 = 1 := by
  obtain ⟨hn1, hn2⟩ := eq_prod_of_adm hn
  rw [hn2, sym2_idl, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun P hP => quadR_sq_eq_one _ _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  intro hm
  have hnP : n ∈ span {πP P} := by
    rw [(πP_spec P).2]
    have := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primeSet.1 hP))
    exact this (Ideal.mem_span_singleton_self n)
  obtain ⟨u, v, huv⟩ := hcop
  exact (instMaxPr P).ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ (span {πP P}).add_mem ((span {πP P}).mul_mem_left u hm)
      ((span {πP P}).mul_mem_left v hnP)))

/-! ### The duality principle -/

/-- **Duality**: a bound for the transposed bilinear form gives the same bound for the form. -/
theorem duality {ι κ : Type*} (I : Finset ι) (J : Finset κ) (c : ι → κ → ℂ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : ∀ b : ι → ℂ, ∑ j ∈ J, ‖∑ i ∈ I, b i * c i j‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖b i‖ ^ 2)
    (a : κ → ℂ) : ∑ i ∈ I, ‖∑ j ∈ J, a j * c i j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖a j‖ ^ 2 := by
  set S : ℝ := ∑ i ∈ I, ‖∑ j ∈ J, a j * c i j‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB := h fun i => conj (∑ j ∈ J, a j * c i j)
  simp only [norm_conj] at hB
  -- S = Σ_j a_j B_j
  have hsum : (S : ℂ) = ∑ j ∈ J, a j * ∑ i ∈ I, conj (∑ j' ∈ J, a j' * c i j') * c i j := by
    rw [hS]
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.mul_conj', Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcs : S ^ 2 ≤ (∑ j ∈ J, ‖a j‖ ^ 2) * (Δ * S) := by
    have e1 : S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
    calc S ^ 2 = ‖∑ j ∈ J, a j * ∑ i ∈ I, conj (∑ j' ∈ J, a j' * c i j') * c i j‖ ^ 2 := by
          rw [← hsum, ← e1]
      _ ≤ (∑ j ∈ J, ‖a j‖ * ‖∑ i ∈ I, conj (∑ j' ∈ J, a j' * c i j') * c i j‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans ?_) 2
          exact Finset.sum_le_sum fun j _ => (norm_mul _ _).le
      _ ≤ (∑ j ∈ J, ‖a j‖ ^ 2) *
            ∑ j ∈ J, ‖∑ i ∈ I, conj (∑ j' ∈ J, a j' * c i j') * c i j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑ j ∈ J, ‖a j‖ ^ 2) * (Δ * S) :=
          mul_le_mul_of_nonneg_left hB (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · nlinarith

theorem coprime6_multiset (m : Multiset (Ideal (𝓞 K)))
    (h : ∀ P ∈ m, P.IsMaximal ∧ (6 : 𝓞 K) ∉ P) : ((m.map absNorm).prod).Coprime 6 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons P m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact Nat.coprime_mul_iff_left.2 ⟨coprime6_Pr ⟨P, h P (Multiset.mem_cons_self P m)⟩,
      ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)⟩

/-- A primary element prime to `2` has norm prime to `6`. -/
theorem coprime6_of_primary {n : 𝓞 K} (hn : n ≠ 0) (hp : Primary n) (h2 : ¬ (2 : 𝓞 K) ∣ n) :
    (absNorm (span {n})).Coprime 6 := by
  have hI : span {n} ≠ (⊥ : Ideal (𝓞 K)) := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfac : ∀ P ∈ normalizedFactors (span {n} : Ideal (𝓞 K)), (6 : 𝓞 K) ∉ P := by
    intro P hP h6
    have hPmax : P.IsMaximal := isMaximal_of_mem_nf hP
    have hnP : n ∈ P :=
      Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self n)
    have h23 : (2 : 𝓞 K) * 3 ∈ P := by
      rw [show (2 : 𝓞 K) * 3 = 6 by norm_num]; exact h6
    rcases hPmax.isPrime.mem_or_mem h23 with h | h
    · have hle : span {(2 : 𝓞 K)} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 h
      have heq : span {(2 : 𝓞 K)} = P := span_two_isMaximal.eq_of_le hPmax.ne_top hle
      exact h2 (Ideal.mem_span_singleton.1 (heq ▸ hnP))
    · obtain ⟨t, ht⟩ := hp
      have h1 : (1 : 𝓞 K) ∈ P := by
        have : (1 : 𝓞 K) = n - 3 * t := by linear_combination -ht
        rw [this]; exact P.sub_mem hnP (P.mul_mem_right t h)
      exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rw [← Ideal.prod_normalizedFactors_eq_self hI, map_multiset_prod]
  exact coprime6_multiset _ fun P hP => ⟨isMaximal_of_mem_nf hP, hfac P hP⟩

/-- **The quadratic large sieve over balls with constant `Δ`**: for finite sets of admissible rows
`k` (the moduli) with `N(k) ≤ M` and columns `n` (the arguments) with `N(n) ≤ N`,
`Σ_k |Σ_n a(n)(n/k)₂|² ≤ Δ Σ_n |a(n)|²`. -/
def QBound (M N Δ : ℝ) : Prop :=
  ∀ (Ks Ns : Finset (𝓞 K)) (a : 𝓞 K → ℂ),
    (∀ k ∈ Ks, QAdm k ∧ (absNorm (span {k}) : ℝ) ≤ M) →
    (∀ n ∈ Ns, QAdm n ∧ (absNorm (span {n}) : ℝ) ≤ N) →
    ∑ k ∈ Ks, ‖∑ n ∈ Ns, a n * sym2 n (span {k})‖ ^ 2 ≤ Δ * ∑ n ∈ Ns, ‖a n‖ ^ 2

/-- Monotone by inclusion of the balls. -/
theorem QBound.mono {M N Δ M' N' Δ' : ℝ} (h : QBound M' N' Δ) (hM : M ≤ M') (hN : N ≤ N')
    (hΔ : Δ ≤ Δ') : QBound M N Δ' := fun Ks Ns a hK hNs =>
  (h Ks Ns a (fun k hk => ⟨(hK k hk).1, (hK k hk).2.trans hM⟩)
    (fun n hn => ⟨(hNs n hn).1, (hNs n hn).2.trans hN⟩)).trans
    (mul_le_mul_of_nonneg_right hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem norm_sym2_le (a : 𝓞 K) (I : Ideal (𝓞 K)) : ‖sym2 a I‖ ≤ 1 := by
  rw [sym2, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_sym6_le a I)

/-- The reciprocity factor as a ratio of normalized Gauss sums. -/
theorem recip_ratio {k n : 𝓞 K} (hk : QAdm k) (hn : QAdm n) (hcop : IsCoprime k n) :
    2 * gq4 (k * n) / (gq4 k * gq4 n) = sym2 n (span {k}) * sym2 k (span {n}) := by
  rw [div_eq_iff (mul_ne_zero (gq4_ne_zero_of_adm hk) (gq4_ne_zero_of_adm hn)),
    sym2_recip_adm hk hn hcop]

open Classical in
/-- **Symmetry** (Heath-Brown's Lemma 1): `QBound N M Δ → QBound M N (N((4))·Δ)`. The reciprocity
factor depends only on the classes modulo `4`; the columns are split by class and the duality
principle turns rows into columns. -/
theorem QBound.symm {M N Δ : ℝ} (hΔ : 0 ≤ Δ) (h : QBound N M Δ) :
    QBound M N ((absNorm (span {(4 : 𝓞 K)}) : ℝ) * Δ) := by
  intro Ks Ns a hK hN
  refine duality Ks Ns (fun k n => sym2 n (span {k})) (mul_nonneg (Nat.cast_nonneg _) hΔ)
    (fun b => ?_) a
  obtain ⟨q, hq⟩ : ∃ q, q = Ideal.Quotient.mk (span {(4 : 𝓞 K)}) := ⟨_, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := q) (t := Ns.image q)
    (fun n hn => Finset.mem_image_of_mem q hn)]
  have hfib : ∀ y ∈ Ns.image q, ∑ n ∈ Ns with q n = y,
      ‖∑ k ∈ Ks, b k * sym2 n (span {k})‖ ^ 2 ≤ Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by
    intro y hy
    obtain ⟨n₀, hn₀, hy₀⟩ := Finset.mem_image.1 hy
    let w : 𝓞 K → ℂ := fun k => if ∃ n ∈ Ns.filter (fun n => q n = y), IsCoprime k n then
      2 * gq4 (k * n₀) / (gq4 k * gq4 n₀) else 0
    have hcls : ∀ {k n : 𝓞 K}, q n = y →
        2 * gq4 (k * n₀) / (gq4 k * gq4 n₀) = 2 * gq4 (k * n) / (gq4 k * gq4 n) := by
      intro k n hny
      have h1 : gq4 n₀ = gq4 n := gq4_congr (by rw [← hq]; rw [hy₀, hny])
      have h2 : gq4 (k * n₀) = gq4 (k * n) :=
        gq4_congr (by rw [map_mul, map_mul, ← hq, hy₀, hny])
      rw [h1, h2]
    have hw : ∀ k ∈ Ks, ‖w k‖ ≤ 1 := by
      intro k hk
      simp only [w]
      split_ifs with hex
      · obtain ⟨n', hn', hcop'⟩ := hex
        have hn'N := (Finset.mem_filter.1 hn')
        rw [hcls hn'N.2, recip_ratio (hK k hk).1 (hN n' hn'N.1).1 hcop', norm_mul]
        calc ‖sym2 n' (span {k})‖ * ‖sym2 k (span {n'})‖ ≤ 1 * 1 :=
              mul_le_mul (norm_sym2_le _ _) (norm_sym2_le _ _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · rw [norm_zero]; exact zero_le_one
    have heq : ∀ n ∈ Ns.filter (fun n => q n = y), ∀ k ∈ Ks,
        sym2 n (span {k}) = w k * sym2 k (span {n}) := by
      intro n hn k hk
      have hnN := Finset.mem_filter.1 hn
      have hka := (hK k hk).1
      have hna := (hN n hnN.1).1
      by_cases hc : IsCoprime k n
      · have hex : ∃ n ∈ Ns.filter (fun n => q n = y), IsCoprime k n := ⟨n, hn, hc⟩
        simp only [w, hex, ↓reduceIte]
        rw [hcls hnN.2, recip_ratio hka hna hc, mul_assoc, ← sq, sym2_sq_of_coprime hna hc,
          mul_one]
      · rw [sym2_eq_zero_of_not_coprime hka hc,
          sym2_eq_zero_of_not_coprime hna (fun h' => hc h'.symm), mul_zero]
    calc ∑ n ∈ Ns with q n = y, ‖∑ k ∈ Ks, b k * sym2 n (span {k})‖ ^ 2
        = ∑ n ∈ Ns with q n = y, ‖∑ k ∈ Ks, (b k * w k) * sym2 k (span {n})‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          congr 2
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [heq n hn k hk]; ring
      _ ≤ Δ * ∑ k ∈ Ks, ‖b k * w k‖ ^ 2 :=
          h _ Ks (fun k => b k * w k) (fun n hn => hN n (Finset.mem_filter.1 hn).1) hK
      _ ≤ Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hΔ
          rw [norm_mul, mul_pow]
          exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hw k hk))
  have hB0 : 0 ≤ Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 :=
    mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc ∑ y ∈ Ns.image q, ∑ n ∈ Ns with q n = y, ‖∑ k ∈ Ks, b k * sym2 n (span {k})‖ ^ 2
      ≤ ∑ _y ∈ Ns.image q, Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := Finset.sum_le_sum hfib
    _ = ((Ns.image q).card : ℝ) * (Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (absNorm (span {(4 : 𝓞 K)}) : ℝ) * (Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        rw [hq]; exact card_image_mk_le (by norm_num) Ns
    _ = (absNorm (span {(4 : 𝓞 K)}) : ℝ) * Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by ring

/-- At most `idealCount X` admissible elements have norm at most `X`. -/
theorem card_adm_le {Ks : Finset (𝓞 K)} {X : ℝ}
    (hK : ∀ k ∈ Ks, QAdm k ∧ (absNorm (span {k}) : ℝ) ≤ X) : (Ks.card : ℝ) ≤ idealCount X := by
  classical
  have hinj : Set.InjOn (fun k : 𝓞 K => (span {k} : Ideal (𝓞 K))) Ks := by
    intro k hk k' hk' h
    have e1 := pgen_eq (hK k hk).1.1
    have e2 := pgen_eq (hK k' hk').1.1
    simp only at h
    rw [← e1, ← e2, h]
  have hsub : Ks.image (fun k : 𝓞 K => (span {k} : Ideal (𝓞 K))) ⊆ idealsLe X := by
    intro J hJ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hJ
    rw [mem_idealsLe]
    exact ⟨by exact_mod_cast absNorm_pos_of_coprime6 (hK k hk).1.2.2, Nat.le_floor (hK k hk).2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, card_idealsLe] at this
  exact_mod_cast this

/-- **The trivial bound**: `QBound M N (c₀²MN)` with `c₀ = 2κ + 5`. -/
theorem qBound_trivial {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    QBound M N ((2 * kappa + 5) ^ 2 * M * N) := by
  intro Ks Ns a hK hNs
  have hk0 := kappa_pos
  have hcK : (Ks.card : ℝ) ≤ (2 * kappa + 5) * M := (card_adm_le hK).trans (idealCount_le hM)
  have hcN : (Ns.card : ℝ) ≤ (2 * kappa + 5) * N := (card_adm_le hNs).trans (idealCount_le hN)
  have hrow : ∀ k ∈ Ks, ‖∑ n ∈ Ns, a n * sym2 n (span {k})‖ ^ 2 ≤
      (Ns.card : ℝ) * ∑ n ∈ Ns, ‖a n‖ ^ 2 := by
    intro k _
    refine (norm_sum_sq_le_card Ns _).trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun n _ => ?_) (Nat.cast_nonneg _))
    rw [norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_sym2_le _ _))
  have hS : 0 ≤ ∑ n ∈ Ns, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ k ∈ Ks, ‖∑ n ∈ Ns, a n * sym2 n (span {k})‖ ^ 2
      ≤ ∑ _k ∈ Ks, (Ns.card : ℝ) * ∑ n ∈ Ns, ‖a n‖ ^ 2 := Finset.sum_le_sum hrow
    _ = (Ks.card : ℝ) * ((Ns.card : ℝ) * ∑ n ∈ Ns, ‖a n‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * kappa + 5) * M) * (((2 * kappa + 5) * N) * ∑ n ∈ Ns, ‖a n‖ ^ 2) :=
        mul_le_mul hcK (mul_le_mul_of_nonneg_right hcN hS)
          (mul_nonneg (Nat.cast_nonneg _) hS) (by positivity)
    _ = (2 * kappa + 5) ^ 2 * M * N * ∑ n ∈ Ns, ‖a n‖ ^ 2 := by ring

/-- **The exponent `(E_α)`** of Goldmakher and Louvel: `B(M, N) ≪_ε (MN)^ε(M + N^α)`. -/
def QExp (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    QBound M N (C * (M * N) ^ ε * (M + N ^ α))

/-- **The transposed exponent** (Heath-Brown's use of his Lemma 1): `(E_α)` gives
`B(M, N) ≪_ε (MN)^ε(N + M^α)`. -/
theorem QExp.reverse {α : ℝ} (h : QExp α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → QBound M N (C * (M * N) ^ ε * (N + M ^ α)) := by
  obtain ⟨C, hC0, hC⟩ := h ε hε
  refine ⟨(absNorm (span {(4 : 𝓞 K)}) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC0,
    fun M N hM hN => ?_⟩
  have hs := (hC N M hN hM).symm (by positivity)
  rw [mul_comm N M] at hs
  exact hs.mono le_rfl le_rfl (le_of_eq (by ring))

theorem primary_of_neg_two_mul {n : 𝓞 K} (h : Primary (-2 * n)) : Primary n := by
  obtain ⟨t, ht⟩ := h
  exact ⟨n + t, by linear_combination ht⟩

theorem sym2_neg_two_mul (x : 𝓞 K) (I : Ideal (𝓞 K)) :
    sym2 (-2 * x) I = sym2 (-2) I * sym2 x I := by
  rw [sym2, sym2, sym2, sym6_mul_left, mul_pow]

theorem absNorm_neg_two : (absNorm (span {(-2 : 𝓞 K)}) : ℝ) = 4 := by
  rw [Ideal.span_singleton_neg]; exact absNorm_two

/-- An even column `−2x` of the companion paper's Lemma 6.5 gives an admissible `x`. -/
theorem qadm_of_neg_two_mul {x : 𝓞 K} (hp : Primary (-2 * x)) (hsq : Squarefree (span {-2 * x})) :
    QAdm x ∧ 4 * (absNorm (span {x}) : ℝ) = absNorm (span {-2 * x}) := by
  have hspan : span {-2 * x} = span {(-2 : 𝓞 K)} * span {x} :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  have hsqx : Squarefree (span {x}) := by rw [hspan] at hsq; exact hsq.of_mul_right
  have hx0 : x ≠ 0 := by
    intro h0; apply hsqx.ne_zero; rw [h0, Ideal.span_singleton_eq_bot.2 rfl]; rfl
  have h2 : ¬ (2 : 𝓞 K) ∣ x := by
    rintro ⟨y, rfl⟩
    have hdvd : span {(2 : 𝓞 K)} * span {(2 : 𝓞 K)} ∣ span {-2 * (2 * y)} := by
      rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact ⟨-y, by ring⟩
    have hu := hsq _ hdvd
    rw [Ideal.isUnit_iff] at hu
    exact span_two_isMaximal.ne_top hu
  refine ⟨⟨primary_of_neg_two_mul hp, hsqx, coprime6_of_primary hx0 (primary_of_neg_two_mul hp) h2⟩,
    ?_⟩
  rw [hspan, map_mul, Nat.cast_mul, absNorm_neg_two]

/-- **The companion paper's Lemma 6.5 from `(E_1)`**: the columns `n` prime to `2` are admissible;
an even column is `n = −2x` with `x` admissible, and `(n/k)₂ = (−2/k)₂(x/k)₂`. -/
theorem quadLargeSieve_of_exp (h : QExp 1) : QuadLargeSieve := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := h ε hε
  refine ⟨4 * 2 ^ ε * C, fun H U hH hU Ks Ns β hK hNs => ?_⟩
  classical
  have hB := hC H (2 * U) hH (by linarith)
  rw [Real.rpow_one] at hB
  have hKs : ∀ k ∈ Ks, QAdm k ∧ (absNorm (span {k}) : ℝ) ≤ H := fun k hk =>
    ⟨⟨(hK k hk).1, (hK k hk).2.1, (hK k hk).2.2.1⟩, (hK k hk).2.2.2⟩
  have hinj : Set.InjOn (fun x : 𝓞 K => -2 * x)
      ((fun x : 𝓞 K => -2 * x) ⁻¹' ((Ns.filter fun n => (2 : 𝓞 K) ∣ n : Finset (𝓞 K)) : Set (𝓞 K))) :=
    fun x _ y _ hxy => mul_left_cancel₀ (by norm_num) hxy
  obtain ⟨Np, hNp⟩ : ∃ Np, Np = (Ns.filter fun n => (2 : 𝓞 K) ∣ n).preimage (fun x => -2 * x) hinj :=
    ⟨_, rfl⟩
  have hrange : ∀ n ∈ Ns.filter (fun n => (2 : 𝓞 K) ∣ n),
      n ∉ Set.range (fun x : 𝓞 K => -2 * x) → False := by
    intro n hn hnr
    obtain ⟨m, hm⟩ := (Finset.mem_filter.1 hn).2
    exact hnr ⟨-m, by simp only; rw [hm]; ring⟩
  have hpre : ∀ g : 𝓞 K → ℂ, ∑ x ∈ Np, g (-2 * x) =
      ∑ n ∈ Ns.filter (fun n => (2 : 𝓞 K) ∣ n), g n := by
    intro g
    rw [hNp]
    exact Finset.sum_preimage _ _ hinj g fun n hn hnr => (hrange n hn hnr).elim
  have hpreR : ∀ g : 𝓞 K → ℝ, ∑ x ∈ Np, g (-2 * x) =
      ∑ n ∈ Ns.filter (fun n => (2 : 𝓞 K) ∣ n), g n := by
    intro g
    rw [hNp]
    exact Finset.sum_preimage _ _ hinj g fun n hn hnr => (hrange n hn hnr).elim
  have hodd : ∀ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n),
      QAdm n ∧ (absNorm (span {n}) : ℝ) ≤ 2 * U := by
    intro n hn
    obtain ⟨hnN, h2⟩ := Finset.mem_filter.1 hn
    obtain ⟨hp, hsq, -, hle⟩ := hNs n hnN
    have hn0 : n ≠ 0 := by
      intro h0; apply hsq.ne_zero; rw [h0, Ideal.span_singleton_eq_bot.2 rfl]; rfl
    exact ⟨⟨hp, hsq, coprime6_of_primary hn0 hp h2⟩, hle⟩
  have heven : ∀ x ∈ Np, QAdm x ∧ (absNorm (span {x}) : ℝ) ≤ 2 * U := by
    intro x hx
    rw [hNp, Finset.mem_preimage] at hx
    obtain ⟨hp, hsq, -, hle⟩ := hNs _ (Finset.mem_filter.1 hx).1
    obtain ⟨hadm, hnorm⟩ := qadm_of_neg_two_mul hp hsq
    refine ⟨hadm, ?_⟩
    have h0 : 0 ≤ (absNorm (span {x}) : ℝ) := Nat.cast_nonneg _
    linarith
  -- the two halves
  set Δ := C * (H * (2 * U)) ^ ε * (H + 2 * U) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hO := hB Ks _ β hKs hodd
  have hE := hB Ks Np (fun x => β (-2 * x)) hKs heven
  have hsplit : ∀ k ∈ Ks, ‖∑ n ∈ Ns, β n * sym6 n (span {k}) ^ 3‖ ^ 2 ≤
      2 * ‖∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k})‖ ^ 2 +
        2 * ‖∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖ ^ 2 := by
    intro k _
    have e2 : ∑ n ∈ Ns.filter (fun n => (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k}) =
        sym2 (-2) (span {k}) * ∑ x ∈ Np, β (-2 * x) * sym2 x (span {k}) := by
      rw [← hpre (fun n => β n * sym2 n (span {k})), Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sym2_neg_two_mul]; ring
    have e1 : ∑ n ∈ Ns, β n * sym6 n (span {k}) ^ 3 =
        ∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k}) +
          sym2 (-2) (span {k}) * ∑ x ∈ Np, β (-2 * x) * sym2 x (span {k}) := by
      change ∑ n ∈ Ns, β n * sym2 n (span {k}) = _
      rw [← Finset.sum_filter_not_add_sum_filter Ns (fun n => (2 : 𝓞 K) ∣ n), e2]
    rw [e1]
    have hb : ‖sym2 (-2) (span {k}) * ∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖ ≤
        ‖∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (norm_sym2_le _ _)
    have ht := norm_add_le (∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k}))
      (sym2 (-2) (span {k}) * ∑ x ∈ Np, β (-2 * x) * sym2 x (span {k}))
    have hab := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hbc := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [sq_nonneg (‖∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k})‖ -
      ‖sym2 (-2) (span {k}) * ∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖)]
  have hsum : ∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), ‖β n‖ ^ 2 +
      ∑ x ∈ Np, ‖β (-2 * x)‖ ^ 2 = ∑ n ∈ Ns, ‖β n‖ ^ 2 := by
    rw [hpreR fun n => ‖β n‖ ^ 2, Finset.sum_filter_not_add_sum_filter]
  have hΔle : Δ ≤ 2 * 2 ^ ε * C * (H * U) ^ ε * (H + U) := by
    rw [hΔ, show H * (2 * U) = 2 * (H * U) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    have h1 : (0 : ℝ) ≤ C * (2 ^ ε * (H * U) ^ ε) := by positivity
    calc C * (2 ^ ε * (H * U) ^ ε) * (H + 2 * U) ≤ C * (2 ^ ε * (H * U) ^ ε) * (2 * (H + U)) :=
          mul_le_mul_of_nonneg_left (by linarith) h1
      _ = 2 * 2 ^ ε * C * (H * U) ^ ε * (H + U) := by ring
  have hS0 : 0 ≤ ∑ n ∈ Ns, ‖β n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ k ∈ Ks, ‖∑ n ∈ Ns, β n * sym6 n (span {k}) ^ 3‖ ^ 2
      ≤ ∑ k ∈ Ks, (2 * ‖∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k})‖ ^ 2 +
          2 * ‖∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖ ^ 2) := Finset.sum_le_sum hsplit
    _ = 2 * ∑ k ∈ Ks, ‖∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), β n * sym2 n (span {k})‖ ^ 2 +
          2 * ∑ k ∈ Ks, ‖∑ x ∈ Np, β (-2 * x) * sym2 x (span {k})‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (Δ * ∑ n ∈ Ns.filter (fun n => ¬ (2 : 𝓞 K) ∣ n), ‖β n‖ ^ 2) +
          2 * (Δ * ∑ x ∈ Np, ‖β (-2 * x)‖ ^ 2) := by linarith
    _ = 2 * Δ * ∑ n ∈ Ns, ‖β n‖ ^ 2 := by rw [← hsum]; ring
    _ ≤ 2 * (2 * 2 ^ ε * C * (H * U) ^ ε * (H + U)) * ∑ n ∈ Ns, ‖β n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hS0
    _ = 4 * 2 ^ ε * C * (H * U) ^ ε * (H + U) * ∑ n ∈ Ns, ‖β n‖ ^ 2 := by ring

end Eis

end

#print axioms Eis.P2_add_four
#print axioms Eis.gq4_congr
#print axioms Eis.sqSum_prod_πP
#print axioms Eis.gaussSum_quadR_ne_zero
#print axioms Eis.sqSum_prod_one_ne_zero
#print axioms Eis.recip_prod
#print axioms Eis.sym2_recip_adm
#print axioms Eis.sym2_eq_zero_of_not_coprime
#print axioms Eis.sym2_sq_of_coprime
#print axioms Eis.duality
#print axioms Eis.coprime6_of_primary
#print axioms Eis.QBound.symm
#print axioms Eis.card_adm_le
#print axioms Eis.qBound_trivial
#print axioms Eis.QExp.reverse
#print axioms Eis.qadm_of_neg_two_mul
#print axioms Eis.quadLargeSieve_of_exp
