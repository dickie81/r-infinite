import EisensteinDualExcl
import EisensteinPoissonExcl

/-! # The mean square after Poisson summation (round 307)

S4 of round 291's plan, part 7: the first half of the assembly of the companion paper's
Proposition 4.5, as exact identities.

* **Finite sets of primes as squarefree ideals.** For a finite set `A` of primes not containing `6`
  (round 305's `Pr`), `idl A = ∏_{P∈A} P` is squarefree of norm prime to `6` (`idl_squarefree`,
  `idl_coprime6`; `coprime6_Pr`: the residue field of `P` has characteristic `p ∤ 6`). Its primes are
  `A` (`primeSet_idl`), its primary generator is `∏_{P∈A} π_P` (`pgen_idl`), its sextic symbol is
  `χ_A = ∏_{P∈A} χ_P` (`chiS`, `sym6_idl`), and `μ(idl A) = (−1)^{|A|}` (`moebius_idl`). `fsLe Y` is
  the finite set of `A` with `N(idl A) ≤ ⌊Y⌋` (`mem_fsLe`).
* **The family as a finite sum** (`famSum_eq`): `A_Z(u) = Σ_A (−1)^{|A|}·χ_A(u)·W(N(A)/Z)` over
  `A ∈ fsLe ⌈βZ⌉`, for `W` vanishing beyond `β`.
* **The majorant** (`sum_sq_le_majorant`): with round 301's `Φ` (`Φ ≥ 1` on the unit disc and
  `Φ ≥ 0`), `Σ_{z∈T} |g(z)|² ≤ Re Σ_u g(u)ḡ(u)·Φ(u/√H)` when `N(z) ≤ H` on `T`. The sum converges for
  bounded `g` (`summable_mul_Phi`).
* **The expansion over pairs** (`famSum_majorant_eq`): the smoothed mean square of the family is
  `Σ_{A₁,A₂} W(N(A₁)/Z)·W(N(A₂)/Z)·μ(A₁)μ(A₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√H)`.
* **One pair** (`pairSum_poisson`): the paper's (4.14), with its Gauss sums evaluated. Put
  `B = A₁∩A₂`, `C₁ = A₁∖A₂` and `C₂ = A₂∖A₁`. Then `χ_{A₁}χ̄_{A₂} = 1_{(u,B)=1}·F` with
  `F = χ_{C₁}χ̄_{C₂} = ∏_{P∈C₁∪C₂} χ_P^{±1}` (`chiS_mul_conj`, `chiS_mul_conj_disjoint`). Round 303's
  `poisson_excl_Phi` (exclusion `B`, modulus `c = ∏_{C₁∪C₂} π_P`), the Gauss transform of a product
  of nontrivial characters (`gaussTr_chars_mu`, `gaussTr_one_eq_gamF`, from round 295's
  `gaussTr_prod_primes`) and round 304's `paired_gauss` give
  `μ(A₁)μ(A₂)·Σ_u χ_{A₁}χ̄_{A₂}·Φ(u/√H) =
  Σ_{T⊆B} (−1)^{|T|}·2H/(√3·√N(c)·N(d_T))·ā(C₁)a(C₂)Ψ(C₁, C₂)·F(d_T)·Σ_μ F̄(μ)·Φ̂(√(4HN(μ)/(3N(c)N(d_T))))`,
  with `d_T = ∏_{P∈T} π_P` and round 304's paired factor `Ψ` (`pairPsi`).
* `majorant_poisson` combines the last two.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### Finite sets of primes as squarefree ideals -/

theorem Pr_ne_bot (P : Pr) : P.1 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField P.2.1 (RingOfIntegers.not_isField K)

/-- A prime not containing `6` has norm prime to `6`: its residue field has characteristic `p ∤ 6`
and `p^f` elements. -/
theorem coprime6_Pr (P : Pr) : (absNorm P.1).Coprime 6 := by
  have hmax := P.2.1
  let : Field (𝓞 K ⧸ P.1) := Ideal.Quotient.field P.1
  have hfin : Finite (𝓞 K ⧸ P.1) := Ideal.finiteQuotientOfFreeOfNeBot _ (Pr_ne_bot P)
  let : Fintype (𝓞 K ⧸ P.1) := Fintype.ofFinite _
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' (𝓞 K ⧸ P.1)
  have hN : absNorm P.1 = Fintype.card (𝓞 K ⧸ P.1) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h6 : ((6 : ℕ) : 𝓞 K ⧸ P.1) ≠ 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (Ideal.Quotient.mk P.1), Ne,
      Ideal.Quotient.eq_zero_iff_mem]
    exact P.2.2
  have hnd : ¬ p ∣ 6 := fun h => h6 ((CharP.cast_eq_zero_iff _ p 6).2 h)
  rw [hN, hcard]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)

/-- The ideal `∏_{P∈A} P` of a finite set of primes. -/
def idl (A : Finset Pr) : Ideal (𝓞 K) := ∏ P ∈ A, P.1

/-- `χ_A(u) = ∏_{P∈A} χ_P(u)`, the sextic symbol of `u` modulo `∏_{P∈A} P`. -/
def chiS (A : Finset Pr) (u : 𝓞 K) : ℂ :=
  ∏ P ∈ A, chiF πP h6Pr P (Ideal.Quotient.mk (span {πP P}) u)

theorem idl_coprime6 (A : Finset Pr) : (absNorm (idl A)).Coprime 6 := by
  unfold idl
  rw [map_prod]
  exact Nat.Coprime.prod_left fun P _ => coprime6_Pr P

theorem normalizedFactors_idl (A : Finset Pr) :
    normalizedFactors (idl A) = A.val.map Subtype.val := by
  unfold idl
  rw [Finset.prod_eq_multiset_prod]
  refine normalizedFactors_prod_of_prime fun Q hQ => ?_
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.1 hQ
  exact Ideal.prime_of_isPrime (Pr_ne_bot P) P.2.1.isPrime

theorem idl_squarefree (A : Finset Pr) : Squarefree (idl A) := by
  have h0 : idl A ≠ 0 := by
    unfold idl
    exact Finset.prod_ne_zero_iff.2 fun P _ => Pr_ne_bot P
  rw [squarefree_iff_nodup_normalizedFactors h0, normalizedFactors_idl]
  exact A.nodup.map Subtype.val_injective

theorem idl_ne_bot (A : Finset Pr) : idl A ≠ ⊥ := (idl_squarefree A).ne_zero

theorem primeSet_idl (A : Finset Pr) : primeSet (idl A) = A := by
  ext P
  rw [mem_primeSet, normalizedFactors_idl, Multiset.mem_map]
  constructor
  · rintro ⟨Q, hQ, hQP⟩
    rw [Subtype.ext hQP] at hQ
    exact hQ
  · intro hP; exact ⟨P, hP, rfl⟩

theorem idl_primeSet {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    idl (primeSet I) = I := prod_primeSet hI hsq

theorem pgen_idl (A : Finset Pr) : pgen (idl A) = ∏ P ∈ A, πP P := by
  rw [pgen_eq_prod (idl_coprime6 A) (idl_squarefree A), primeSet_idl]

theorem sym6_idl (A : Finset Pr) (u : 𝓞 K) : sym6 u (idl A) = chiS A u := by
  rw [sym6_eq_prod (idl_coprime6 A) (idl_squarefree A), primeSet_idl]; rfl

theorem moebius_idl (A : Finset Pr) : moebius (idl A) = (-1) ^ A.card := by
  rw [(idl_squarefree A).moebius_eq, factors_eq_normalizedFactors, normalizedFactors_idl,
    Multiset.card_map, Finset.card_val]

theorem absNorm_idl (A : Finset Pr) : absNorm (idl A) = ∏ P ∈ A, absNorm P.1 := by
  unfold idl; rw [map_prod]

theorem idl_union {A B : Finset Pr} (h : Disjoint A B) : idl (A ∪ B) = idl A * idl B := by
  unfold idl; rw [Finset.prod_union h]

theorem chiS_union {A B : Finset Pr} (h : Disjoint A B) (u : 𝓞 K) :
    chiS (A ∪ B) u = chiS A u * chiS B u := by
  unfold chiS; rw [Finset.prod_union h]

open Classical in
/-- The squarefree ideals of norm prime to `6` and at most `Y`, as sets of primes. -/
def fsLe (Y : ℝ) : Finset (Finset Pr) :=
  ((idealsLe Y).filter fun I => (absNorm I).Coprime 6 ∧ Squarefree I).image primeSet

theorem mem_fsLe {Y : ℝ} {A : Finset Pr} : A ∈ fsLe Y ↔ absNorm (idl A) ≤ ⌊Y⌋₊ := by
  classical
  unfold fsLe
  rw [Finset.mem_image]
  constructor
  · rintro ⟨I, hI, rfl⟩
    rw [Finset.mem_filter, mem_idealsLe] at hI
    rw [idl_primeSet hI.2.1 hI.2.2]; exact hI.1.2
  · intro h
    refine ⟨idl A, ?_, primeSet_idl A⟩
    rw [Finset.mem_filter, mem_idealsLe]
    refine ⟨⟨?_, h⟩, idl_coprime6 A, idl_squarefree A⟩
    exact Nat.pos_of_ne_zero (by rw [Ne, absNorm_eq_zero_iff]; exact idl_ne_bot A)

open Classical in
/-- `w(𝔞) = (−1)^{|A|}·χ_A(u)` at `𝔞 = ∏_{P∈A} P`. -/
theorem wsym_idl (u : 𝓞 K) (A : Finset Pr) : wsym u (idl A) = (-1 : ℂ) ^ A.card * chiS A u := by
  unfold wsym
  rw [ite_eq_left (idl_coprime6 A), moebius_idl, sym6_idl]; push_cast; ring

open Classical in
/-- **The family as a finite sum over sets of primes**: for `W` vanishing beyond `β` and `Z > 0`,
`A_Z(u) = Σ_A (−1)^{|A|}·χ_A(u)·W(N(A)/Z)` over the sets of primes `A` with `N(A) ≤ ⌈βZ⌉`. -/
theorem famSum_eq {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    (u : 𝓞 K) :
    famSum W Z u = ∑ A ∈ fsLe (⌈β * Z⌉₊ : ℝ), (-1 : ℂ) ^ A.card * chiS A u *
      (W ((absNorm (idl A) : ℝ) / Z) : ℂ) := by
  set M := ⌈β * Z⌉₊ with hM
  unfold famSum
  rw [tsum_eq_Ioc (normSum_wsym_zero u) hW hZ (Nat.le_ceil _)]
  have e1 : ∑ n ∈ Finset.Ioc 0 M, normSum (wsym u) n * (W (n / Z) : ℂ) =
      ∑ I ∈ idealsLe (M : ℝ), wsym u I * (W ((absNorm I : ℝ) / Z) : ℂ) := by
    rw [idealsLe, Nat.floor_natCast, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [normSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I hI => ?_
      rw [mem_ofNorm.1 hI]
    · intro m _ n _ hmn
      rw [Function.onFun, Finset.disjoint_left]
      intro J hm hn
      exact hmn ((mem_ofNorm.1 hm).symm.trans (mem_ofNorm.1 hn))
  rw [e1]
  have e2 : ∑ I ∈ idealsLe (M : ℝ), wsym u I * (W ((absNorm I : ℝ) / Z) : ℂ) =
      ∑ I ∈ (idealsLe (M : ℝ)).filter (fun I => (absNorm I).Coprime 6 ∧ Squarefree I),
        wsym u I * (W ((absNorm I : ℝ) / Z) : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · unfold wsym
      by_cases h6 : (absNorm I).Coprime 6
      · rw [ite_eq_left h6, moebius_of_not_squarefree (fun hs => h ⟨h6, hs⟩)]; simp
      · rw [ite_eq_right h6, zero_mul]
  rw [e2, fsLe, Finset.sum_image]
  · refine Finset.sum_congr rfl fun I hI => ?_
    obtain ⟨-, h6, hsq⟩ := Finset.mem_filter.1 hI
    conv_lhs => rw [← idl_primeSet h6 hsq]
    rw [wsym_idl]
  · intro I hI J hJ hIJ
    obtain ⟨-, h6, hsq⟩ := Finset.mem_filter.1 hI
    obtain ⟨-, h6', hsq'⟩ := Finset.mem_filter.1 hJ
    rw [← idl_primeSet h6 hsq, ← idl_primeSet h6' hsq']
    exact congrArg idl hIJ

/-! ### One pair of columns -/

/-- `χ̄(x) = χ⁻¹(x)` for the sextic characters. -/
theorem conj_chi6 (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hQ6 : (6 : 𝓞 K) ∉ Q) (x : 𝓞 K ⧸ Q) :
    conj (chi6 Q hQ6 x) = (chi6 Q hQ6)⁻¹ x := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, MulChar.map_zero, map_zero]
  · rw [MulChar.inv_apply_eq_inv']
    refine conj_eq_inv_of_norm (norm_eq_one_of_pow_eq_one (chi6_pow_six_of_ne_zero Q hQ6 hx)
      (by norm_num))

open Classical in
/-- `χ(x)·χ̄(x) = [x ≠ 0]`. -/
theorem chi6_mul_conj (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hQ6 : (6 : 𝓞 K) ∉ Q) (x : 𝓞 K ⧸ Q) :
    chi6 Q hQ6 x * conj (chi6 Q hQ6 x) = if x = 0 then 0 else 1 := by
  split_ifs with hx
  · rw [hx, MulChar.map_zero, zero_mul]
  · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_eq_one_of_pow_eq_one (chi6_pow_six_of_ne_zero Q hQ6 hx) (by norm_num)]
    norm_num

theorem mk_πP_eq_zero_iff (P : Pr) (u : 𝓞 K) :
    Ideal.Quotient.mk (span {πP P}) u = 0 ↔ πP P ∣ u := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- The character `χ_{z₁}χ̄_{z₂}` of a pair of disjoint sets of primes, prime by prime. -/
def mixedChar (C1 : Finset Pr) (P : Pr) : MulChar (𝓞 K ⧸ span {πP P}) ℂ :=
  if P ∈ C1 then chiF πP h6Pr P else (chiF πP h6Pr P)⁻¹

open Classical in
/-- **The product of a pair of symbols**: `χ_{A₁}(u)·χ̄_{A₂}(u) = 1_{(u, A₁∩A₂) = 1}·f(u)` with
`f = ∏_{P ∈ C₁∪C₂} χ_P^{±1}`, `C₁ = A₁∖A₂`, `C₂ = A₂∖A₁`. -/
theorem chiS_mul_conj (A1 A2 : Finset Pr) (u : 𝓞 K) :
    chiS A1 u * conj (chiS A2 u) =
      (if ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u then 1 else 0) *
        ∏ P ∈ A1 \ A2 ∪ A2 \ A1, mixedChar (A1 \ A2) P (Ideal.Quotient.mk (span {πP P}) u) := by
  have d3 : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have e1 : chiS A1 u = chiS (A1 ∩ A2) u * chiS (A1 \ A2) u := by
    unfold chiS; rw [Finset.prod_inter_mul_prod_sdiff]
  have e2 : chiS A2 u = chiS (A1 ∩ A2) u * chiS (A2 \ A1) u := by
    unfold chiS; rw [Finset.inter_comm, Finset.prod_inter_mul_prod_sdiff]
  rw [e1, e2, map_mul]
  have hB : chiS (A1 ∩ A2) u * conj (chiS (A1 ∩ A2) u) =
      if ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u then 1 else 0 := by
    unfold chiS
    rw [map_prod, ← Finset.prod_mul_distrib]
    simp_rw [chiF, chi6_mul_conj, mk_πP_eq_zero_iff]
    by_cases h : ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u
    · rw [ite_eq_left h]; exact Finset.prod_eq_one fun P hP => ite_eq_right (h P hP)
    · rw [ite_eq_right h]; push Not at h
      obtain ⟨P, hP, hd⟩ := h
      exact Finset.prod_eq_zero hP (ite_eq_left hd)
  have hC : chiS (A1 \ A2) u * conj (chiS (A2 \ A1) u) =
      ∏ P ∈ A1 \ A2 ∪ A2 \ A1, mixedChar (A1 \ A2) P (Ideal.Quotient.mk (span {πP P}) u) := by
    rw [Finset.prod_union d3]
    unfold chiS
    rw [map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [mixedChar, ite_eq_left hP]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [mixedChar, ite_eq_right (Finset.disjoint_right.1 d3 hP), chiF, conj_chi6]
  calc chiS (A1 ∩ A2) u * chiS (A1 \ A2) u * (conj (chiS (A1 ∩ A2) u) * conj (chiS (A2 \ A1) u))
      = (chiS (A1 ∩ A2) u * conj (chiS (A1 ∩ A2) u)) *
          (chiS (A1 \ A2) u * conj (chiS (A2 \ A1) u)) := by ring
    _ = _ := by rw [hB, hC]

open Classical in
/-- For disjoint `C₁, C₂`: `χ_{C₁}(u)·χ̄_{C₂}(u) = ∏_{P∈C₁∪C₂} χ_P^{±1}(u)`. -/
theorem chiS_mul_conj_disjoint {C1 C2 : Finset Pr} (h : Disjoint C1 C2) (u : 𝓞 K) :
    chiS C1 u * conj (chiS C2 u) =
      ∏ P ∈ C1 ∪ C2, mixedChar C1 P (Ideal.Quotient.mk (span {πP P}) u) := by
  rw [Finset.prod_union h]
  unfold chiS
  rw [map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [mixedChar, ite_eq_left hP]
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [mixedChar, ite_eq_right (Finset.disjoint_right.1 h hP), chiF, conj_chi6]

theorem conj_mixedChar (C1 : Finset Pr) (P : Pr) (x : 𝓞 K ⧸ span {πP P}) :
    conj (mixedChar C1 P x) = (mixedChar C1 P)⁻¹ x := by
  unfold mixedChar
  split_ifs
  · exact conj_chi6 _ _ x
  · rw [inv_inv, ← conj_chi6, Complex.conj_conj]

theorem mixedChar_ne_one (C1 : Finset Pr) (P : Pr) : mixedChar C1 P ≠ 1 := by
  have h : chiF πP h6Pr P ≠ 1 := by
    have := chi6_pow_ne_one (span {πP P}) (h6Pr P) (j := 1) (by simp)
    rwa [pow_one] at this
  unfold mixedChar
  split_ifs
  · exact h
  · exact inv_ne_one.2 h

theorem prod_πP_ne_zero (S : Finset Pr) : ∏ P ∈ S, πP P ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun P _ => ne_zero_of_maximal (πP P)

theorem norm_σO_eq_sqrt (c : 𝓞 K) : ‖σO c‖ = Real.sqrt (absNorm (span {c}) : ℝ) := by
  rw [← normSq_σO, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem σO_norm_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : ((‖σO c‖ : ℝ) : ℂ) ≠ 0 := by
  rw [norm_σO_eq_sqrt, Complex.ofReal_ne_zero, Real.sqrt_ne_zero', Nat.cast_pos]
  exact Nat.pos_of_ne_zero (by rwa [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot])

/-- The Gauss transform is linear in a constant factor. -/
theorem gaussTr_const_mul (c : 𝓞 K) (hc : c ≠ 0) (a : ℂ) (g : 𝓞 K → ℂ) (μ : 𝓞 K) :
    gaussTr c (fun z => a * g z) μ = a * gaussTr c g μ := by
  have : Finite (𝓞 K ⧸ span {c}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  rw [gaussTr, gaussTr, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The Gauss transform of a product of nontrivial characters at `μ`** is `∏_P χ_P⁻¹(μ)` times
the transform at `1` (round 295's `gaussTr_prod_primes` at `μ` and at `1`). -/
theorem gaussTr_chars_mu (S : Finset Pr) (χ : ∀ P : Pr, MulChar (𝓞 K ⧸ span {πP P}) ℂ)
    (hχ : ∀ P ∈ S, χ P ≠ 1) (μ : 𝓞 K) :
    gaussTr (∏ P ∈ S, πP P) (fun z => ∏ P ∈ S, χ P (Ideal.Quotient.mk (span {πP P}) z)) μ =
      (∏ P ∈ S, (χ P)⁻¹ (Ideal.Quotient.mk (span {πP P}) μ)) *
        gaussTr (∏ P ∈ S, πP P) (fun z => ∏ P ∈ S, χ P (Ideal.Quotient.mk (span {πP P}) z)) 1 := by
  rw [gaussTr_prod_primes πP S (hcopPr S) χ hχ μ, gaussTr_prod_primes πP S (hcopPr S) χ hχ 1,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [map_one, MulChar.map_one]; ring

theorem gaussTr_one_eq_gamF (S : Finset Pr) (χ : ∀ P : Pr, MulChar (𝓞 K ⧸ span {πP P}) ℂ) :
    gaussTr (∏ P ∈ S, πP P) (fun z => ∏ P ∈ S, χ P (Ideal.Quotient.mk (span {πP P}) z)) 1 =
      ((‖σO (∏ P ∈ S, πP P)‖ : ℝ) : ℂ) * gamF πP S χ := by
  rw [gamF, mul_div_cancel₀ _ (σO_norm_ne_zero (prod_πP_ne_zero S))]

/-- The paired factor of round 304's `paired_gauss`: `χ_{z₁}(4)⁻¹·χ_{z₂}(4)·γ₃(z₁z₂)`. -/
def pairPsi (C1 C2 : Finset Pr) : ℂ :=
  (∏ P ∈ C1, chiF πP h6Pr P 4)⁻¹ * (∏ P ∈ C2, chiF πP h6Pr P 4) *
    gamF πP (C1 ∪ C2) (fun P => chiF πP h6Pr P ^ 3)

open Classical in
/-- **Poisson summation and the Gauss sums for one pair of columns** (the paper's (4.14), with its
Gauss sums evaluated by round 304's `paired_gauss`). For sets of primes `A₁, A₂` put `B = A₁∩A₂`,
`C₁ = A₁∖A₂`, `C₂ = A₂∖A₁`, `c = ∏_{C₁∪C₂} π_P`, `d_T = ∏_{P∈T} π_P` and `F = χ_{C₁}χ̄_{C₂}`. Then
`μ(A₁)μ(A₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√H)` is
`Σ_{T⊆B} (−1)^{|T|}·2H/(√3·√N(c)·N(d_T))·ā(C₁)a(C₂)Ψ(C₁, C₂)·F(d_T)·Σ_μ F̄(μ)·Φ̂(√(4HN(μ)/(3N(c)N(d_T))))`. -/
theorem pairSum_poisson (H : ℝ) (hH : 0 < H) (A1 A2 : Finset Pr) :
    (-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
      ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
    ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card *
      ((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
        (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
      (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
      (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
      ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
        dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))) := by
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  set c : 𝓞 K := ∏ P ∈ (A1 \ A2 ∪ A2 \ A1), πP P with hc
  set f : 𝓞 K → ℂ :=
    fun u => ∏ P ∈ (A1 \ A2 ∪ A2 \ A1), mixedChar (A1 \ A2) P (Ideal.Quotient.mk (span {πP P}) u) with hf
  have hfF : ∀ u, f u = chiS (A1 \ A2) u * conj (chiS (A2 \ A1) u) := fun u =>
    (chiS_mul_conj_disjoint hd u).symm
  have hper : ∀ z u, f (z + c * u) = f z := by
    intro z u
    simp only [hf]
    refine Finset.prod_congr rfl fun P hP => ?_
    have h0 : Ideal.Quotient.mk (span {πP P}) c = 0 := by
      rw [mk_πP_eq_zero_iff]; exact Finset.dvd_prod_of_mem _ hP
    rw [map_add, map_mul, h0, zero_mul, add_zero]
  have hL : ∀ u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      (if ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u then f u else 0) *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ)) := by
    intro u
    rw [chiS_mul_conj]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul, zero_mul]
  rw [tsum_congr hL, poisson_excl_Phi H hH c (prod_πP_ne_zero _) f hper (A1 ∩ A2) πP
    (fun P _ => ne_zero_of_maximal (πP P)) (hcopPr _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  set d : 𝓞 K := ∏ P ∈ T, πP P with hdd
  set K0 : ℂ := ((‖σO c‖ : ℝ) : ℂ) with hK0
  have hG : ∀ μ, gaussTr c (fun z => f (d * z)) μ =
      f d * conj (f μ) * (K0 * gamF πP (A1 \ A2 ∪ A2 \ A1) (mixedChar (A1 \ A2))) := by
    intro μ
    have e : (fun z => f (d * z)) = fun z => f d * f z := by
      funext z; simp only [hf]; rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun P _ => by rw [map_mul, map_mul]
    rw [e, gaussTr_const_mul c (prod_πP_ne_zero _), gaussTr_chars_mu (A1 \ A2 ∪ A2 \ A1) (mixedChar (A1 \ A2))
      (fun P _ => mixedChar_ne_one (A1 \ A2) P) μ, gaussTr_one_eq_gamF]
    have hconj : ∏ P ∈ (A1 \ A2 ∪ A2 \ A1), (mixedChar (A1 \ A2) P)⁻¹ (Ideal.Quotient.mk (span {πP P}) μ) =
        conj (f μ) := by
      simp only [hf]; rw [map_prod]
      exact Finset.prod_congr rfl fun P _ => (conj_mixedChar (A1 \ A2) P _).symm
    rw [hconj, hK0, hc]
    ring
  simp_rw [hG]
  have hsum : ∑' μ : 𝓞 K, f d * conj (f μ) * (K0 * gamF πP (A1 \ A2 ∪ A2 \ A1) (mixedChar (A1 \ A2))) *
        dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {d}) : ℝ)))) =
      f d * (K0 * gamF πP (A1 \ A2 ∪ A2 \ A1) (mixedChar (A1 \ A2))) *
        ∑' μ : 𝓞 K, conj (f μ) * dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {d}) : ℝ)))) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun μ => by ring
  rw [hsum]
  have hsign : (-1 : ℂ) ^ A1.card * (-1) ^ A2.card = (-1) ^ (A1 \ A2).card * (-1) ^ (A2 \ A1).card := by
    have e1 : A1.card = (A1 ∩ A2).card + (A1 \ A2).card := by
      rw [add_comm]; exact (Finset.card_sdiff_add_card_inter A1 A2).symm
    have e2 : A2.card = (A1 ∩ A2).card + (A2 \ A1).card := by
      rw [add_comm, Finset.inter_comm]; exact (Finset.card_sdiff_add_card_inter A2 A1).symm
    rw [e1, e2, pow_add, pow_add]
    have : ((-1 : ℂ) ^ (A1 ∩ A2).card) * (-1) ^ (A1 ∩ A2).card = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination ((-1 : ℂ) ^ (A1 \ A2).card * (-1) ^ (A2 \ A1).card) * this
  have hpg : (-1 : ℂ) ^ (A1 \ A2).card * (-1) ^ (A2 \ A1).card * gamF πP (A1 \ A2 ∪ A2 \ A1) (mixedChar (A1 \ A2)) =
      conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1) := by
    have := paired_gauss πP h6Pr (A1 \ A2) (A2 \ A1) hd (hcopPr _) (fun P _ => (πP_spec P).1)
    rw [pairPsi]
    calc _ = _ := this
      _ = _ := by ring
  have hK : K0 * (((2 * H / (Real.sqrt 3 * (absNorm (span {c}) : ℝ) *
        (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) =
      (((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {c}) : ℝ) *
        (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) := by
    rw [hK0, norm_σO_eq_sqrt, ← Complex.ofReal_mul]
    congr 1
    have hc0 : (0 : ℝ) < absNorm (span {c}) := by
      exact_mod_cast Nat.pos_of_ne_zero (by
        rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact prod_πP_ne_zero _)
    have hs := Real.mul_self_sqrt hc0.le
    have hs0 : 0 < Real.sqrt (absNorm (span {c}) : ℝ) := Real.sqrt_pos.2 hc0
    have hd0 : (0 : ℝ) < absNorm (span {d}) := by
      exact_mod_cast Nat.pos_of_ne_zero (by
        rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact prod_πP_ne_zero _)
    have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
    calc Real.sqrt (absNorm (span {c}) : ℝ) * (2 * H / (Real.sqrt 3 * (absNorm (span {c}) : ℝ) *
          (absNorm (span {d}) : ℝ)))
        = Real.sqrt (absNorm (span {c}) : ℝ) * (2 * H / (Real.sqrt 3 *
            (Real.sqrt (absNorm (span {c}) : ℝ) * Real.sqrt (absNorm (span {c}) : ℝ)) *
            (absNorm (span {d}) : ℝ))) := by rw [hs]
      _ = _ := by field_simp
  rw [hfF d]
  simp_rw [hfF]
  rw [← hK, hsign, ← hpg]
  ring


/-! ### The majorant and the expansion of the mean square -/

theorem norm_chiS_le (A : Finset Pr) (u : 𝓞 K) : ‖chiS A u‖ ≤ 1 := by
  rw [← sym6_idl]; exact norm_sym6_le u (idl A)

theorem Phi_div_sqrt_eq (H : ℝ) (hH : 0 < H) :
    ∃ F : SchwartzMap ℂ ℂ, ∀ w, F w = Majorant.Phi (w / (Real.sqrt H : ℂ)) := by
  have hsH : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.2 hH
  have hb : ((Real.sqrt H)⁻¹ : ℂ) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact_mod_cast hsH.ne'
  exact ⟨affS Majorant.Phi 0 ((Real.sqrt H)⁻¹ : ℂ) hb, fun w => by
    rw [affS_apply, zero_add, div_eq_inv_mul]⟩

/-- `Σ_u g(u)·Φ(u/√H)` converges for bounded `g`. -/
theorem summable_mul_Phi (H : ℝ) (hH : 0 < H) (g : 𝓞 K → ℂ) {B : ℝ} (hg : ∀ u, ‖g u‖ ≤ B) :
    Summable fun u : 𝓞 K => g u * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) := by
  obtain ⟨F, hF⟩ := Phi_div_sqrt_eq H hH
  refine Summable.of_norm_bounded ((summable_σO F).norm.mul_left B) fun u => ?_
  rw [norm_mul, ← hF]
  exact mul_le_mul_of_nonneg_right (hg u) (norm_nonneg _)

/-- **The majorant** (the first step of the proof of the paper's Proposition 4.5): `Φ ≥ 1` on the
unit disc and `Φ ≥ 0` (round 301), so for `z` with `N(z) ≤ H`,
`Σ_{z∈T} |g(z)|² ≤ Re Σ_u g(u)·ḡ(u)·Φ(u/√H)`. -/
theorem sum_sq_le_majorant (H : ℝ) (hH : 0 < H) (g : 𝓞 K → ℂ) {B : ℝ} (hg : ∀ u, ‖g u‖ ≤ B)
    (T : Finset (𝓞 K)) (hT : ∀ z ∈ T, (absNorm (span {z}) : ℝ) ≤ H) :
    ∑ z ∈ T, ‖g z‖ ^ 2 ≤
      (∑' u : 𝓞 K, g u * conj (g u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hg 0)
  have hgg : ∀ u, ‖g u * conj (g u)‖ ≤ B * B := fun u => by
    rw [norm_mul, RCLike.norm_conj]; exact mul_le_mul (hg u) (hg u) (norm_nonneg _) hB
  have hs := summable_mul_Phi H hH _ hgg
  have hre : ∀ u : 𝓞 K, (g u * conj (g u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re =
      ‖g u‖ ^ 2 * (Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re := fun u => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
  rw [Complex.re_tsum hs]
  simp_rw [hre]
  have hsr : Summable fun u : 𝓞 K =>
      ‖g u‖ ^ 2 * (Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re := by
    refine (Complex.reCLM.summable hs).congr fun u => ?_
    rw [Complex.reCLM_apply, hre]
  have hnn : ∀ u : 𝓞 K, 0 ≤ ‖g u‖ ^ 2 * (Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re :=
    fun u => mul_nonneg (sq_nonneg _) (Majorant.Phi_re_nonneg _)
  calc ∑ z ∈ T, ‖g z‖ ^ 2
      ≤ ∑ z ∈ T, ‖g z‖ ^ 2 * (Majorant.Phi (σO z / (Real.sqrt H : ℂ))).re := by
        refine Finset.sum_le_sum fun z hz => ?_
        have h1 : 1 ≤ (Majorant.Phi (σO z / (Real.sqrt H : ℂ))).re := by
          refine Majorant.one_le_Phi_re _ ?_
          have hsH : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.2 hH
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsH.le, div_le_one hsH,
            norm_σO_eq_sqrt]
          exact Real.sqrt_le_sqrt (hT z hz)
        nlinarith [sq_nonneg ‖g z‖]
    _ ≤ ∑' u : 𝓞 K, ‖g u‖ ^ 2 * (Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re :=
        hsr.sum_le_tsum T (fun u _ => hnn u)

/-- `|A_Z(u)| ≤ Σ_A |W(N(A)/Z)|`, uniformly in `u`. -/
theorem norm_famSum_le {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    (u : 𝓞 K) :
    ‖famSum W Z u‖ ≤ ∑ A ∈ fsLe (⌈β * Z⌉₊ : ℝ), |W ((absNorm (idl A) : ℝ) / Z)| := by
  rw [famSum_eq hW hZ u]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc ‖chiS A u‖ * |W ((absNorm (idl A) : ℝ) / Z)| ≤ 1 * |W ((absNorm (idl A) : ℝ) / Z)| :=
        mul_le_mul_of_nonneg_right (norm_chiS_le A u) (abs_nonneg _)
    _ = _ := one_mul _

/-- **The mean square as a double sum over pairs**: `Σ_u A_Z(u)·Ā_Z(u)·Φ(u/√H)` is
`Σ_{A₁,A₂} W(N(A₁)/Z)·W(N(A₂)/Z)·μ(A₁)μ(A₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√H)`. -/
theorem famSum_majorant_eq {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    (H : ℝ) (hH : 0 < H) :
    ∑' u : 𝓞 K, famSum W Z u * conj (famSum W Z u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A1 ∈ fsLe (⌈β * Z⌉₊ : ℝ), ∑ A2 ∈ fsLe (⌈β * Z⌉₊ : ℝ),
        ((W ((absNorm (idl A1) : ℝ) / Z) * W ((absNorm (idl A2) : ℝ) / Z) : ℝ) : ℂ) *
          ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
            ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))) := by
  set 𝒜 := fsLe (⌈β * Z⌉₊ : ℝ)
  have hexp : ∀ u : 𝓞 K, famSum W Z u * conj (famSum W Z u) *
      Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A1 ∈ 𝒜, ∑ A2 ∈ 𝒜,
        ((W ((absNorm (idl A1) : ℝ) / Z) * W ((absNorm (idl A2) : ℝ) / Z) : ℝ) : ℂ) *
          ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
            (chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)))) := by
    intro u
    rw [famSum_eq hW hZ u, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun A1 _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun A2 _ => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, Complex.conj_ofReal]
    push_cast
    ring
  rw [tsum_congr hexp]
  have hs : ∀ A1 A2 : Finset Pr, Summable fun u : 𝓞 K =>
      ((W ((absNorm (idl A1) : ℝ) / Z) * W ((absNorm (idl A2) : ℝ) / Z) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
          (chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)))) := by
    intro A1 A2
    have hb : ∀ u, ‖chiS A1 u * conj (chiS A2 u)‖ ≤ 1 := fun u => by
      rw [norm_mul, RCLike.norm_conj]
      calc ‖chiS A1 u‖ * ‖chiS A2 u‖ ≤ 1 * 1 :=
            mul_le_mul (norm_chiS_le A1 u) (norm_chiS_le A2 u) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact ((summable_mul_Phi H hH _ hb).mul_left _).mul_left _
  rw [Summable.tsum_finsetSum fun A1 _ => summable_sum fun A2 _ => hs A1 A2]
  refine Finset.sum_congr rfl fun A1 _ => ?_
  rw [Summable.tsum_finsetSum fun A2 _ => hs A1 A2]
  refine Finset.sum_congr rfl fun A2 _ => ?_
  rw [tsum_mul_left, tsum_mul_left]


/-- **The mean square after Poisson summation**: `famSum_majorant_eq` with `pairSum_poisson` in each
pair. -/
theorem majorant_poisson {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    (H : ℝ) (hH : 0 < H) :
    ∑' u : 𝓞 K, famSum W Z u * conj (famSum W Z u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A1 ∈ fsLe (⌈β * Z⌉₊ : ℝ), ∑ A2 ∈ fsLe (⌈β * Z⌉₊ : ℝ),
        ((W ((absNorm (idl A1) : ℝ) / Z) * W ((absNorm (idl A2) : ℝ) / Z) : ℝ) : ℂ) *
        ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card *
          ((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
          (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
          (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
          ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
            dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
              (3 * (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
                (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))) := by
  rw [famSum_majorant_eq hW hZ H hH]
  refine Finset.sum_congr rfl fun A1 _ => Finset.sum_congr rfl fun A2 _ => ?_
  rw [pairSum_poisson H hH A1 A2]

end Eis

end

#print axioms Eis.Pr_ne_bot
#print axioms Eis.coprime6_Pr
#print axioms Eis.idl_coprime6
#print axioms Eis.normalizedFactors_idl
#print axioms Eis.idl_squarefree
#print axioms Eis.idl_ne_bot
#print axioms Eis.primeSet_idl
#print axioms Eis.idl_primeSet
#print axioms Eis.pgen_idl
#print axioms Eis.sym6_idl
#print axioms Eis.moebius_idl
#print axioms Eis.absNorm_idl
#print axioms Eis.idl_union
#print axioms Eis.chiS_union
#print axioms Eis.mem_fsLe
#print axioms Eis.wsym_idl
#print axioms Eis.famSum_eq
#print axioms Eis.conj_chi6
#print axioms Eis.chi6_mul_conj
#print axioms Eis.mk_πP_eq_zero_iff
#print axioms Eis.chiS_mul_conj
#print axioms Eis.chiS_mul_conj_disjoint
#print axioms Eis.conj_mixedChar
#print axioms Eis.mixedChar_ne_one
#print axioms Eis.prod_πP_ne_zero
#print axioms Eis.norm_σO_eq_sqrt
#print axioms Eis.σO_norm_ne_zero
#print axioms Eis.gaussTr_const_mul
#print axioms Eis.gaussTr_chars_mu
#print axioms Eis.gaussTr_one_eq_gamF
#print axioms Eis.pairSum_poisson
#print axioms Eis.norm_chiS_le
#print axioms Eis.Phi_div_sqrt_eq
#print axioms Eis.summable_mul_Phi
#print axioms Eis.sum_sq_le_majorant
#print axioms Eis.norm_famSum_le
#print axioms Eis.famSum_majorant_eq
#print axioms Eis.majorant_poisson
