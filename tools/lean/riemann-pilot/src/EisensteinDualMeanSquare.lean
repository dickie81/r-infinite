import EisensteinPairedGauss
import HalfPlaneMeanSquare

/-! # The dual mean square (round 305)

S4 of round 291's plan, part 5: the objects of the companion paper's Definition 4.3 on ideals, and its
hypothesis (4.12) as the displayed hypothesis `DualMeanSquare ϑ`.

* **The primes prime to `6`** (`Pr`), each with its primary generator `πP` (round 290's `pgen`).
  Distinct primes have coprime generators (`isCoprime_πP`), and `χ_P(z)` is round 300's `chiF` at
  `πP P` (`chiP_eq_chiF`, by transporting `chi6` along `span {πP P} = P`).
* **A squarefree ideal of norm prime to `6` as a set of primes** (`primeSet`): its factor multiset is
  `primeSet I`, each prime once (`normalizedFactors_eq_map`). So `∏_{P∈primeSet I} P = I`, the primary
  generator is `∏ πP P` (`pgen_eq_prod`), and the sextic symbol is `∏ χ_P` (`sym6_eq_prod`). For
  coprime ideals `primeSet (IJ)` is the disjoint union (`primeSet_mul`).
* **The column coefficients on ideals**: `γ_j(𝔫) = Σ_{x mod n} (x/𝔫)₆^j·ψ_n(x)/|σn|` (`gamI`),
  `α(𝔫) = σn/|σn|` (`alphaI`) and the paper's `a_ξ(𝔫) = ᾱ(n)·γ₂(n)·ξ(n)` (`aXi`) for a character
  `ξ` modulo `4`. Through `primeSet` these are round 300's `gamF` and `alphaN` products
  (`gamI_eq_gamF`, `alphaI_eq_prod`).
* **The paper's (4.6)**, `a_ξ(𝔞𝔟) = a_ξ(𝔞)·a_ξ(𝔟)·χ_𝔟(a)⁴` (`aXi_mul`), from round 300's
  `gamF_two_union` (`gamI_two_mul`) and the multiplicativity of `α`, `ξ` and the primary generator.
* **The dual mean square**: the column sum `colSum` with an excluded ideal, and the hypothesis
  `DualMeanSquare ϑ`, the paper's (4.12) with the sum over rows written out.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The primes prime to `6` -/

/-- The primes of `ℤ[ω]` not containing `6`. -/
abbrev Pr : Type := {P : Ideal (𝓞 K) // P.IsMaximal ∧ (6 : 𝓞 K) ∉ P}

noncomputable instance : DecidableEq Pr := Classical.decEq _

/-- The primary generator of a prime prime to `6`. -/
def πP (P : Pr) : 𝓞 K := pgen P.1

theorem πP_spec (P : Pr) : Primary (πP P) ∧ span {πP P} = P.1 := by
  have := P.2.1
  exact pgen_maximal P.1 (three_not_mem_of_six P.1 P.2.2)

instance instMaxPr (P : Pr) : (span {πP P} : Ideal (𝓞 K)).IsMaximal := by
  rw [(πP_spec P).2]; exact P.2.1

theorem h6Pr (P : Pr) : (6 : 𝓞 K) ∉ span {πP P} := by
  rw [(πP_spec P).2]; exact P.2.2

theorem chi6_congr {Q R : Ideal (𝓞 K)} (h : Q = R) [Q.IsMaximal] [R.IsMaximal]
    (hQ6 : (6 : 𝓞 K) ∉ Q) (hR6 : (6 : 𝓞 K) ∉ R) (z : 𝓞 K) :
    chi6 Q hQ6 (Ideal.Quotient.mk Q z) = chi6 R hR6 (Ideal.Quotient.mk R z) := by
  subst h; rfl

/-- `χ_P(z)` through the primary generator. -/
theorem chiP_eq_chiF (P : Pr) (z : 𝓞 K) :
    chiP P.1 z = chiF πP h6Pr P (Ideal.Quotient.mk (span {πP P}) z) := by
  have := P.2.1
  unfold chiP
  rw [dite_eq_left ⟨P.2.1, P.2.2⟩]
  exact chi6_congr (πP_spec P).2.symm _ _ z

/-! ### Squarefree ideals as sets of primes -/

open Classical in
/-- The prime factors of an ideal that are prime to `6`. -/
def primeSet (I : Ideal (𝓞 K)) : Finset Pr :=
  (normalizedFactors I).toFinset.subtype fun P => P.IsMaximal ∧ (6 : 𝓞 K) ∉ P

theorem mem_primeSet {I : Ideal (𝓞 K)} {P : Pr} : P ∈ primeSet I ↔ P.1 ∈ normalizedFactors I := by
  classical
  unfold primeSet
  rw [Finset.mem_subtype, Multiset.mem_toFinset]

/-- For a squarefree `I` of norm prime to `6`, the factor multiset is `primeSet I`, each prime once. -/
theorem normalizedFactors_eq_map {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6)
    (hsq : Squarefree I) :
    normalizedFactors I = (primeSet I).val.map Subtype.val := by
  have hnd : (normalizedFactors I).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hsq.ne_zero).1 hsq
  have hnd' : ((primeSet I).val.map Subtype.val).Nodup :=
    (primeSet I).nodup.map Subtype.val_injective
  refine (Multiset.Nodup.ext hnd hnd').2 fun Q => ⟨fun hQ => ?_, fun hQ => ?_⟩
  · refine Multiset.mem_map.2 ⟨⟨Q, isMaximal_of_factor hQ, six_not_mem_of_factor hI hQ⟩, ?_, rfl⟩
    exact Finset.mem_def.1 (mem_primeSet.2 hQ)
  · obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hQ
    exact mem_primeSet.1 (Finset.mem_def.2 hP)

theorem prod_primeSet {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    ∏ P ∈ primeSet I, P.1 = I := by
  rw [Finset.prod_eq_multiset_prod, ← normalizedFactors_eq_map hI hsq,
    Ideal.prod_normalizedFactors_eq_self hsq.ne_zero]

theorem primary_prod_πP (A : Finset Pr) : Primary (∏ P ∈ A, πP P) := by
  rw [Finset.prod_eq_multiset_prod]
  exact primary_multiset_prod fun x hx => by
    obtain ⟨P, -, rfl⟩ := Multiset.mem_map.1 hx
    exact (πP_spec P).1

/-- **The primary generator of a squarefree ideal** is the product of those of its primes. -/
theorem pgen_eq_prod {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    pgen I = ∏ P ∈ primeSet I, πP P := by
  have hspan : span {∏ P ∈ primeSet I, πP P} = I := by
    rw [← Ideal.prod_span_singleton]
    conv_rhs => rw [← prod_primeSet hI hsq]
    exact Finset.prod_congr rfl fun P _ => (πP_spec P).2
  conv_lhs => rw [← hspan]
  exact pgen_eq (primary_prod_πP _)

/-- **The sextic symbol of a squarefree ideal** through its primes. -/
theorem sym6_eq_prod {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I)
    (z : 𝓞 K) :
    sym6 z I = ∏ P ∈ primeSet I, chiF πP h6Pr P (Ideal.Quotient.mk (span {πP P}) z) := by
  rw [sym6, normalizedFactors_eq_map hI hsq, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  exact Multiset.map_congr rfl fun P _ => chiP_eq_chiF P z


/-- Distinct primes have coprime primary generators. -/
theorem isCoprime_πP {P Q : Pr} (h : P ≠ Q) : IsCoprime (πP P) (πP Q) := by
  rw [← Ideal.isCoprime_span_singleton_iff, (πP_spec P).2, (πP_spec Q).2,
    Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 fun h' => h (Subtype.ext h')

theorem hcopPr (S : Finset Pr) : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (πP i) (πP j) :=
  fun _ _ _ _ h => isCoprime_πP h

/-- `primeSet` of a coprime product is the disjoint union. -/
theorem primeSet_mul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : IsRelPrime I J) :
    primeSet (I * J) = primeSet I ∪ primeSet J ∧ Disjoint (primeSet I) (primeSet J) := by
  refine ⟨Finset.ext fun P => ?_, Finset.disjoint_left.2 fun P hPI hPJ => ?_⟩
  · rw [Finset.mem_union, mem_primeSet, mem_primeSet, mem_primeSet,
      normalizedFactors_mul hI hJ, Multiset.mem_add]
  · have h1 := dvd_of_mem_normalizedFactors (mem_primeSet.1 hPI)
    have h2 := dvd_of_mem_normalizedFactors (mem_primeSet.1 hPJ)
    have hu := h h1 h2
    exact P.2.1.ne_top (Ideal.isUnit_iff.1 hu)

/-! ### The column coefficients on ideals -/

/-- The normalized Gauss sum `γ_j(𝔫) = Σ_{x mod n} (x/𝔫)₆^j·ψ_n(x)/|σn|` of an ideal, with its
primary generator `n`. -/
def gamI (j : ℕ) (I : Ideal (𝓞 K)) : ℂ :=
  gaussTr (pgen I) (fun z => sym6 z I ^ j) 1 / ((‖σO (pgen I)‖ : ℝ) : ℂ)

/-- `α(𝔫) = σn/|σn|` for the primary generator `n`. -/
def alphaI (I : Ideal (𝓞 K)) : ℂ := σO (pgen I) / ((‖σO (pgen I)‖ : ℝ) : ℂ)

theorem gamI_eq_gamF {j : ℕ} (hj : j ≠ 0) {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6)
    (hsq : Squarefree I) :
    gamI j I = gamF πP (primeSet I) (fun P => chiF πP h6Pr P ^ j) := by
  unfold gamI gamF
  rw [pgen_eq_prod hI hsq]
  congr 2
  funext z
  rw [sym6_eq_prod hI hsq, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun P _ => (MulChar.pow_apply' _ hj _).symm

theorem alphaI_eq_prod {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    alphaI I = ∏ P ∈ primeSet I, alphaN (πP P) := by
  unfold alphaI alphaN
  rw [pgen_eq_prod hI hsq, map_prod, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]


open Classical in
/-- **The paper's column coefficient** `a_ξ(𝔫) = ᾱ(n)·γ₂(n)·ξ(n)` for a squarefree ideal `𝔫` of
norm prime to `6` with primary generator `n`, and a character `ξ` modulo `4`; `0` otherwise. -/
def aXi (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if (absNorm I).Coprime 6 ∧ Squarefree I then
    conj (alphaI I) * gamI 2 I * ξ (Ideal.Quotient.mk _ (pgen I))
  else 0

theorem squarefree_mul_of {I J : Ideal (𝓞 K)} (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : IsRelPrime I J) : Squarefree (I * J) := squarefree_mul_iff.2 ⟨h, hsI, hsJ⟩

theorem coprime6_mul {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hJ : (absNorm J).Coprime 6) :
    (absNorm (I * J)).Coprime 6 := by
  rw [map_mul]; exact Nat.coprime_mul_iff_left.2 ⟨hI, hJ⟩

theorem pgen_mul {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsI : Squarefree I)
    (hJ : (absNorm J).Coprime 6) (hsJ : Squarefree J) (h : IsRelPrime I J) :
    pgen (I * J) = pgen I * pgen J := by
  obtain ⟨hu, hd⟩ := primeSet_mul hsI.ne_zero hsJ.ne_zero h
  rw [pgen_eq_prod (coprime6_mul hI hJ) (squarefree_mul_of hsI hsJ h), hu, Finset.prod_union hd,
    ← pgen_eq_prod hI hsI, ← pgen_eq_prod hJ hsJ]

theorem alphaI_mul {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsI : Squarefree I)
    (hJ : (absNorm J).Coprime 6) (hsJ : Squarefree J) (h : IsRelPrime I J) :
    alphaI (I * J) = alphaI I * alphaI J := by
  obtain ⟨hu, hd⟩ := primeSet_mul hsI.ne_zero hsJ.ne_zero h
  rw [alphaI_eq_prod (coprime6_mul hI hJ) (squarefree_mul_of hsI hsJ h), hu, Finset.prod_union hd,
    ← alphaI_eq_prod hI hsI, ← alphaI_eq_prod hJ hsJ]

/-- **`γ₂(𝔞𝔟) = γ₂(𝔞)·γ₂(𝔟)·(a/𝔟)₆⁴`** for coprime squarefree ideals of norm prime to `6`
(round 300's `gamF_two_union`). -/
theorem gamI_two_mul {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsI : Squarefree I)
    (hJ : (absNorm J).Coprime 6) (hsJ : Squarefree J) (h : IsRelPrime I J) :
    gamI 2 (I * J) = gamI 2 I * gamI 2 J * sym6 (pgen I) J ^ 4 := by
  obtain ⟨hu, hd⟩ := primeSet_mul hsI.ne_zero hsJ.ne_zero h
  rw [gamI_eq_gamF two_ne_zero (coprime6_mul hI hJ) (squarefree_mul_of hsI hsJ h), hu,
    gamF_two_union πP h6Pr _ _ hd (hcopPr _) (fun P _ => (πP_spec P).1),
    ← gamI_eq_gamF two_ne_zero hI hsI, ← gamI_eq_gamF two_ne_zero hJ hsJ,
    sym6_eq_prod hJ hsJ, pgen_eq_prod hI hsI, ← Finset.prod_pow]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_prod, map_prod, Finset.prod_pow]

open Classical in
/-- **The paper's `a_ξ(𝔞𝔟) = a_ξ(𝔞)·a_ξ(𝔟)·χ_𝔟(a)⁴`** for coprime squarefree ideals of norm prime
to `6`, with `χ_𝔟(a) = (a/𝔟)₆` for the primary generator `a` of `𝔞`. -/
theorem aXi_mul (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {I J : Ideal (𝓞 K)}
    (hI : (absNorm I).Coprime 6) (hsI : Squarefree I) (hJ : (absNorm J).Coprime 6)
    (hsJ : Squarefree J) (h : IsRelPrime I J) :
    aXi ξ (I * J) = aXi ξ I * aXi ξ J * sym6 (pgen I) J ^ 4 := by
  unfold aXi
  rw [ite_eq_left ⟨coprime6_mul hI hJ, squarefree_mul_of hsI hsJ h⟩, ite_eq_left ⟨hI, hsI⟩,
    ite_eq_left ⟨hJ, hsJ⟩, alphaI_mul hI hsI hJ hsJ h, gamI_two_mul hI hsI hJ hsJ h,
    pgen_mul hI hsI hJ hsJ h, map_mul, map_mul, map_mul]
  ring


/-! ### The dual mean square -/

open Classical in
/-- **The column sum of the dual mean square**, with an excluded ideal `𝔯`:
`Σ_{𝔫 : (𝔫, 𝔯) = 1} a_ξ(𝔫)·(k/𝔫)₆·(f/𝔫)₆⁴·W(N𝔫/X)`, a finite sum since `W` will have compact
support. `𝔯 = 1` gives the paper's sum without exclusion. -/
def colSum (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ) (X : ℝ) (R : Ideal (𝓞 K))
    (k f : 𝓞 K) : ℂ :=
  ∑' I : Ideal (𝓞 K), (if IsRelPrime I R then aXi ξ I else 0) * sym6 k I * sym6 f I ^ 4 *
    W ((absNorm I : ℝ) / X)

/-- **The dual mean-square bound** (the companion paper's hypothesis (4.12) of Proposition 4.5, in
the ranges (4.11), for its dual mean square of Definition 4.3), with `S = {2, 3}`, `ν = 1` and
characters `ξ` modulo `4`:
for every `ε > 0` there is a derivative order `J` such that, for every interval `[α, β] ⊂ (0, ∞)` and
`C ≥ 1`, uniformly in the character `ξ`, the smooth weight `W` supported in `[α, β]` with its first
`J` derivatives bounded by `N`, the scales `D, B, F ≥ 1` with `X = D/(BF)`, and
`0 < 𝓗 ≤ C·D²/(D^{1+ϑ}B²)`, every finite set of rows `(𝔣, k)` with `𝔣` squarefree of norm prime
to `6` in `[F, 2F)` and `0 < N(k) ≤ 𝓗` satisfies
`Σ_{𝔣, k} |Σ_𝔫 a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴W(N𝔫/X)|² ≤ K·N²·D^ε·(XF)²`, `f` the primary generator of `𝔣`.
This is `E(𝓗, X, F; ξ, W) ≪ ‖W‖²_{C^J}·D^ε·XF` with the sum over rows written out. -/
def DualMeanSquare (ϑ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∀ C : ℝ, 1 ≤ C → ∃ Kc : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W x‖ ≤ N) →
      ∀ D B F Hc : ℝ, 1 ≤ D → 1 ≤ B → 1 ≤ F → 0 < Hc →
        Hc ≤ C * D ^ 2 / (D ^ (1 + ϑ) * B ^ 2) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hc) →
        ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W (D / (B * F)) 1 k (pgen f)‖ ^ 2 ≤
          Kc * N ^ 2 * D ^ ε * (D / B) ^ 2

end Eis

end

#print axioms Eis.chiP_eq_chiF
#print axioms Eis.normalizedFactors_eq_map
#print axioms Eis.prod_primeSet
#print axioms Eis.pgen_eq_prod
#print axioms Eis.sym6_eq_prod
#print axioms Eis.isCoprime_πP
#print axioms Eis.primeSet_mul
#print axioms Eis.gamI_eq_gamF
#print axioms Eis.alphaI_eq_prod
#print axioms Eis.pgen_mul
#print axioms Eis.alphaI_mul
#print axioms Eis.gamI_two_mul
#print axioms Eis.aXi_mul
