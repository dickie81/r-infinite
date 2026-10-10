import EisensteinDualMeanSquare
import MellinSeparation

/-! # Removing the exclusion, classes modulo `4`, and two coefficient families (round 306)

S4 of round 291's plan, part 6: three inputs of the companion paper's proof of its Proposition 4.5.

* **Lemma 4.4.** The paper's statement, with its LaTeX rendered as text: "Let `r₀` be the product of
  the primes dividing `r` outside `S`. For `H, X > 0`, `F ≥ 1`, and smooth compactly supported `W`,
  `E_r(H, X, F; ξ, W) ≤ τ_div(r₀)·Σ_{d|r₀} E(H, X/N(d), F·N(d); ξ, W)`." (4.10) Here `𝔯` is
  squarefree of norm prime to `6`, so `𝔯₀ = 𝔯`.
  - `colSum_excl`: inclusion–exclusion over the primes of `𝔯` (`indicator_Pr`), `𝔫 = 𝔡𝔪`
    (`tsum_ideal_dvd_eq`) and the paper's (4.6) for an arbitrary second factor (`aXi_mul_left`) give
    `C_𝔯(X; k, f) = Σ_{𝔡∣𝔯} μ(𝔡)·a_ξ(𝔡)·(k/𝔡)₆·(f/𝔡)₆⁴·C_1(X/N𝔡; k, df)`.
  - `colSum_excl_meanSquare_le`: (4.10) multiplied by its normalisation `XF`. The exterior
    coefficients have modulus at most `1` (`norm_aXi_le`, `norm_sym6_le`), those with `(𝔡, 𝔣) ≠ 1`
    vanish, Cauchy–Schwarz runs over the `2^{ω(𝔯)}` divisors, and `𝔣 ↦ 𝔡𝔣` is injective.
  - `dualMeanSquare_excl`: under `DualMeanSquare ϑ` the bound holds with an excluded `𝔯`, at the cost
    `4^{ω(𝔯)}`. The shifts `(X, F) ↦ (X/N𝔡, F·N𝔡)` keep `XF` and the range of `H`.
* **Classes modulo `4` through characters.** For a finite commutative monoid `M`:
  `Σ_ξ ξ(a) = 0` for a unit `a ≠ 1` (`sum_mulChar_eq_zero`, from Mathlib's
  `exists_apply_ne_one_of_hasEnoughRootsOfUnity`); `1_{x = c} = N⁻¹·Σ_ξ ξ(c⁻¹)ξ(x)`
  (`indicator_eq_sum_mulChar`); and a function `Ψ` of two unit classes is
  `Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂)·ξ₁(x)·ξ₂(y)` (`pair_eq_sum_mulChar`) with `|ĉ| ≤ max |Ψ|`
  (`norm_pairCoeff_le`; a character's values at units have norm `1`, `norm_mulChar_unit`, round
  332). Primary generators of squarefree ideals of norm prime to `6` are prime to
  `2` (`isCoprime_pgen_two`), so their classes modulo `4` are units (`isUnit_mk_four`). With
  `M = ℤ[ω]/4` this expands round 304's paired factor, which depends only on the classes of `z₁, z₂`
  modulo `4` (`pairFactor_eq_of_mod_four`), into products of characters. The paper instead reduces its
  pair factor to a function of one class with its (4.7) and expands that.
* **Two coefficient families** (`MellinSep.bilinear_dual_bound₂`): round 302's `bilinear_dual_bound`
  with coefficient families `a` and `b` on the two columns, each satisfying the mean-square hypothesis
  with the same `M`. Since round 332 it is an instance of `bilinear_dual_bound_of_dilated`
  (`MellinSeparation.lean`), whose AM–GM step combines the dilated bounds of the two families.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-- `(a/𝔪)₆ = 0` if a prime factor of `𝔪` contains `a`. -/
theorem sym6_eq_zero_of_mem {a : 𝓞 K} {I P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I)
    (ha : a ∈ P) : sym6 a I = 0 := by
  unfold sym6
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨P, hP, chiP_eq_zero_of_mem ha⟩)

/-- Two nonzero ideals that are not relatively prime have a common prime factor. -/
theorem exists_common_factor {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ¬ IsRelPrime I J) : ∃ P ∈ normalizedFactors J, P ∣ I := by
  by_contra hno
  push Not at hno
  apply h
  refine WfDvdMonoid.isRelPrime_of_no_irreducible_factors (fun h0 => hI h0.1) fun z hz hzI hzJ => ?_
  obtain ⟨q, hq, hzq⟩ := exists_mem_normalizedFactors_of_dvd hJ hz hzJ
  have hzq' : z = q := associated_iff_eq.1 hzq
  exact hno q hq (hzq' ▸ hzI)

/-- The primary generator of a squarefree ideal of norm prime to `6` generates it. -/
theorem span_pgen {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    span {pgen I} = I := by
  rw [pgen_eq_prod hI hsq, ← Ideal.prod_span_singleton]
  conv_rhs => rw [← prod_primeSet hI hsq]
  exact Finset.prod_congr rfl fun P _ => (πP_spec P).2

open Classical in
/-- **The paper's (4.6) for an arbitrary second factor**: for `𝔡` squarefree of norm prime to `6`
and any ideal `𝔪`, `a_ξ(𝔡𝔪) = a_ξ(𝔡)·a_ξ(𝔪)·(d/𝔪)₆⁴`. Both sides vanish unless `𝔪` is
squarefree, of norm prime to `6` and prime to `𝔡`. -/
theorem aXi_mul_left (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {D M : Ideal (𝓞 K)}
    (hD : (absNorm D).Coprime 6) (hsD : Squarefree D) :
    aXi ξ (D * M) = aXi ξ D * aXi ξ M * sym6 (pgen D) M ^ 4 := by
  by_cases hM : (absNorm M).Coprime 6 ∧ Squarefree M
  · by_cases hrel : IsRelPrime D M
    · exact aXi_mul ξ hD hsD hM.1 hM.2 hrel
    · obtain ⟨P, hP, hPD⟩ := exists_common_factor hsD.ne_zero hM.2.ne_zero hrel
      have hmem : pgen D ∈ P := by
        have h1 : pgen D ∈ D := by
          have := Ideal.mem_span_singleton_self (pgen D)
          rwa [span_pgen hD hsD] at this
        exact Ideal.le_of_dvd hPD h1
      rw [sym6_eq_zero_of_mem hP hmem]
      unfold aXi
      rw [ite_eq_right (fun h => hrel (squarefree_mul_iff.1 h.2).1)]
      ring
  · unfold aXi
    rw [ite_eq_right hM, ite_eq_right]
    · ring
    · intro h
      apply hM
      refine ⟨Nat.Coprime.coprime_dvd_left ?_ h.1, Squarefree.of_mul_right h.2⟩
      rw [map_mul]; exact dvd_mul_left _ _


/-- A product of distinct primes from `Pr` divides `I` iff each does. -/
theorem prod_Pr_dvd_iff (T : Finset Pr) (I : Ideal (𝓞 K)) :
    (∏ P ∈ T, P.1) ∣ I ↔ ∀ P ∈ T, P.1 ∣ I := by
  have h := prod_dvd_iff (T := T.map ⟨Subtype.val, Subtype.val_injective⟩)
    (fun Q hQ => by obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ; exact P.2.1) I
  rw [Finset.prod_map] at h
  simp only [Function.Embedding.coeFn_mk, Finset.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  exact h

open Classical in
/-- **Inclusion–exclusion over primes**: `1_{P ∤ I ∀ P∈S} = Σ_{T⊆S} (−1)^{|T|}·1_{∏_T P ∣ I}`, an
instance of `indicator_forall_not` (round 332) through `prod_Pr_dvd_iff`. -/
theorem indicator_Pr (S : Finset Pr) (I : Ideal (𝓞 K)) :
    (if ∀ P ∈ S, ¬ P.1 ∣ I then (1 : ℂ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (if (∏ P ∈ T, P.1) ∣ I then 1 else 0) := by
  rw [indicator_forall_not S (fun P : Pr => P.1 ∣ I)]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  exact if_congr (prod_Pr_dvd_iff T I).symm rfl rfl

/-- `I` is prime to `R` iff no prime of `R` divides it (for `R` of norm prime to `6`). -/
theorem isRelPrime_iff_primeSet {I R : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hR6 : (absNorm R).Coprime 6)
    (hsR : Squarefree R) : IsRelPrime I R ↔ ∀ P ∈ primeSet R, ¬ P.1 ∣ I := by
  constructor
  · intro h P hP hPI
    have hPR := dvd_of_mem_normalizedFactors (mem_primeSet.1 hP)
    exact P.2.1.ne_top (Ideal.isUnit_iff.1 (h hPI hPR))
  · intro h
    by_contra hrel
    obtain ⟨Q, hQ, hQI⟩ := exists_common_factor hI hsR.ne_zero hrel
    exact h ⟨Q, isMaximal_of_factor hQ, six_not_mem_of_factor hR6 hQ⟩ (mem_primeSet.2 hQ) hQI


open Classical in
/-- `Σ_I 1_{𝔡 ∣ I}·h(I) = Σ_𝔪 h(𝔡𝔪)` over the ideals, for `𝔡 ≠ 0` (`tsum_ite_dvd_eq`, since
round 332). -/
theorem tsum_ideal_dvd_eq (D : Ideal (𝓞 K)) (hD : D ≠ ⊥) (h : Ideal (𝓞 K) → ℂ) :
    ∑' I : Ideal (𝓞 K), (if D ∣ I then h I else 0) = ∑' M : Ideal (𝓞 K), h (D * M) := by
  convert tsum_ite_dvd_eq D (by simpa using hD) h

open Classical in
theorem aXi_bot (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) : aXi ξ ⊥ = 0 := by
  unfold aXi
  rw [ite_eq_right]
  intro h
  have h1 := h.1
  rw [Ideal.absNorm_bot] at h1
  norm_num at h1

/-- The column sums are finite: the summand vanishes outside `idealsLe (βX)`. -/
theorem colSum_summand_eq_zero (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β : ℝ}
    (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X) (c : Ideal (𝓞 K) → ℂ)
    {I : Ideal (𝓞 K)} (hI : I ∉ idealsLe (β * X)) :
    aXi ξ I * c I * W ((absNorm I : ℝ) / X) = 0 := by
  rw [mem_idealsLe] at hI
  by_cases h0 : absNorm I = 0
  · rw [(Ideal.absNorm_eq_zero_iff).1 h0, aXi_bot]; ring
  · have hlt : ⌊β * X⌋₊ < absNorm I := by
      by_contra hle; exact hI ⟨Nat.pos_of_ne_zero h0, not_lt.1 hle⟩
    have hβX : β * X < (absNorm I : ℝ) := by
      by_cases hb : 0 ≤ β * X
      · exact (Nat.floor_lt hb).1 hlt
      · have : (0 : ℝ) ≤ absNorm I := Nat.cast_nonneg _
        linarith
    rw [hW _ (by rw [lt_div_iff₀ hX]; linarith), mul_zero]


/-- A product of primes of `R` is squarefree, of norm prime to `6`, and divides `R`. -/
theorem prod_sub_primeSet {R : Ideal (𝓞 K)} (hR6 : (absNorm R).Coprime 6) (hsR : Squarefree R)
    {T : Finset Pr} (hT : T ⊆ primeSet R) :
    (∏ P ∈ T, P.1) ∣ R ∧ (absNorm (∏ P ∈ T, P.1)).Coprime 6 ∧ Squarefree (∏ P ∈ T, P.1) := by
  have hDR : (∏ P ∈ T, P.1) ∣ R := by
    conv_rhs => rw [← prod_primeSet hR6 hsR]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hT
  exact ⟨hDR, Nat.Coprime.coprime_dvd_left (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hDR)) hR6,
    hsR.squarefree_of_dvd hDR⟩

open Classical in
/-- **Lemma 4.4, the identity** (the paper's proof, before Cauchy–Schwarz): inclusion–exclusion over
the primes of a squarefree `𝔯` of norm prime to `6`, `𝔫 = 𝔡𝔪` and `a_ξ(𝔡𝔪) = a_ξ(𝔡)a_ξ(𝔪)χ_𝔪(d)⁴`
give `colSum_𝔯(k, f) = Σ_{T⊆primes(𝔯)} (−1)^{|T|}·a_ξ(𝔡_T)(k/𝔡_T)₆(f/𝔡_T)₆⁴·colSum_1(k, d_T f)` at
the scale `X/N𝔡_T`, for `𝔡_T = ∏_{P∈T} P` with primary generator `d_T`. -/
theorem colSum_excl (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β : ℝ}
    (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X) {R : Ideal (𝓞 K)}
    (hR6 : (absNorm R).Coprime 6) (hsR : Squarefree R) (k f : 𝓞 K) :
    colSum ξ W X R k f = ∑ T ∈ (primeSet R).powerset, (-1 : ℂ) ^ T.card *
      (aXi ξ (∏ P ∈ T, P.1) * sym6 k (∏ P ∈ T, P.1) * sym6 f (∏ P ∈ T, P.1) ^ 4 *
        colSum ξ W (X / (absNorm (∏ P ∈ T, P.1) : ℝ)) 1 k (pgen (∏ P ∈ T, P.1) * f)) := by
  set h : Ideal (𝓞 K) → ℂ := fun I =>
    aXi ξ I * (sym6 k I * sym6 f I ^ 4) * W ((absNorm I : ℝ) / X) with hh
  have hsupp : ∀ I ∉ idealsLe (β * X), h I = 0 := fun I hI =>
    colSum_summand_eq_zero ξ hW hX (fun I => sym6 k I * sym6 f I ^ 4) hI
  have hpt : ∀ I, (if IsRelPrime I R then aXi ξ I else 0) * sym6 k I * sym6 f I ^ 4 *
      W ((absNorm I : ℝ) / X) =
      ∑ T ∈ (primeSet R).powerset, (-1 : ℂ) ^ T.card * (if (∏ P ∈ T, P.1) ∣ I then h I else 0) := by
    intro I
    have e2 : (if IsRelPrime I R then aXi ξ I else 0) * sym6 k I * sym6 f I ^ 4 *
        W ((absNorm I : ℝ) / X) = (if IsRelPrime I R then (1 : ℂ) else 0) * h I := by
      simp only [hh]; split_ifs <;> ring
    by_cases hI0 : I = ⊥
    · have hb : h I = 0 := by simp only [hh, hI0, aXi_bot, zero_mul]
      rw [e2, hb, mul_zero]
      symm
      exact Finset.sum_eq_zero fun T _ => by simp
    · have e := indicator_Pr (primeSet R) I
      have hiff := isRelPrime_iff_primeSet hI0 hR6 hsR
      have e' : (if IsRelPrime I R then (1 : ℂ) else 0) =
          (if ∀ P ∈ primeSet R, ¬ P.1 ∣ I then (1 : ℂ) else 0) := by
        by_cases hr : IsRelPrime I R
        · rw [ite_eq_left hr, ite_eq_left (hiff.1 hr)]
        · rw [ite_eq_right hr, ite_eq_right (fun h' => hr (hiff.2 h'))]
      rw [e2, e', e, Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs <;> ring
  have hsum : ∀ T ∈ (primeSet R).powerset, Summable fun I =>
      (-1 : ℂ) ^ T.card * (if (∏ P ∈ T, P.1) ∣ I then h I else 0) := by
    intro T _
    refine summable_of_ne_finset_zero (s := idealsLe (β * X)) fun I hI => ?_
    rw [hsupp I hI]; simp
  unfold colSum
  rw [tsum_congr hpt, Summable.tsum_finsetSum hsum]
  refine Finset.sum_congr rfl fun T hT => ?_
  obtain ⟨-, hD6, hDsq⟩ := prod_sub_primeSet hR6 hsR (Finset.mem_powerset.1 hT)
  set D := ∏ P ∈ T, P.1 with hD
  have hD0 : D ≠ ⊥ := hDsq.ne_zero
  have hND : (absNorm D : ℝ) ≠ 0 := by
    have : absNorm D ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast this
  rw [tsum_mul_left]
  congr 1
  rw [tsum_ideal_dvd_eq D hD0 h, ← tsum_mul_left]
  refine tsum_congr fun M => ?_
  rw [ite_eq_left isRelPrime_one_right]
  simp only [hh]
  rw [aXi_mul_left ξ hD6 hDsq]
  by_cases hM0 : M = ⊥
  · rw [hM0, aXi_bot]; ring
  · rw [sym6_mul_right k hD0 hM0, sym6_mul_right f hD0 hM0, sym6_mul_left (pgen D) f M, map_mul,
      Nat.cast_mul]
    have hw : ((absNorm D : ℝ) * absNorm M) / X = (absNorm M : ℝ) / (X / absNorm D) := by
      field_simp
    rw [hw]
    ring


/-! ### Norm bounds -/

/-- A character of a monoid with finitely many units has values of norm `1` at the units: they are
roots of unity (round 332). -/
theorem norm_mulChar_unit {M : Type*} [CommMonoid M] [Finite Mˣ] (ξ : MulChar M ℂ) (u : Mˣ) :
    ‖ξ (u : M)‖ = 1 :=
  norm_eq_one_of_pow_eq_one (by rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
    Units.val_one, map_one]) (orderOf_pos u).ne'

/-- A character of `ℤ[ω]/4` has values of norm at most `1`. -/
theorem norm_xi_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) :
    ‖ξ x‖ ≤ 1 := by
  have : Finite (𝓞 K ⧸ span {(4 : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact (norm_mulChar_unit ξ u).le
  · rw [MulChar.map_nonunit ξ hx, norm_zero]; exact zero_le_one

open Classical in
theorem norm_chiP_le (P : Ideal (𝓞 K)) (a : 𝓞 K) : ‖chiP P a‖ ≤ 1 := by
  by_cases h : P.IsMaximal ∧ (6 : 𝓞 K) ∉ P
  · have h6 := chiP_pow_six h.1 h.2 a
    have hn : ‖chiP P a‖ ^ 6 ≤ 1 := by
      rw [← norm_pow, h6]; split_ifs <;> simp
    by_contra hlt
    push Not at hlt
    have : 1 < ‖chiP P a‖ ^ 6 := one_lt_pow₀ hlt (by norm_num)
    linarith
  · unfold chiP; rw [dite_eq_right_iff.2 fun h' => absurd h' h, norm_zero]; exact zero_le_one

theorem norm_sym6_le (a : 𝓞 K) (I : Ideal (𝓞 K)) : ‖sym6 a I‖ ≤ 1 := by
  unfold sym6
  induction normalizedFactors I using Multiset.induction_on with
  | empty => simp
  | cons P m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    calc ‖chiP P a‖ * ‖(Multiset.map (fun P => chiP P a) m).prod‖ ≤ 1 * 1 :=
          mul_le_mul (norm_chiP_le P a) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

open Classical in
theorem norm_aXi_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (I : Ideal (𝓞 K)) :
    ‖aXi ξ I‖ ≤ 1 := by
  unfold aXi
  split_ifs with h
  · have hα : ‖alphaI I‖ = 1 := by
      rw [alphaI_eq_prod h.1 h.2, norm_prod]
      exact Finset.prod_eq_one fun P _ => norm_alphaN (πP P)
    have hγ : ‖gamI 2 I‖ = 1 := by
      rw [gamI_eq_gamF two_ne_zero h.1 h.2]
      exact norm_gamF πP _ (hcopPr _) _ (fun P _ => chi6_pow_ne_one _ (h6Pr P) (by norm_num))
        (fun P _ => chiF_pow_pow_six πP h6Pr P 2)
    rw [norm_mul, norm_mul, RCLike.norm_conj, hα, hγ, one_mul, one_mul]
    exact norm_xi_le ξ _
  · rw [norm_zero]; exact zero_le_one

/-! ### Lemma 4.4, the inequality -/

open Classical in
/-- **Lemma 4.4** (the paper's (4.10), multiplied by its normalisation `XF`): removing the exclusion
`(𝔫, 𝔯) = 1` from the column sums costs the divisor count of `𝔯`. For rows `𝔣` squarefree of norm
prime to `6`, `Σ_𝔣 Σ_k |C_𝔯(X; k, f)|² ≤ τ(𝔯)·Σ_{𝔡 ∣ 𝔯} Σ_{𝔣' ∈ 𝔡·{𝔣 : (𝔡, 𝔣) = 1}} Σ_k
|C_1(X/N𝔡; k, f')|²`, with `τ(𝔯) = 2^{ω(𝔯)}` and the divisors `𝔡 = ∏_{P∈S} P` for `S ⊆ primes(𝔯)`.
The terms with `(𝔡, 𝔣) ≠ 1` vanish (their factor `(f/𝔡)₆⁴` is `0`), the rest have exterior coefficient
of modulus at most `1`, and `f ↦ df` is injective. -/
theorem colSum_excl_meanSquare_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β : ℝ}
    (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X) {R : Ideal (𝓞 K)}
    (hR6 : (absNorm R).Coprime 6) (hsR : Squarefree R) (Fs : Finset (Ideal (𝓞 K)))
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f) (T : Finset (𝓞 K)) :
    ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W X R k (pgen f)‖ ^ 2 ≤
      2 ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset,
        ∑ f ∈ (Fs.filter (IsRelPrime (∏ P ∈ S, P.1))).image ((∏ P ∈ S, P.1) * ·),
          ∑ k ∈ T, ‖colSum ξ W (X / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen f)‖ ^ 2 := by
  set g : Finset Pr → Ideal (𝓞 K) → 𝓞 K → ℝ := fun S f k =>
    if IsRelPrime (∏ P ∈ S, P.1) f then
      ‖colSum ξ W (X / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen ((∏ P ∈ S, P.1) * f))‖ else 0
    with hg
  have hpt : ∀ f ∈ Fs, ∀ k : 𝓞 K, ‖colSum ξ W X R k (pgen f)‖ ^ 2 ≤
      2 ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset, g S f k ^ 2 := by
    intro f hf k
    obtain ⟨hf6, hfsq⟩ := hFs f hf
    have hS : ∀ S ∈ (primeSet R).powerset,
        ‖(-1 : ℂ) ^ S.card * (aXi ξ (∏ P ∈ S, P.1) * sym6 k (∏ P ∈ S, P.1) *
          sym6 (pgen f) (∏ P ∈ S, P.1) ^ 4 *
          colSum ξ W (X / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen (∏ P ∈ S, P.1) * pgen f))‖ ≤
        g S f k := by
      intro S hS
      obtain ⟨-, hD6, hDsq⟩ := prod_sub_primeSet hR6 hsR (Finset.mem_powerset.1 hS)
      simp only [hg]
      split_ifs with hrel
      · rw [← pgen_mul hD6 hDsq hf6 hfsq hrel, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
          norm_pow, norm_neg, norm_one, one_pow, one_mul]
        have h1 := norm_aXi_le ξ (∏ P ∈ S, P.1)
        have h2 := norm_sym6_le k (∏ P ∈ S, P.1)
        have h3 : ‖sym6 (pgen f) (∏ P ∈ S, P.1)‖ ^ 4 ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) (norm_sym6_le _ _)
        calc ‖aXi ξ (∏ P ∈ S, P.1)‖ * ‖sym6 k (∏ P ∈ S, P.1)‖ *
              ‖sym6 (pgen f) (∏ P ∈ S, P.1)‖ ^ 4 *
              ‖colSum ξ W (X / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen ((∏ P ∈ S, P.1) * f))‖
            ≤ 1 * 1 * 1 *
              ‖colSum ξ W (X / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen ((∏ P ∈ S, P.1) * f))‖ := by
              gcongr
          _ = _ := by ring
      · have hrel' : ¬ IsRelPrime f (∏ P ∈ S, P.1) := fun h => hrel h.symm
        obtain ⟨P, hP, hPf⟩ := exists_common_factor hfsq.ne_zero hDsq.ne_zero hrel'
        have hmem : pgen f ∈ P := by
          refine Ideal.le_of_dvd hPf ?_
          have := Ideal.mem_span_singleton_self (pgen f)
          rwa [span_pgen hf6 hfsq] at this
        rw [sym6_eq_zero_of_mem hP hmem]
        simp
    rw [colSum_excl ξ hW hX hR6 hsR]
    have hg0 : ∀ S ∈ (primeSet R).powerset, 0 ≤ g S f k := fun S _ => by
      simp only [hg]; split_ifs <;> simp
    calc _ ≤ (∑ S ∈ (primeSet R).powerset, g S f k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (Finset.sum_le_sum hS)) 2
      _ ≤ ((primeSet R).powerset.card : ℝ) * ∑ S ∈ (primeSet R).powerset, g S f k ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by rw [Finset.card_powerset]; push_cast; rfl
  calc ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W X R k (pgen f)‖ ^ 2
      ≤ ∑ f ∈ Fs, ∑ k ∈ T, 2 ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset, g S f k ^ 2 :=
        Finset.sum_le_sum fun f hf => Finset.sum_le_sum fun k _ => hpt f hf k
    _ = 2 ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset, ∑ f ∈ Fs, ∑ k ∈ T, g S f k ^ 2 := by
        simp_rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm (s := (primeSet R).powerset)]
        exact Finset.sum_congr rfl fun f _ => Finset.sum_comm
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun S hS => ?_
        obtain ⟨-, -, hDsq⟩ := prod_sub_primeSet hR6 hsR (Finset.mem_powerset.1 hS)
        rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hDsq.ne_zero hab),
          Finset.sum_filter]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [hg]
        by_cases hrel : IsRelPrime (∏ P ∈ S, P.1) f
        · simp [hrel]
        · simp [hrel]

open Classical in
/-- **Lemma 4.4 under the hypothesis (4.12)**: if the dual mean square holds without exclusion, it
holds with an excluded squarefree `𝔯` of norm prime to `6`, at the cost `4^{ω(𝔯)}` (the paper's
`τ(𝔯)·Σ_{𝔡∣𝔯}`). The shifts `(X, F) ↦ (X/N𝔡, F·N𝔡)` keep `XF = D/B` and the range of `H`. -/
theorem dualMeanSquare_excl {ϑ : ℝ} (hDM : DualMeanSquare ϑ) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∀ C : ℝ, 1 ≤ C → ∃ Kc : ℝ,
      ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
        (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W x‖ ≤ N) →
        ∀ D B F Hc : ℝ, 1 ≤ D → 1 ≤ B → 1 ≤ F → 0 < Hc →
          Hc ≤ C * D ^ 2 / (D ^ (1 + ϑ) * B ^ 2) →
        ∀ R : Ideal (𝓞 K), (absNorm R).Coprime 6 → Squarefree R →
        ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
          (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
            (absNorm f : ℝ) < 2 * F) →
          (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hc) →
          ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W (D / (B * F)) R k (pgen f)‖ ^ 2 ≤
            4 ^ (primeSet R).card * (Kc * N ^ 2 * D ^ ε * (D / B) ^ 2) := by
  intro ε hε
  obtain ⟨J, hJ⟩ := hDM ε hε
  refine ⟨J, fun α β hα C hC => ?_⟩
  obtain ⟨Kc, hKc⟩ := hJ α β hα C hC
  refine ⟨Kc, fun ξ W hW hsupp N hN D B F Hc hD1 hB1 hF1 hHc0 hHc R hR6 hsR Fs T hFs hT => ?_⟩
  have hX : 0 < D / (B * F) := by positivity
  refine (colSum_excl_meanSquare_le ξ (fun x hx => hsupp x (Or.inr hx)) hX hR6 hsR Fs
    (fun f hf => ⟨(hFs f hf).1, (hFs f hf).2.1⟩) T).trans ?_
  have hterm : ∀ S ∈ (primeSet R).powerset,
      ∑ f ∈ (Fs.filter (IsRelPrime (∏ P ∈ S, P.1))).image ((∏ P ∈ S, P.1) * ·),
        ∑ k ∈ T, ‖colSum ξ W (D / (B * F) / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen f)‖ ^ 2 ≤
      Kc * N ^ 2 * D ^ ε * (D / B) ^ 2 := by
    intro S hS
    obtain ⟨-, hD6, hDsq⟩ := prod_sub_primeSet hR6 hsR (Finset.mem_powerset.1 hS)
    have hN1 : (1 : ℝ) ≤ absNorm (∏ P ∈ S, P.1) := by
      have : absNorm (∏ P ∈ S, P.1) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hDsq.ne_zero
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    rw [div_div, mul_assoc]
    refine hKc ξ W hW hsupp N hN D B (F * absNorm (∏ P ∈ S, P.1)) Hc hD1 hB1
      (one_le_mul_of_one_le_of_one_le hF1 hN1) hHc0 hHc _ T ?_ hT
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
    rw [Finset.mem_filter] at hf
    obtain ⟨hf6, hfsq, hFl, hFu⟩ := hFs f hf.1
    refine ⟨coprime6_mul hD6 hf6, squarefree_mul_of hDsq hfsq hf.2, ?_, ?_⟩
    · rw [map_mul, Nat.cast_mul]; nlinarith
    · rw [map_mul, Nat.cast_mul]; nlinarith
  calc (2 : ℝ) ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset,
        ∑ f ∈ (Fs.filter (IsRelPrime (∏ P ∈ S, P.1))).image ((∏ P ∈ S, P.1) * ·),
          ∑ k ∈ T, ‖colSum ξ W (D / (B * F) / (absNorm (∏ P ∈ S, P.1) : ℝ)) 1 k (pgen f)‖ ^ 2
      ≤ 2 ^ (primeSet R).card * ∑ S ∈ (primeSet R).powerset, Kc * N ^ 2 * D ^ ε * (D / B) ^ 2 := by
        gcongr with S hS
        exact hterm S hS
    _ = 4 ^ (primeSet R).card * (Kc * N ^ 2 * D ^ ε * (D / B) ^ 2) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, ← mul_assoc]
        push_cast
        rw [← mul_pow]
        norm_num


/-! ### Classes modulo `4` through characters -/

section CharExpand

variable {M : Type*} [CommMonoid M] [Finite M]

/-- **Dual orthogonality**: `Σ_ξ ξ(a) = 0` over the complex characters of a finite commutative monoid,
for a unit `a ≠ 1` (Mathlib's `exists_apply_ne_one_of_hasEnoughRootsOfUnity` supplies a character
with `ξ₀(a) ≠ 1`). -/
theorem sum_mulChar_eq_zero [Fintype (MulChar M ℂ)] {a : Mˣ} (ha : a ≠ 1) :
    ∑ ξ : MulChar M ℂ, ξ (a : M) = 0 := by
  have : NeZero ((Monoid.exponent Mˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ0, hχ0⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity M ℂ
    (a := (a : M)) (by rwa [Ne, Units.val_eq_one])
  have h : ∑ ξ : MulChar M ℂ, χ0 (a : M) * ξ (a : M) = ∑ ξ : MulChar M ℂ, ξ (a : M) :=
    Fintype.sum_equiv (Equiv.mulLeft χ0) _ _ fun ξ => by
      rw [Equiv.coe_mulLeft, MulChar.coeToFun_mul, Pi.mul_apply]
  rw [← Finset.mul_sum] at h
  have h2 : (1 - χ0 (a : M)) * ∑ ξ : MulChar M ℂ, ξ (a : M) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hχ0))

open Classical in
/-- **Class indicators through characters**: `1_{x = c} = N⁻¹·Σ_ξ ξ(c⁻¹)·ξ(x)` for a unit `c`, with
`N` the number of characters. -/
theorem indicator_eq_sum_mulChar [Fintype (MulChar M ℂ)] (c : Mˣ) (x : M) :
    (if x = (c : M) then (1 : ℂ) else 0) =
      (Fintype.card (MulChar M ℂ) : ℂ)⁻¹ * ∑ ξ : MulChar M ℂ, ξ ((c⁻¹ : Mˣ) : M) * ξ x := by
  have hN : (Fintype.card (MulChar M ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have e : ∀ ξ : MulChar M ℂ, ξ ((c⁻¹ : Mˣ) : M) * ξ (u : M) = ξ ((c⁻¹ * u : Mˣ) : M) :=
      fun ξ => by rw [Units.val_mul, map_mul]
    simp_rw [e]
    by_cases hu : (u : M) = c
    · have h1 : c⁻¹ * u = 1 := by rw [Units.val_inj.1 hu, inv_mul_cancel]
      rw [ite_eq_left hu, h1, Units.val_one]
      simp only [MulChar.map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact (inv_mul_cancel₀ hN).symm
    · have h1 : c⁻¹ * u ≠ 1 := fun h => hu (by rw [inv_mul_eq_one.1 h])
      rw [ite_eq_right hu, sum_mulChar_eq_zero h1, mul_zero]
  · rw [ite_eq_right (fun h => hx (by rw [h]; exact c.isUnit))]
    simp [MulChar.map_nonunit _ hx]

/-- The coefficients of a function of two unit classes in products of characters:
`ĉ(ξ₁, ξ₂) = N⁻²·Σ_{c₁,c₂} Ψ(c₁, c₂)·ξ₁(c₁⁻¹)·ξ₂(c₂⁻¹)`. -/
def pairCoeff [Fintype (MulChar M ℂ)] [Fintype Mˣ] (Ψ : M → M → ℂ) (ξ1 ξ2 : MulChar M ℂ) : ℂ :=
  (Fintype.card (MulChar M ℂ) : ℂ)⁻¹ * (Fintype.card (MulChar M ℂ) : ℂ)⁻¹ *
    ∑ c1 : Mˣ, ∑ c2 : Mˣ, Ψ c1 c2 * ξ1 ((c1⁻¹ : Mˣ) : M) * ξ2 ((c2⁻¹ : Mˣ) : M)

/-- **A function of two unit classes is a sum of products of characters**:
`Ψ(x, y) = Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂)·ξ₁(x)·ξ₂(y)` for units `x, y`. -/
theorem pair_eq_sum_mulChar [Fintype (MulChar M ℂ)] [Fintype Mˣ] (Ψ : M → M → ℂ) (x y : Mˣ) :
    Ψ x y = ∑ ξ1 : MulChar M ℂ, ∑ ξ2 : MulChar M ℂ, pairCoeff Ψ ξ1 ξ2 * ξ1 x * ξ2 y := by
  open Classical in
  have h1 : Ψ x y = ∑ c1 : Mˣ, ∑ c2 : Mˣ, Ψ c1 c2 * ((if (x : M) = c1 then (1 : ℂ) else 0) *
      (if (y : M) = c2 then (1 : ℂ) else 0)) := by
    rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
    · simp
    · intro c2 _ hc2
      rw [ite_eq_right (fun h => hc2 (Units.val_inj.1 h).symm)]; ring
    · intro h; exact absurd (Finset.mem_univ y) h
    · intro c1 _ hc1
      refine Finset.sum_eq_zero fun c2 _ => ?_
      rw [ite_eq_right (fun h => hc1 (Units.val_inj.1 h).symm)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  set N : ℂ := (Fintype.card (MulChar M ℂ) : ℂ) with hN
  set T : Mˣ → Mˣ → MulChar M ℂ → MulChar M ℂ → ℂ := fun c1 c2 ξ1 ξ2 =>
    N⁻¹ * N⁻¹ * (Ψ c1 c2 * ξ1 ((c1⁻¹ : Mˣ) : M) * ξ2 ((c2⁻¹ : Mˣ) : M)) * ξ1 x * ξ2 y with hT
  have e1 : ∀ c1 c2 : Mˣ, Ψ c1 c2 * ((if (x : M) = c1 then (1 : ℂ) else 0) *
      (if (y : M) = c2 then (1 : ℂ) else 0)) =
      ∑ ξ1 : MulChar M ℂ, ∑ ξ2 : MulChar M ℂ, T c1 c2 ξ1 ξ2 := by
    intro c1 c2
    rw [indicator_eq_sum_mulChar, indicator_eq_sum_mulChar, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ2 _ => ?_
    simp only [hT]
    ring
  have e2 : ∀ ξ1 ξ2 : MulChar M ℂ, pairCoeff Ψ ξ1 ξ2 * ξ1 x * ξ2 y =
      ∑ c1 : Mˣ, ∑ c2 : Mˣ, T c1 c2 ξ1 ξ2 := by
    intro ξ1 ξ2
    unfold pairCoeff
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c1 _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  rw [h1, Finset.sum_congr rfl fun c1 _ => Finset.sum_congr rfl fun c2 _ => e1 c1 c2,
    Finset.sum_congr rfl fun ξ1 _ => Finset.sum_congr rfl fun ξ2 _ => e2 ξ1 ξ2]
  calc ∑ c1 : Mˣ, ∑ c2 : Mˣ, ∑ ξ1 : MulChar M ℂ, ∑ ξ2 : MulChar M ℂ, T c1 c2 ξ1 ξ2
      = ∑ c1 : Mˣ, ∑ ξ1 : MulChar M ℂ, ∑ c2 : Mˣ, ∑ ξ2 : MulChar M ℂ, T c1 c2 ξ1 ξ2 :=
        Finset.sum_congr rfl fun c1 _ => Finset.sum_comm
    _ = ∑ ξ1 : MulChar M ℂ, ∑ c1 : Mˣ, ∑ c2 : Mˣ, ∑ ξ2 : MulChar M ℂ, T c1 c2 ξ1 ξ2 :=
        Finset.sum_comm
    _ = ∑ ξ1 : MulChar M ℂ, ∑ c1 : Mˣ, ∑ ξ2 : MulChar M ℂ, ∑ c2 : Mˣ, T c1 c2 ξ1 ξ2 :=
        Finset.sum_congr rfl fun ξ1 _ => Finset.sum_congr rfl fun c1 _ => Finset.sum_comm
    _ = ∑ ξ1 : MulChar M ℂ, ∑ ξ2 : MulChar M ℂ, ∑ c1 : Mˣ, ∑ c2 : Mˣ, T c1 c2 ξ1 ξ2 :=
        Finset.sum_congr rfl fun ξ1 _ => Finset.sum_comm

/-- `‖ĉ(ξ₁, ξ₂)‖ ≤ B` when `‖Ψ‖ ≤ B` on unit classes (the numbers of characters and of units agree,
by Mathlib's `card_eq_card_units_of_hasEnoughRootsOfUnity`). -/
theorem norm_pairCoeff_le [Fintype (MulChar M ℂ)] [Fintype Mˣ] (Ψ : M → M → ℂ) {B : ℝ}
    (hB : ∀ c1 c2 : Mˣ, ‖Ψ c1 c2‖ ≤ B) (ξ1 ξ2 : MulChar M ℂ) : ‖pairCoeff Ψ ξ1 ξ2‖ ≤ B := by
  have : NeZero ((Monoid.exponent Mˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Fintype.card (MulChar M ℂ) = Fintype.card Mˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity M ℂ
  have hN : (0 : ℝ) < Fintype.card (MulChar M ℂ) := Nat.cast_pos.2 Fintype.card_pos
  have hv : ∀ (ξ : MulChar M ℂ) (c : Mˣ), ‖ξ ((c : Mˣ) : M)‖ = 1 := norm_mulChar_unit
  unfold pairCoeff
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ * (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ *
        ‖∑ c1 : Mˣ, ∑ c2 : Mˣ, Ψ c1 c2 * ξ1 ((c1⁻¹ : Mˣ) : M) * ξ2 ((c2⁻¹ : Mˣ) : M)‖
      ≤ (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ * (Fintype.card (MulChar M ℂ) : ℝ)⁻¹ *
        ∑ _c1 : Mˣ, ∑ _c2 : Mˣ, B := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c1 _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c2 _ => ?_)
        rw [norm_mul, norm_mul, hv, hv, mul_one, mul_one]
        exact hB c1 c2
    _ = B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcard]
        field_simp

end CharExpand

/-- An element prime to `2` has a unit class modulo `4`. -/
theorem isUnit_mk_four {z : 𝓞 K} (hz : IsCoprime z 2) :
    IsUnit (Ideal.Quotient.mk (span {(4 : 𝓞 K)}) z) := by
  obtain ⟨a, b, h⟩ := (hz.pow_right : IsCoprime z (2 ^ 2))
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (span {(4 : 𝓞 K)}) a) ?_
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (span {(4 : 𝓞 K)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  exact ⟨-b, by linear_combination -h⟩

/-- The primary generator of a squarefree ideal of norm prime to `6` is prime to `2`. -/
theorem isCoprime_pgen_two {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hsq : Squarefree I) :
    IsCoprime (pgen I) 2 := by
  rw [pgen_eq_prod hI hsq]
  exact IsCoprime.prod_left fun P _ => isCoprime_two (πP P) (h6Pr P)


end Eis

namespace MellinSep

open Complex MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace ContDiff SchwartzMap Nat ComplexConjugate

/-- **The bilinear form with two coefficient families**: round 302's `bilinear_dual_bound` with the
family `a` on the first column and `b` on the second, both satisfying the mean-square hypothesis with
the same `M`. -/
theorem bilinear_dual_bound₂ (W0 : ℝ → ℂ) (hW0 : ContDiff ℝ ∞ W0) {α β : ℝ} (hα : 0 < α)
    (hW0s : ∀ y, y < α ∨ β < y → W0 y = 0) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0) {ρ0 ρ1 : ℝ} (hρ0 : 0 < ρ0)
    (hV1 : ∀ y, α / ρ1 ≤ y → y ≤ β / ρ0 → V y = 1) (J : ℕ)
    (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ n : ℕ, ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n G ρ‖ ≤ C)
    {R : ℝ} (hR : ∀ ρ, R ≤ ρ → G ρ = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K, ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a b : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, b r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, ρ0 ≤ ρ r ∧ ρ r ≤ ρ1) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (b r n2) *
          (W0 (ρ r * x n1) * conj (W0 (ρ r * x n2)) *
            G (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ K * Amin ^ (-σ) * M := by
  obtain ⟨Kd, hKd⟩ := dilated_meanSquare W0 hW0 hα hW0s V hV hVc hVp hρ0 hV1 σ J
  obtain ⟨Kg, -, hKg⟩ := bilinear_dual_bound_of_dilated J G hG hGb hR hσ
  refine ⟨Kg * Kd, fun T C a b x hx M hM hyp hypb ρ hρ w hw Ar Amin hAmin hAr => ?_⟩
  have hs : ∀ s : ℂ, s.re = σ → |s.re| ≤ σ := fun s hs => by rw [hs, abs_of_pos hσ]
  have h := hKg W0 T C a b x hx ρ (Kd * M)
    (fun s hsr => hKd T C a x hx M hM hyp ρ hρ s (hs s hsr))
    (fun s hsr => hKd T C b x hx M hM hypb ρ hρ s (hs s hsr)) w hw Ar Amin hAmin hAr
  calc _ ≤ Kg * (Kd * M) * Amin ^ (-σ) := h
    _ = Kg * Kd * Amin ^ (-σ) * M := by ring

end MellinSep

end

#print axioms Eis.sym6_eq_zero_of_mem
#print axioms Eis.exists_common_factor
#print axioms Eis.span_pgen
#print axioms Eis.aXi_mul_left
#print axioms Eis.prod_Pr_dvd_iff
#print axioms Eis.indicator_Pr
#print axioms Eis.isRelPrime_iff_primeSet
#print axioms Eis.tsum_ideal_dvd_eq
#print axioms Eis.aXi_bot
#print axioms Eis.colSum_summand_eq_zero
#print axioms Eis.prod_sub_primeSet
#print axioms Eis.colSum_excl
#print axioms Eis.norm_mulChar_unit
#print axioms Eis.norm_xi_le
#print axioms Eis.norm_chiP_le
#print axioms Eis.norm_sym6_le
#print axioms Eis.norm_aXi_le
#print axioms Eis.colSum_excl_meanSquare_le
#print axioms Eis.dualMeanSquare_excl
#print axioms Eis.sum_mulChar_eq_zero
#print axioms Eis.indicator_eq_sum_mulChar
#print axioms Eis.pair_eq_sum_mulChar
#print axioms Eis.norm_pairCoeff_le
#print axioms Eis.isUnit_mk_four
#print axioms Eis.isCoprime_pgen_two
#print axioms MellinSep.bilinear_dual_bound₂
