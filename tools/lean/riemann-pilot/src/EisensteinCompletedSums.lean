import EisensteinMeanSquareDual

/-! # The completed sums and the cube inversion (round 313)

S5 of round 312's plan, part 1 (S5a): the companion paper's completed sum (5.3) and its cube
inversion (5.8), on the ideals of `ℤ[ω]`.

* **Primary generators of all ideals prime to `6`** (`exists_primary_gen`, `pgen_mul6`,
  `alphaI_mul6`): every ideal of norm prime to `6` has a primary generator, the product of those of
  its prime factors, so `pgen` and `α(𝔫) = σn/|σn|` are multiplicative on these ideals (round 305 had
  this for coprime squarefree ideals).
* **The twist** `twistPsi ξ k f 𝔫 = ξ(n)·(k/𝔫)₆·(f/𝔫)₆⁴` on ideals of norm prime to `6`, `0`
  otherwise: the paper's `Ψ_k` of (5.4), completely multiplicative (`twistPsi_mul`).
* **`tsum_moebius_dvd`**: `Σ_{𝔥 ∣ 𝔠} μ(𝔥) = [𝔠 = 1]` for `𝔠` of norm prime to `6`, through the
  squarefree divisors `∏_{P∈A} P`, `A ⊆ primeSet 𝔠` (Mathlib's `Finset.sum_powerset_neg_one_pow_card`).
* **The completed sum** `compT` (the paper's (5.3)): `T(X;Ψ) = Σ_{𝔫 squarefree, 𝔟}
  ᾱ(𝔫)γ₂(𝔫)Ψ(𝔫)·ᾱ(𝔟)³Ψ(𝔟)³/(√N𝔫·N𝔟)·V_*(N𝔫·N𝔟³/X)` with `V_*(y) = √y·W(y)`; its column coefficient
  is the dual mean square's (`gCoef_eq_col`), and at length `X/N(𝔥)³` it is a finite double sum over
  the ideals of norm at most `βX` (`compT_eq_sum`).
* **Two finite sums** (round 332): the column sum over the ideals of norm at most `βX`
  (`colSum_eq_sum_gCoef`, round 314's, from `EisensteinCubeReduction.lean`), and the sum over `𝔥` of
  the cube inversion, whose terms with `N𝔥 > βX` vanish (`tsum_compT_eq_sum`).
* **`inner_cube_sum`** and **`cube_inversion`** (the paper's (5.8)): the normalized column sum of
  the dual mean square is `X^{−1/2}·colSum = Σ_𝔥 μ(𝔥)ᾱ(𝔥)³Ψ(𝔥)³/N𝔥 · T(X/N𝔥³; Ψ)`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-! ### Primary generators of the ideals prime to `6` -/

theorem ne_bot_of_coprime6 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) : I ≠ ⊥ := by
  intro h; rw [h, absNorm_bot] at hI; norm_num at hI

/-- Every ideal of norm prime to `6` has a primary generator: the product of those of its prime
factors. -/
theorem exists_primary_gen {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    ∃ a, Primary a ∧ span {a} = I := by
  have hspec : ∀ P ∈ normalizedFactors I, Primary (pgen P) ∧ span {pgen P} = P := by
    intro P hP
    have := isMaximal_of_factor hP
    exact pgen_maximal P (three_not_mem_of_six P (six_not_mem_of_factor hI hP))
  refine ⟨((normalizedFactors I).map pgen).prod, primary_multiset_prod fun x hx => ?_, ?_⟩
  · obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
    exact (hspec P hP).1
  · rw [← Ideal.multiset_prod_span_singleton, Multiset.map_map]
    have e : (normalizedFactors I).map ((fun x => span {x}) ∘ pgen) = normalizedFactors I := by
      conv_rhs => rw [← Multiset.map_id (normalizedFactors I)]
      exact Multiset.map_congr rfl fun P hP => (hspec P hP).2
    rw [e]
    exact Ideal.prod_normalizedFactors_eq_self (ne_bot_of_coprime6 hI)

theorem pgen_spec6 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    Primary (pgen I) ∧ span {pgen I} = I := pgen_spec (exists_primary_gen hI)

/-- **The primary generator is multiplicative** on the ideals of norm prime to `6`. -/
theorem pgen_mul6 {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hJ : (absNorm J).Coprime 6) :
    pgen (I * J) = pgen I * pgen J := by
  obtain ⟨h1, h2⟩ := pgen_spec6 hI
  obtain ⟨h1', h2'⟩ := pgen_spec6 hJ
  have e : span {pgen I * pgen J} = I * J := by
    rw [← Ideal.span_singleton_mul_span_singleton, h2, h2']
  rw [← e]; exact pgen_eq (h1.mul h1')

theorem pgen_one : pgen (1 : Ideal (𝓞 K)) = 1 := by
  have : (1 : Ideal (𝓞 K)) = span {1} := by rw [Ideal.one_eq_top, Ideal.span_singleton_one]
  rw [this]; exact pgen_eq (by unfold Primary; simp)

theorem alphaI_mul6 {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (hJ : (absNorm J).Coprime 6) :
    alphaI (I * J) = alphaI I * alphaI J := by
  unfold alphaI
  rw [pgen_mul6 hI hJ, map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

theorem alphaI_one : alphaI (1 : Ideal (𝓞 K)) = 1 := by
  unfold alphaI; rw [pgen_one, map_one, norm_one]; simp

/-! ### The twists `Ψ` -/

open Classical in
/-- `Ψ(𝔫) = ξ(n)·(k/𝔫)₆·(f/𝔫)₆⁴` for an ideal `𝔫` of norm prime to `6` with primary generator `n`,
and `0` otherwise: the twist `Ψ_k` of the companion paper's (5.4), extended to all ideals. -/
def twistPsi (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ :=
  if (absNorm I).Coprime 6 then ξ (Ideal.Quotient.mk _ (pgen I)) * sym6 k I * sym6 f I ^ 4 else 0

/-- **`Ψ` is completely multiplicative.** -/
theorem twistPsi_mul (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (I J : Ideal (𝓞 K)) :
    twistPsi ξ k f (I * J) = twistPsi ξ k f I * twistPsi ξ k f J := by
  unfold twistPsi
  by_cases hI : (absNorm I).Coprime 6
  · by_cases hJ : (absNorm J).Coprime 6
    · rw [ite_eq_left (coprime6_mul hI hJ), ite_eq_left hI, ite_eq_left hJ, pgen_mul6 hI hJ,
        map_mul, map_mul, sym6_mul_right k (ne_bot_of_coprime6 hI) (ne_bot_of_coprime6 hJ),
        sym6_mul_right f (ne_bot_of_coprime6 hI) (ne_bot_of_coprime6 hJ)]
      ring
    · have : ¬ (absNorm (I * J)).Coprime 6 := by
        rw [map_mul, Nat.coprime_mul_iff_left]; exact fun h => hJ h.2
      rw [ite_eq_right this, ite_eq_right hJ, mul_zero]
  · have : ¬ (absNorm (I * J)).Coprime 6 := by
      rw [map_mul, Nat.coprime_mul_iff_left]; exact fun h => hI h.1
    rw [ite_eq_right this, ite_eq_right hI, zero_mul]

theorem twistPsi_one (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) :
    twistPsi ξ k f 1 = 1 := by
  unfold twistPsi
  rw [ite_eq_left (by rw [map_one]; norm_num), pgen_one, map_one, map_one, sym6_one_right,
    sym6_one_right]
  ring

theorem norm_twistPsi_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (I : Ideal (𝓞 K)) :
    ‖twistPsi ξ k f I‖ ≤ 1 := by
  unfold twistPsi
  split_ifs
  · rw [norm_mul, norm_mul, norm_pow]
    have h1 := norm_xi_le ξ (Ideal.Quotient.mk _ (pgen I))
    have h2 := norm_sym6_le k I
    have h3 := norm_sym6_le f I
    calc ‖ξ (Ideal.Quotient.mk _ (pgen I))‖ * ‖sym6 k I‖ * ‖sym6 f I‖ ^ 4 ≤ 1 * 1 * 1 ^ 4 := by
          gcongr
      _ = 1 := by norm_num
  · simp

/-! ### The Möbius sum over divisors -/

theorem dvd_of_subset_primeSet {C : Ideal (𝓞 K)} (hC : C ≠ ⊥) {A : Finset Pr}
    (hA : A ⊆ primeSet C) : idl A ∣ C := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (idl_ne_bot A) hC, normalizedFactors_idl]
  rw [Multiset.le_iff_subset (A.nodup.map Subtype.val_injective)]
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 hP
  exact mem_primeSet.1 (hA hQ)

theorem eq_one_iff_primeSet {C : Ideal (𝓞 K)} (hC : (absNorm C).Coprime 6) :
    C = 1 ↔ primeSet C = ∅ := by
  constructor
  · rintro rfl
    unfold primeSet
    rw [normalizedFactors_one]
    rfl
  · intro h
    have hC0 := ne_bot_of_coprime6 hC
    have hnf : normalizedFactors C = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro P hP
      have hmem : (⟨P, isMaximal_of_factor hP, six_not_mem_of_factor hC hP⟩ : Pr) ∈ primeSet C :=
        mem_primeSet.2 hP
      rw [h] at hmem
      exact Finset.notMem_empty _ hmem
    have hu : IsUnit C := (normalizedFactors_eq_zero_iff hC0).1 hnf
    rw [Ideal.one_eq_top]; exact Ideal.isUnit_iff.1 hu

open Classical in
/-- **`Σ_{𝔥 ∣ 𝔠} μ(𝔥) = [𝔠 = 1]`** for an ideal `𝔠` of norm prime to `6`: the squarefree divisors are
the products over the subsets of the prime set (Mathlib's `Finset.sum_powerset_neg_one_pow_card`). -/
theorem tsum_moebius_dvd {C : Ideal (𝓞 K)} (hC : (absNorm C).Coprime 6) :
    ∑' H : Ideal (𝓞 K), (if H ∣ C then (moebius H : ℂ) else 0) = if C = 1 then 1 else 0 := by
  have hC0 := ne_bot_of_coprime6 hC
  have hinj : Set.InjOn (idl : Finset Pr → Ideal (𝓞 K)) ↑((primeSet C).powerset) := fun A _ B _ h => by
    rw [← primeSet_idl A, ← primeSet_idl B, h]
  have hzero : ∀ H ∉ (primeSet C).powerset.image idl,
      (if H ∣ C then (moebius H : ℂ) else 0) = 0 := by
    intro H hH
    by_cases hdvd : H ∣ C
    · rw [ite_eq_left hdvd]
      by_cases hsq : Squarefree H
      · exfalso
        apply hH
        have hH6 : (absNorm H).Coprime 6 :=
          Nat.Coprime.coprime_dvd_left (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)) hC
        rw [Finset.mem_image]
        refine ⟨primeSet H, ?_, idl_primeSet hH6 hsq⟩
        rw [Finset.mem_powerset]
        intro P hP
        rw [mem_primeSet] at hP ⊢
        exact Multiset.mem_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors
          (ne_bot_of_coprime6 hH6) hC0).1 hdvd) hP
      · rw [moebius_of_not_squarefree hsq]; simp
    · rw [ite_eq_right hdvd]
  rw [tsum_eq_sum hzero, Finset.sum_image hinj]
  have e : ∀ A ∈ (primeSet C).powerset,
      (if idl A ∣ C then (moebius (idl A) : ℂ) else 0) = ((-1 : ℤ) ^ A.card : ℤ) := by
    intro A hA
    rw [ite_eq_left (dvd_of_subset_primeSet hC0 (Finset.mem_powerset.1 hA)), moebius_idl]
  rw [Finset.sum_congr rfl e, ← Int.cast_sum, Finset.sum_powerset_neg_one_pow_card]
  by_cases h1 : C = 1
  · rw [ite_eq_left ((eq_one_iff_primeSet hC).1 h1), ite_eq_left h1]; simp
  · rw [ite_eq_right (fun h => h1 ((eq_one_iff_primeSet hC).2 h)), ite_eq_right h1]; simp

section Completed

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- `V_*(y) = √y·W(y)`, the weight of the companion paper's (5.3). -/
def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := ((Real.sqrt y : ℝ) : ℂ) * W y

open Classical in
/-- The column coefficient of the completed sum: `ᾱ(𝔫)γ₂(𝔫)Ψ(𝔫)` on squarefree `𝔫`. -/
def gCoef (I : Ideal (𝓞 K)) : ℂ :=
  if Squarefree I then conj (alphaI I) * gamI 2 I * twistPsi ξ k f I else 0

/-- The cube coefficient of the completed sum: `ᾱ(𝔟)³Ψ(𝔟)³`. -/
def dCoef (J : Ideal (𝓞 K)) : ℂ := conj (alphaI J) ^ 3 * twistPsi ξ k f J ^ 3

/-- **The completed sum** (the companion paper's (5.3) with `Ψ = Ψ_{k,f}` of (5.4)):
`T(X;Ψ) = Σ_{𝔫 squarefree, 𝔟} ᾱ(𝔫)γ₂(𝔫)Ψ(𝔫)·ᾱ(𝔟)³Ψ(𝔟)³/(√N𝔫·N𝔟)·V_*(N𝔫·N𝔟³/X)`, over the ideals
of norm prime to `6` (where `Ψ` vanishes otherwise). -/
def compT (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal (𝓞 K) × Ideal (𝓞 K),
    gCoef ξ k f p.1 * dCoef ξ k f p.2 /
        (((Real.sqrt (absNorm p.1 : ℝ) : ℝ) : ℂ) * (absNorm p.2 : ℂ)) *
      Vstar W ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 / X)

theorem twistPsi_eq_zero {I : Ideal (𝓞 K)} (h : ¬ (absNorm I).Coprime 6) : twistPsi ξ k f I = 0 := by
  unfold twistPsi; exact ite_eq_right h

theorem coprime6_of_twistPsi {I : Ideal (𝓞 K)} (h : twistPsi ξ k f I ≠ 0) : (absNorm I).Coprime 6 := by
  by_contra hc; exact h (twistPsi_eq_zero ξ k f hc)

theorem coprime6_of_gCoef {I : Ideal (𝓞 K)} (h : gCoef ξ k f I ≠ 0) : (absNorm I).Coprime 6 := by
  apply coprime6_of_twistPsi ξ k f
  intro h0; apply h; unfold gCoef; rw [h0]; simp

theorem coprime6_of_dCoef {J : Ideal (𝓞 K)} (h : dCoef ξ k f J ≠ 0) : (absNorm J).Coprime 6 := by
  apply coprime6_of_twistPsi ξ k f
  intro h0; apply h; unfold dCoef; rw [h0]; ring

theorem one_le_absNorm_of_coprime6 {I : Ideal (𝓞 K)} (h : (absNorm I).Coprime 6) :
    (1 : ℝ) ≤ absNorm I := by
  have : absNorm I ≠ 0 := fun h0 => by rw [h0] at h; norm_num at h
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem dCoef_mul (H J : Ideal (𝓞 K)) :
    dCoef ξ k f (H * J) = dCoef ξ k f H * dCoef ξ k f J := by
  unfold dCoef
  by_cases hH : (absNorm H).Coprime 6
  · by_cases hJ : (absNorm J).Coprime 6
    · rw [alphaI_mul6 hH hJ, twistPsi_mul, map_mul]; ring
    · rw [twistPsi_mul, twistPsi_eq_zero ξ k f hJ]; ring
  · rw [twistPsi_mul, twistPsi_eq_zero ξ k f hH]; ring

theorem dCoef_one : dCoef ξ k f 1 = 1 := by
  unfold dCoef; rw [alphaI_one, twistPsi_one]; simp

open Classical in
/-- The column coefficient is the dual mean square's: `ᾱγ₂Ψ = a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴`. -/
theorem gCoef_eq_col (I : Ideal (𝓞 K)) :
    gCoef ξ k f I = aXi ξ I * sym6 k I * sym6 f I ^ 4 := by
  unfold gCoef aXi twistPsi
  by_cases hsq : Squarefree I
  · by_cases h6 : (absNorm I).Coprime 6
    · rw [ite_eq_left hsq, ite_eq_left h6,
        ite_eq_left (show (absNorm I).Coprime 6 ∧ Squarefree I from ⟨h6, hsq⟩)]
      ring
    · rw [ite_eq_left hsq, ite_eq_right h6,
        ite_eq_right (show ¬ ((absNorm I).Coprime 6 ∧ Squarefree I) from fun h => h6 h.1)]
      ring
  · rw [ite_eq_right hsq,
      ite_eq_right (show ¬ ((absNorm I).Coprime 6 ∧ Squarefree I) from fun h => hsq h.2)]
    ring

/-! ### The completed sum as a finite sum -/

theorem le_of_Vstar_ne_zero {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {y : ℝ}
    (h : Vstar W y ≠ 0) : y ≤ β := by
  by_contra hc
  apply h
  unfold Vstar; rw [hW y (not_le.1 hc), mul_zero]

theorem mem_idealsLe_of {C : Ideal (𝓞 K)} {B : ℝ} (h1 : (1 : ℝ) ≤ absNorm C)
    (h2 : (absNorm C : ℝ) ≤ B) : C ∈ idealsLe B := by
  rw [mem_idealsLe]
  refine ⟨?_, Nat.le_floor h2⟩
  have : (0 : ℝ) < absNorm C := lt_of_lt_of_le zero_lt_one h1
  exact_mod_cast this

theorem le_cube {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ 3 := by nlinarith [sq_nonneg x]

/-- **The completed sum at length `X/N(𝔥)³`** as a finite double sum over the ideals of norm at most
`βX`. -/
theorem compT_eq_sum {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X)
    {nH : ℝ} (hnH : 1 ≤ nH) :
    compT ξ k f W (X / nH ^ 3) =
      ∑ I ∈ idealsLe (β * X), ∑ J ∈ idealsLe (β * X),
        gCoef ξ k f I * dCoef ξ k f J /
            (((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) * (absNorm J : ℂ)) *
          Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * nH ^ 3 / X) := by
  have hnH0 : (0 : ℝ) < nH := by linarith
  unfold compT
  rw [← Finset.sum_product']
  have e : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), (absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 / (X / nH ^ 3) =
      (absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 * nH ^ 3 / X := fun p => by
    field_simp
  simp_rw [e]
  refine tsum_eq_sum fun p hp => ?_
  by_contra hne
  apply hp
  have hg : gCoef ξ k f p.1 ≠ 0 := fun h => hne (by rw [h]; simp)
  have hd : dCoef ξ k f p.2 ≠ 0 := fun h => hne (by rw [h]; simp)
  have hV : Vstar W ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 * nH ^ 3 / X) ≠ 0 :=
    fun h => hne (by rw [h]; simp)
  have h1 := one_le_absNorm_of_coprime6 (coprime6_of_gCoef ξ k f hg)
  have h2 := one_le_absNorm_of_coprime6 (coprime6_of_dCoef ξ k f hd)
  have hle := le_of_Vstar_ne_zero hW hV
  rw [div_le_iff₀ hX] at hle
  have hc2 := le_cube h2
  have hcH := le_cube hnH
  have hJ3 : (1 : ℝ) ≤ (absNorm p.2 : ℝ) ^ 3 := le_trans h2 hc2
  have hH3 : (1 : ℝ) ≤ nH ^ 3 := le_trans hnH hcH
  rw [Finset.mem_product]
  constructor
  · refine mem_idealsLe_of h1 ?_
    calc (absNorm p.1 : ℝ) = (absNorm p.1 : ℝ) * 1 * 1 := by ring
      _ ≤ (absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 * nH ^ 3 := by gcongr
      _ ≤ β * X := hle
  · refine mem_idealsLe_of h2 ?_
    calc (absNorm p.2 : ℝ) ≤ (absNorm p.2 : ℝ) ^ 3 := hc2
      _ = 1 * (absNorm p.2 : ℝ) ^ 3 * 1 := by ring
      _ ≤ (absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 * nH ^ 3 := by gcongr
      _ ≤ β * X := hle

end Completed

section Inversion

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- The cube term `F(𝔠) = ᾱ(𝔠)³Ψ(𝔠)³/N𝔠 · V_*(n·N𝔠³/X)`. -/
def cubeF (W : ℝ → ℂ) (X n : ℝ) (C : Ideal (𝓞 K)) : ℂ :=
  dCoef ξ k f C / (absNorm C : ℂ) * Vstar W (n * (absNorm C : ℝ) ^ 3 / X)

theorem cubeF_mem {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X)
    {n : ℝ} (hn : 1 ≤ n) {C : Ideal (𝓞 K)} (h : cubeF ξ k f W X n C ≠ 0) :
    C ∈ idealsLe (β * X) := by
  have hd : dCoef ξ k f C ≠ 0 := fun h0 => h (by unfold cubeF; rw [h0]; simp)
  have hV : Vstar W (n * (absNorm C : ℝ) ^ 3 / X) ≠ 0 :=
    fun h0 => h (by unfold cubeF; rw [h0]; simp)
  have h1 := one_le_absNorm_of_coprime6 (coprime6_of_dCoef ξ k f hd)
  have hle := le_of_Vstar_ne_zero hW hV
  rw [div_le_iff₀ hX] at hle
  refine mem_idealsLe_of h1 ?_
  calc (absNorm C : ℝ) ≤ (absNorm C : ℝ) ^ 3 := le_cube h1
    _ = 1 * (absNorm C : ℝ) ^ 3 := (one_mul _).symm
    _ ≤ n * (absNorm C : ℝ) ^ 3 := by gcongr
    _ ≤ β * X := hle

theorem cubeF_mul (W : ℝ → ℂ) (X n : ℝ) (H J : Ideal (𝓞 K)) :
    cubeF ξ k f W X n (H * J) = dCoef ξ k f H / (absNorm H : ℂ) *
      (dCoef ξ k f J / (absNorm J : ℂ) *
        Vstar W (n * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X)) := by
  unfold cubeF
  have e : n * ((absNorm (H * J) : ℕ) : ℝ) ^ 3 / X =
      n * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X := by
    rw [map_mul]; push_cast; ring
  rw [e, dCoef_mul, map_mul]
  push_cast
  ring

theorem cubeF_one (W : ℝ → ℂ) (X n : ℝ) : cubeF ξ k f W X n 1 = Vstar W (n / X) := by
  unfold cubeF
  rw [dCoef_one, map_one]
  simp

open Classical in
/-- **The Möbius sum over the cube index**:
`Σ_𝔥 μ(𝔥)ᾱ(𝔥)³Ψ(𝔥)³/N𝔥 · Σ_𝔟 ᾱ(𝔟)³Ψ(𝔟)³/N𝔟 · V_*(n·N(𝔟)³N(𝔥)³/X) = V_*(n/X)` for `n ≥ 1`, the sums
running over the ideals of norm at most `βX`: the cube indices `𝔠 = 𝔥𝔟` carry `Σ_{𝔥∣𝔠} μ(𝔥) = [𝔠 = 1]`. -/
theorem inner_cube_sum {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X)
    {n : ℝ} (hn : 1 ≤ n) :
    ∑ H ∈ idealsLe (β * X), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
      ∑ J ∈ idealsLe (β * X), dCoef ξ k f J / (absNorm J : ℂ) *
        Vstar W (n * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) =
      Vstar W (n / X) := by
  set 𝓘 := idealsLe (β * X) with h𝓘
  set F := cubeF ξ k f W X n with hF
  have h12 : ∀ H ∈ 𝓘, (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
      ∑ J ∈ 𝓘, dCoef ξ k f J / (absNorm J : ℂ) *
        Vstar W (n * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) =
      (moebius H : ℂ) * ∑ C ∈ 𝓘, if H ∣ C then F C else 0 := by
    intro H hH
    have hH0 : H ≠ ⊥ := ne_bot_of_mem_idealsLe hH
    have e1 : ∑ J ∈ 𝓘, F (H * J) = ∑' J, F (H * J) := by
      refine (tsum_eq_sum fun J hJ => ?_).symm
      by_contra hne
      apply hJ
      have hC := cubeF_mem ξ k f hW hX hn hne
      rw [mem_idealsLe] at hC ⊢
      rw [map_mul] at hC
      have hJ0 : 0 < absNorm J := Nat.pos_of_mul_pos_left hC.1
      have hH1 : 0 < absNorm H := Nat.pos_of_mul_pos_right hC.1
      exact ⟨hJ0, le_trans (Nat.le_mul_of_pos_left _ hH1) hC.2⟩
    have e2 : ∑ C ∈ 𝓘, (if H ∣ C then F C else 0) = ∑' C, if H ∣ C then F C else 0 := by
      refine (tsum_eq_sum fun C hC => ?_).symm
      by_cases hd : H ∣ C
      · rw [ite_eq_left hd]
        by_contra hne
        exact hC (cubeF_mem ξ k f hW hX hn hne)
      · rw [ite_eq_right hd]
    rw [e2, tsum_ideal_dvd_eq H hH0 F, ← e1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hF, cubeF_mul]
    ring
  rw [Finset.sum_congr rfl h12]
  have h3 : ∑ H ∈ 𝓘, (moebius H : ℂ) * (∑ C ∈ 𝓘, if H ∣ C then F C else 0) =
      ∑ C ∈ 𝓘, F C * ∑ H ∈ 𝓘, (if H ∣ C then (moebius H : ℂ) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun H _ => ?_
    split_ifs <;> ring
  rw [h3]
  have h4 : ∀ C ∈ 𝓘, F C * ∑ H ∈ 𝓘, (if H ∣ C then (moebius H : ℂ) else 0) =
      if C = 1 then F C else 0 := by
    intro C hC
    by_cases hC6 : (absNorm C).Coprime 6
    · have e : ∑ H ∈ 𝓘, (if H ∣ C then (moebius H : ℂ) else 0) =
          ∑' H, if H ∣ C then (moebius H : ℂ) else 0 := by
        refine (tsum_eq_sum fun H hH => ?_).symm
        by_cases hd : H ∣ C
        · exfalso
          apply hH
          have hC0 := ne_bot_of_coprime6 hC6
          have hNle : absNorm H ≤ absNorm C :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => hC0 (absNorm_eq_zero_iff.1 h)))
              (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
          have hH0 : H ≠ ⊥ := fun h => hC0 (by rw [h] at hd; exact zero_dvd_iff.1 hd)
          rw [mem_idealsLe] at hC ⊢
          exact ⟨Nat.pos_of_ne_zero (fun h => hH0 (absNorm_eq_zero_iff.1 h)), hNle.trans hC.2⟩
        · rw [ite_eq_right hd]
      rw [e, tsum_moebius_dvd hC6]
      split_ifs <;> ring
    · have hF0 : F C = 0 := by
        rw [hF]; unfold cubeF dCoef; rw [twistPsi_eq_zero ξ k f hC6]; ring
      rw [hF0]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq']
  split_ifs with h1
  · rw [hF, cubeF_one]
  · by_contra hne
    rw [← cubeF_one ξ k f W X n] at hne
    exact h1 (cubeF_mem ξ k f hW hX hn (Ne.symm hne))

end Inversion

section Inversion2

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- The column sum of the dual mean square as a finite sum of the completed sums' column
coefficients, over the ideals of norm at most `βX`. -/
theorem colSum_eq_sum_gCoef {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) :
    colSum ξ W X 1 k f = ∑ I ∈ idealsLe (β * X), gCoef ξ k f I * W ((absNorm I : ℝ) / X) := by
  unfold colSum
  rw [tsum_eq_sum (s := idealsLe (β * X)) (fun I hI => ?_)]
  · refine Finset.sum_congr rfl fun I _ => ?_
    rw [ite_eq_left isRelPrime_one_right, gCoef_eq_col]
  · rw [ite_eq_left isRelPrime_one_right]
    have h0 : aXi ξ I * (sym6 k I * sym6 f I ^ 4) * W ((absNorm I : ℝ) / X) = 0 :=
      colSum_summand_eq_zero ξ hW hX (fun I => sym6 k I * sym6 f I ^ 4) hI
    linear_combination h0

/-- **The sum over `𝔥` in the cube inversion is finite**: the terms with `N𝔥 > βX` vanish (round 332,
from round 314's `cube_inversion_sum`). -/
theorem tsum_compT_eq_sum {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) :
    ∑' H : Ideal (𝓞 K), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        compT ξ k f W (X / (absNorm H : ℝ) ^ 3) =
      ∑ H ∈ idealsLe (β * X), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        compT ξ k f W (X / (absNorm H : ℝ) ^ 3) := by
  refine tsum_eq_sum fun H hH => ?_
  by_cases hd : dCoef ξ k f H = 0
  · rw [hd]; simp
  have h1 := one_le_absNorm_of_coprime6 (coprime6_of_dCoef ξ k f hd)
  have hgt : β * X < absNorm H := by
    by_contra hle
    exact hH (mem_idealsLe_of h1 (not_lt.1 hle))
  rw [compT_eq_sum ξ k f hW hX h1]
  have hz : ∀ I ∈ idealsLe (β * X), ∀ J ∈ idealsLe (β * X), gCoef ξ k f I * dCoef ξ k f J /
        (((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) * (absNorm J : ℂ)) *
      Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) = 0 := by
    intro I hI J hJ
    have hI1 : (1 : ℝ) ≤ absNorm I := by rw [mem_idealsLe] at hI; exact_mod_cast hI.1
    have hJ1 : (1 : ℝ) ≤ absNorm J := by rw [mem_idealsLe] at hJ; exact_mod_cast hJ.1
    have hV : Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) = 0 := by
      unfold Vstar
      rw [hW _ ?_, mul_zero]
      rw [lt_div_iff₀ hX]
      have hJ3 : (1 : ℝ) ≤ (absNorm J : ℝ) ^ 3 := one_le_pow₀ hJ1
      calc β * X < absNorm H := hgt
        _ ≤ (absNorm H : ℝ) ^ 3 := le_cube h1
        _ = 1 * 1 * (absNorm H : ℝ) ^ 3 := by ring
        _ ≤ (absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 := by gcongr
    rw [hV, mul_zero]
  rw [Finset.sum_eq_zero fun I hI => Finset.sum_eq_zero fun J hJ => hz I hI J hJ, mul_zero]

/-- **The cube inversion** (the companion paper's (5.8)): the normalized column sum of the dual mean
square is `X^{−1/2}·Σ_𝔫 a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴W(N𝔫/X) = Σ_𝔥 μ(𝔥)ᾱ(𝔥)³Ψ(𝔥)³/N𝔥 · T(X/N𝔥³; Ψ)`. -/
theorem cube_inversion {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X) :
    ((Real.sqrt X : ℝ) : ℂ)⁻¹ * colSum ξ W X 1 k f =
      ∑' H : Ideal (𝓞 K), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        compT ξ k f W (X / (absNorm H : ℝ) ^ 3) := by
  set 𝓘 := idealsLe (β * X) with h𝓘
  have hL : ((Real.sqrt X : ℝ) : ℂ)⁻¹ * colSum ξ W X 1 k f =
      ∑ I ∈ 𝓘, gCoef ξ k f I * (((Real.sqrt X : ℝ) : ℂ)⁻¹ * W ((absNorm I : ℝ) / X)) := by
    rw [colSum_eq_sum_gCoef ξ k f hW hX, Finset.mul_sum]
    exact Finset.sum_congr rfl fun I _ => by ring
  have hR : ∑' H : Ideal (𝓞 K), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        compT ξ k f W (X / (absNorm H : ℝ) ^ 3) =
      ∑ H ∈ 𝓘, (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        ∑ I ∈ 𝓘, ∑ J ∈ 𝓘, gCoef ξ k f I * dCoef ξ k f J /
            (((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) * (absNorm J : ℂ)) *
          Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) := by
    rw [tsum_compT_eq_sum ξ k f hW hX]
    refine Finset.sum_congr rfl fun H hH => ?_
    have h1 : (1 : ℝ) ≤ absNorm H := by
      rw [mem_idealsLe] at hH; exact_mod_cast hH.1
    rw [compT_eq_sum ξ k f hW hX h1]
  rw [hL, hR]
  have hreg : ∑ H ∈ 𝓘, (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        ∑ I ∈ 𝓘, ∑ J ∈ 𝓘, gCoef ξ k f I * dCoef ξ k f J /
            (((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) * (absNorm J : ℂ)) *
          Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) =
      ∑ I ∈ 𝓘, gCoef ξ k f I / ((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) *
        ∑ H ∈ 𝓘, (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
          ∑ J ∈ 𝓘, dCoef ξ k f J / (absNorm J : ℂ) *
            Vstar W ((absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * (absNorm H : ℝ) ^ 3 / X) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun H _ =>
      Finset.sum_congr rfl fun J _ => ?_
    ring
  rw [hreg]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hg : gCoef ξ k f I = 0
  · rw [hg]; ring
  have h1 := one_le_absNorm_of_coprime6 (coprime6_of_gCoef ξ k f hg)
  rw [inner_cube_sum ξ k f hW hX h1]
  unfold Vstar
  have hs : Real.sqrt ((absNorm I : ℝ) / X) = Real.sqrt (absNorm I : ℝ) / Real.sqrt X :=
    Real.sqrt_div (by positivity) X
  have hsI : ((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (absNorm I : ℝ) := Real.sqrt_pos.2 (by linarith)
    exact_mod_cast this.ne'
  have hsX : ((Real.sqrt X : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX
    exact_mod_cast this.ne'
  rw [hs]
  push_cast
  field_simp

end Inversion2

end Eis

end

#print axioms Eis.ne_bot_of_coprime6
#print axioms Eis.exists_primary_gen
#print axioms Eis.pgen_spec6
#print axioms Eis.pgen_mul6
#print axioms Eis.pgen_one
#print axioms Eis.alphaI_mul6
#print axioms Eis.alphaI_one
#print axioms Eis.twistPsi_mul
#print axioms Eis.twistPsi_one
#print axioms Eis.norm_twistPsi_le
#print axioms Eis.dvd_of_subset_primeSet
#print axioms Eis.eq_one_iff_primeSet
#print axioms Eis.tsum_moebius_dvd
#print axioms Eis.twistPsi_eq_zero
#print axioms Eis.coprime6_of_twistPsi
#print axioms Eis.coprime6_of_gCoef
#print axioms Eis.coprime6_of_dCoef
#print axioms Eis.one_le_absNorm_of_coprime6
#print axioms Eis.dCoef_mul
#print axioms Eis.dCoef_one
#print axioms Eis.gCoef_eq_col
#print axioms Eis.le_of_Vstar_ne_zero
#print axioms Eis.mem_idealsLe_of
#print axioms Eis.le_cube
#print axioms Eis.compT_eq_sum
#print axioms Eis.cubeF_mem
#print axioms Eis.cubeF_mul
#print axioms Eis.cubeF_one
#print axioms Eis.inner_cube_sum
#print axioms Eis.colSum_eq_sum_gCoef
#print axioms Eis.tsum_compT_eq_sum
#print axioms Eis.cube_inversion
