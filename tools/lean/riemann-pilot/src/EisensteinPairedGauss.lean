import EisensteinGaussSquarefree

/-! # The paired Gauss sums of the Poisson reduction (round 304)

S4 of round 291's plan, part 4: the arithmetic step of the companion paper's Proposition 4.5. After
Poisson summation (round 303) the mean square produces, for each pair of coprime squarefree columns
`z₁, z₂`, the normalized Gauss sum of `χ_{z₁}·χ̄_{z₂}` modulo `z₁z₂`. The paper converts it into
`Σ_ξ c_ξ a_ξ(z₁)ā_ξ(z₂)`, a sum over characters `ξ` of a ray class group, using its Lemma 4.1 and a
bicharacter `R` on that group. Here the conversion is made without the bicharacter: the factor left
after splitting off `ā(z₁)a(z₂)` is computed in closed form, and it depends only on `z₁, z₂ mod 4`.

* **Quadratic sums over squarefree moduli.** `ψ₁ = 1` (`ψc_one`); `S_{ab}(t) = S_a(tb)·S_b(ta)` for
  coprime `a, b` (`sqSum_mul_t`, round 298's `sqSum_mul` with a twist `t`); by induction
  `S_{∏c_i}(t) = ∏_i S_{c_i}(t·∏_{j≠i} c_j)` (`sqSum_prod`).
* **`γ₃(n) = Φ(a, b)/2`** for `n = ∏_{i∈S} π_i = a + bω` (`gamF_three_eq`), the paper's
  `γ₃(n) = Γ_quad(n)`: round 300's factorization of the Gauss sum of the Jacobi symbol is
  `∏_i S_{π_i}(n/π_i)` (round 298's `sqSum_prime`), which is `S_n(1)`, evaluated by round 297's
  `quad_gauss_coords`. Also `γ₃(n)² = χ_n(−1)` (`gamF_three_sq`, from Mathlib's `gaussSum_sq`).
* **`χ_n(4)` through `n mod 2`** (`prod_chi6_four`, `prod_chi6_four_eq`), from round 299's
  `chi6_four`.
* **Unit norms**: `|γ(n)| = 1` for nontrivial characters of order dividing `6` (`norm_gamF`),
  `|α(p)| = |χ_p(4)| = 1`, and `|a(n)| = 1` for the paper's `a(n) = ᾱ(n)γ₂(n)` (`aF`, `norm_aF`).
* **The cross term** of a pair of coprime primary primes (`chiF_mul_inv_pair`):
  `χ_p(q)·χ_q(p)⁻¹ = ρ_p(q)ρ_q(p)`, by round 298's sextic reciprocity.
* **`paired_gauss`**: for disjoint sets `A, B` of primary primes `∤ 6` with products `z₁, z₂`,
  `μ(z₁)μ(z₂)·γ(χ_{z₁}χ̄_{z₂}) = ā(z₁)·a(z₂)·χ_{z₁}(4)⁻¹·χ_{z₂}(4)·γ₃(z₁z₂)`. The proof combines
  round 300's `gamF_union`, `gamF_one_mul_two`, `gamF_one_mul_inv` and `GF_union` with
  `γ₃(z₂)² = χ_{z₂}(−1)`.
* **`pairFactor_eq_of_mod_four`**: the factor `χ_{z₁}(4)⁻¹·χ_{z₂}(4)·γ₃(z₁z₂)` is unchanged when
  `z₁, z₂` are replaced by products congruent to them modulo `4`, since `γ₃(z₁z₂) = Φ(z₁z₂)/2` and
  `Φ` depends only on the coordinates modulo `4` (round 299's `quadPhi_add_four`).
-/

open NumberField Complex Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- `ψ₁ = 1`: the trace character modulo a unit is trivial. -/
theorem ψc_one (x : 𝓞 K) : ψc 1 x = 1 := by
  obtain ⟨n, hn⟩ := exists_re_two_σO_div_δ3 x
  unfold ψc trPhase
  rw [mul_one, hn, fourierChar_intCast]

/-- `S_1(t) = 1`. -/
theorem sqSum_one_left (t : 𝓞 K) : sqSum 1 t = 1 := by
  have hR : Function.Bijective
      (fun p : Unit × 𝓞 K => (fun _ : Unit => (0 : 𝓞 K)) p.1 + 1 * p.2) := by
    constructor
    · rintro ⟨⟨⟩, u⟩ ⟨⟨⟩, u'⟩ h
      simp only [zero_add, one_mul] at h
      rw [h]
    · intro z; exact ⟨((), z), by simp⟩
  unfold sqSum
  rw [gaussTr_eq_sum 1 one_ne_zero _ (sq_periodic 1 t one_ne_zero) (fun _ => 0) hR 0]
  simp [ψc_one]

/-- **Chinese remainders for the twisted quadratic sums**: `S_{ab}(t) = S_a(tb)·S_b(ta)` for coprime
`a, b`. -/
theorem sqSum_mul_t (a b t : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsCoprime a b) :
    sqSum (a * b) t = sqSum a (t * b) * sqSum b (t * a) := by
  have : Finite (𝓞 K ⧸ span {a}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {a}) := Fintype.ofFinite _
  have : Finite (𝓞 K ⧸ span {b}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {b}) := Fintype.ofFinite _
  have hcrt := crt_rep_bijective a b ha hb hab (repQ a) (repQ b) (repQ_bijective a ha)
    (repQ_bijective b hb)
  have e1 := gaussTr_eq_sum (ι := (𝓞 K ⧸ span {a}) × (𝓞 K ⧸ span {b})) (a * b)
    (mul_ne_zero ha hb) (fun x => ψc (a * b) (t * (x * x)))
    (sq_periodic (a * b) t (mul_ne_zero ha hb))
    (fun q => b * repQ a q.1 + a * repQ b q.2) hcrt 0
  have e2 := gaussTr_eq_sum a ha (fun x => ψc a (t * b * (x * x))) (sq_periodic a (t * b) ha)
    (repQ a) (repQ_bijective a ha) 0
  have e3 := gaussTr_eq_sum b hb (fun x => ψc b (t * a * (x * x))) (sq_periodic b (t * a) hb)
    (repQ b) (repQ_bijective b hb) 0
  unfold sqSum
  rw [e1, e2, e3, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_zero, ψc_zero, mul_one]
  set r := repQ a i
  set s := repQ b j
  have hx : t * ((b * r + a * s) * (b * r + a * s)) =
      b * (t * b * (r * r)) + a * (t * a * (s * s)) + (a * b) * (2 * t * r * s) := by ring
  rw [hx, ψc_add, ψc_add, ψc_mul_right a b _ hb, mul_comm a b, ψc_mul_right b a _ ha,
    ψc_mul_self _ (mul_ne_zero hb ha), mul_one]

/-- **The twisted quadratic sum over pairwise coprime moduli**:
`S_{∏c_i}(t) = ∏_i S_{c_i}(t·∏_{j≠i} c_j)`. -/
theorem sqSum_prod {ι : Type*} [DecidableEq ι] (c : ι → 𝓞 K) (S : Finset ι)
    (hc0 : ∀ i ∈ S, c i ≠ 0) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (c i) (c j)) (t : 𝓞 K) :
    sqSum (∏ i ∈ S, c i) t = ∏ i ∈ S, sqSum (c i) (t * ∏ j ∈ S.erase i, c j) := by
  induction S using Finset.induction_on generalizing t with
  | empty => simp only [Finset.prod_empty]; exact sqSum_one_left t
  | @insert k S hk ih =>
    have hc0' : ∀ i ∈ S, c i ≠ 0 := fun i hi => hc0 i (Finset.mem_insert_of_mem hi)
    have hcop' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (c i) (c j) := fun i hi j hj =>
      hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hk0 : c k ≠ 0 := hc0 k (Finset.mem_insert_self k S)
    have hS0 : ∏ i ∈ S, c i ≠ 0 := Finset.prod_ne_zero_iff.2 hc0'
    have hkS : IsCoprime (c k) (∏ i ∈ S, c i) := IsCoprime.prod_right fun i hi =>
      hcop k (Finset.mem_insert_self k S) i (Finset.mem_insert_of_mem hi)
        (fun h => hk (h ▸ hi))
    rw [Finset.prod_insert hk, sqSum_mul_t (c k) (∏ i ∈ S, c i) t hk0 hS0 hkS, ih hc0' hcop',
      Finset.prod_insert hk, Finset.erase_insert hk]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    rw [Finset.erase_insert_of_ne hik.symm,
      Finset.prod_insert (fun h => hk (Finset.mem_of_mem_erase h)), mul_assoc]


section Jacobi

variable {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K) [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal]
  (h6 : ∀ i, (6 : 𝓞 K) ∉ span {π i})

/-- **The quadratic Gauss sum of a squarefree modulus**: `γ₃(n) = Φ(a, b)/2` for
`n = ∏_{i∈S} π_i = a + bω`, the paper's `γ₃(n) = Γ_quad(n)`. The Gauss sum of the Jacobi symbol
`∏_i ρ_{π_i}` is the quadratic sum `S_n(1)` of round 297, by the Chinese remainder theorem for both. -/
theorem gamF_three_eq (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))
    (a b : ℤ) (hab : ∏ i ∈ S, π i = a + b * ω) :
    gamF π S (fun i => chiF π h6 i ^ 3) = quadPhi a b / 2 := by
  have hn0 : ∏ i ∈ S, π i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_maximal (π i)
  have hterm : ∀ i ∈ S, chiF π h6 i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k)) ^ 3 *
      gamN (π i) (chiF π h6 i ^ 3) =
        sqSum (π i) (1 * ∏ k ∈ S.erase i, π k) / ((‖σO (π i)‖ : ℝ) : ℂ) := by
    intro i hi
    have ht : (∏ k ∈ S.erase i, π k) ∉ span {π i} := fun h =>
      mk_cofactor_ne_zero π S hcop hi (Ideal.Quotient.eq_zero_iff_mem.2 h)
    rw [one_mul, sqSum_prime (π i) (two_not_mem_of_six _ (h6 i)) _ ht, gamN,
      ← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0)]
    unfold chiF
    rw [chi6_cube, ψp, mul_div_assoc]
  have hnorm : ∏ i ∈ S, ((‖σO (π i)‖ : ℝ) : ℂ) = ((‖σO (∏ i ∈ S, π i)‖ : ℝ) : ℂ) := by
    rw [map_prod, norm_prod, Complex.ofReal_prod]
  rw [gamF_pow π h6 S hcop 3 (by simp), Finset.prod_congr rfl hterm, Finset.prod_div_distrib,
    ← sqSum_prod π S (fun i _ => ne_zero_of_maximal (π i)) hcop 1, sqSum_one, hnorm]
  have hσ : ((‖σO (∏ i ∈ S, π i)‖ : ℝ) : ℂ) ≠ 0 := by
    have : σO (∏ i ∈ S, π i) ≠ 0 := fun h => hn0 (σO_injective (h.trans (map_zero σO).symm))
    exact_mod_cast norm_ne_zero_iff.2 this
  have hq := quad_gauss_coords a b (hab ▸ hn0)
  rw [← hab] at hq
  rw [hq, quadPhi]
  field_simp
  push_cast
  ring


omit [DecidableEq ι] hP in
/-- `gamF` depends only on the characters at the primes of `S`. -/
theorem gamF_congr (S : Finset ι) (χ χ' : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ)
    (h : ∀ i ∈ S, χ i = χ' i) : gamF π S χ = gamF π S χ' := by
  unfold gamF
  congr 2
  funext z
  exact Finset.prod_congr rfl fun i hi => by rw [h i hi]

/-- `|γ(n)| = 1` for nontrivial characters of order dividing `6`. -/
theorem norm_gamF (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))
    (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) (hχ : ∀ i ∈ S, χ i ≠ 1)
    (h6' : ∀ i ∈ S, χ i ^ 6 = 1) : ‖gamF π S χ‖ = 1 := by
  rw [gamF_eq π S hcop χ hχ, norm_prod]
  refine Finset.prod_eq_one fun i hi => ?_
  have hu : IsUnit (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k)) :=
    isUnit_iff_ne_zero.2 (mk_cofactor_ne_zero π S hcop hi)
  have hpow : χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k)) ^ 6 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), h6' i hi, MulChar.one_apply hu]
  rw [norm_mul, norm_eq_one_of_pow_eq_one hpow (by norm_num), norm_gamN (π i) (hχ i hi), one_mul]

theorem norm_alphaN (p : 𝓞 K) [(span {p} : Ideal (𝓞 K)).IsMaximal] : ‖alphaN p‖ = 1 := by
  have h := norm_σO_ne_zero p
  have h' : ‖σO p‖ ≠ 0 := by exact_mod_cast h
  rw [alphaN, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self h']

omit [DecidableEq ι] in
theorem norm_chiF_four (i : ι) : ‖chiF π h6 i 4‖ = 1 :=
  norm_eq_one_of_pow_eq_one (chi6_four_pow_six (π i) (h6 i)) (by norm_num)

/-- **`χ_n(4)` through `n mod 2`**: `∏_{i∈S} χ_{π_i}(4) = σ(u)` for a cube root of unity
`u ≡ n (mod 2)`. -/
theorem prod_chi6_four (S : Finset ι) (hpr : ∀ i ∈ S, Primary (π i)) :
    ∃ u : 𝓞 K, u ^ 3 = 1 ∧
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) u =
        Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (∏ i ∈ S, π i) ∧
      ∏ i ∈ S, chiF π h6 i 4 = σO u := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pow 3, by simp, by simp⟩
  | @insert k S hk ih =>
    obtain ⟨u, hu3, hu2, hu⟩ := ih fun i hi => hpr i (Finset.mem_insert_of_mem hi)
    obtain ⟨v, hv3, hv2, hv⟩ := chi6_four (π k) (h6 k) (hpr k (Finset.mem_insert_self k S))
    refine ⟨v * u, by rw [mul_pow, hu3, hv3, one_mul], ?_, ?_⟩
    · rw [Finset.prod_insert hk, map_mul, map_mul, hu2, hv2]
    · rw [Finset.prod_insert hk, hu, map_mul]
      unfold chiF
      rw [hv]

open Classical in
/-- `γ₃(p)² = χ_p(−1)`. -/
theorem gamN_three_sq (p : 𝓞 K) [(span {p} : Ideal (𝓞 K)).IsMaximal]
    (hp6 : (6 : 𝓞 K) ∉ span {p}) :
    gamN p (chi6 (span {p}) hp6 ^ 3) ^ 2 = chi6 (span {p}) hp6 (-1) := by
  have hF := ringChar_ne_two_of_two p (two_not_mem_of_six _ hp6)
  have hρ1 : quadR (𝓞 K ⧸ span {p}) ℂ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
      (quadraticChar_ne_one hF)
  have hq : (quadR (𝓞 K ⧸ span {p}) ℂ).IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hsq := gaussSum_sq hρ1 hq (ψp_isPrimitive p)
  rw [card_eq_norm_sq] at hsq
  have hσ := norm_σO_ne_zero p
  have hm1 : chi6 (span {p}) hp6 (-1) ^ 2 = 1 := by
    rw [← map_pow, neg_one_sq, MulChar.map_one]
  have hc : quadR (𝓞 K ⧸ span {p}) ℂ (-1) = chi6 (span {p}) hp6 (-1) := by
    rw [← chi6_cube, MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), pow_succ, hm1, one_mul]
  rw [chi6_cube, gamN, div_pow, hsq, hc]
  field_simp

/-- **`γ₃(n)² = χ_n(−1)`** for `n = ∏_{i∈S} π_i`. -/
theorem gamF_three_sq (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j)) :
    gamF π S (fun i => chiF π h6 i ^ 3) ^ 2 = ∏ i ∈ S, chiF π h6 i (-1) := by
  rw [gamF_pow π h6 S hcop 3 (by simp), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mul_pow, ← pow_mul, show 3 * 2 = 6 by rfl,
    chi6_pow_six_of_ne_zero _ _ (mk_cofactor_ne_zero π S hcop hi), one_mul]
  exact gamN_three_sq (π i) (h6 i)


/-- The paper's column coefficient `a(n) = ᾱ(n)·γ₂(n)` for `n = ∏_{i∈S} π_i`. -/
def aF (S : Finset ι) : ℂ := conj (∏ i ∈ S, alphaN (π i)) * gamF π S (fun i => chiF π h6 i ^ 2)

omit [DecidableEq ι] in
theorem chiF_pow_pow_six (i : ι) (j : ℕ) : (chiF π h6 i ^ j) ^ 6 = 1 := by
  unfold chiF
  rw [← pow_mul, mul_comm, pow_mul, chi6_pow_six, one_pow]

theorem norm_aF (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j)) :
    ‖aF π h6 S‖ = 1 := by
  rw [aF, norm_mul, RCLike.norm_conj, norm_prod,
    Finset.prod_eq_one (fun i _ => norm_alphaN (π i)), one_mul]
  exact norm_gamF π S hcop _ (fun i _ => chi6_pow_ne_one _ (h6 i) (by norm_num))
    (fun i _ => chiF_pow_pow_six π h6 i 2)

omit [DecidableEq ι] in
open Classical in
/-- **The cross term of a pair**: `χ_p(q)·χ_q(p)⁻¹ = ρ_p(q)·ρ_q(p)` for coprime primary primes, by
round 298's sextic reciprocity. -/
theorem chiF_mul_inv_pair (i k : ι) (hi : Primary (π i)) (hk : Primary (π k))
    (hik : IsCoprime (π i) (π k)) :
    chiF π h6 i (Ideal.Quotient.mk (span {π i}) (π k)) *
        (chiF π h6 k)⁻¹ (Ideal.Quotient.mk (span {π k}) (π i)) =
      (chiF π h6 i ^ 3) (Ideal.Quotient.mk (span {π i}) (π k)) *
        (chiF π h6 k ^ 3) (Ideal.Quotient.mk (span {π k}) (π i)) := by
  have hr := sextic_recip (π i) (π k) (h6 i) (h6 k) hi hk hik
  have hx : Ideal.Quotient.mk (span {π i}) (π k) ≠ 0 := mk_ne_zero_of_coprime hik
  have hy : Ideal.Quotient.mk (span {π k}) (π i) ≠ 0 := mk_ne_zero_of_coprime hik.symm
  have hc0 := chi6_ne_zero_of_ne_zero (span {π i}) (h6 i) hx
  have hq1 := quadR_sq_eq_one (span {π i}) _ hx
  have hq2 := quadR_sq_eq_one (span {π k}) _ hy
  unfold chiF
  rw [MulChar.inv_apply_eq_inv', hr, chi6_cube, chi6_cube]
  have hq1' : quadR (𝓞 K ⧸ span {π i}) ℂ (Ideal.Quotient.mk (span {π i}) (π k)) ≠ 0 := by
    intro h; rw [h] at hq1; norm_num at hq1
  have hq2' : quadR (𝓞 K ⧸ span {π k}) ℂ (Ideal.Quotient.mk (span {π k}) (π i)) ≠ 0 := by
    intro h; rw [h] at hq2; norm_num at hq2
  field_simp
  linear_combination -((quadR (𝓞 K ⧸ span {π k}) ℂ (Ideal.Quotient.mk (span {π k}) (π i)) ^ 2 *
    hq1 + hq2))

/-- For `‖z‖ = 1`, `conj z = z⁻¹`. -/
theorem conj_eq_inv_of_norm {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]; simp


/-- **The paired Gauss sums** (the companion paper's `μ(z₁)μ(z₂)γ(χ_{z₁}χ̄_{z₂}) = Σ_ξ c_ξ a_ξ(z₁)ā_ξ(z₂)`,
before the expansion in `ξ`): for disjoint sets `A, B` of primary primes `∤ 6` with products
`z₁, z₂`, the normalized Gauss sum of the character `χ_{z₁}·χ̄_{z₂}` modulo `z₁z₂` satisfies
`μ(z₁)μ(z₂)·γ(χ_{z₁}χ̄_{z₂}) = ā(z₁)·a(z₂)·χ_{z₁}(4)⁻¹·χ_{z₂}(4)·γ₃(z₁z₂)`. -/
theorem paired_gauss (A B : Finset ι) (hAB : Disjoint A B)
    (hcop : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → IsCoprime (π i) (π j))
    (hpr : ∀ i ∈ A ∪ B, Primary (π i)) :
    (-1 : ℂ) ^ A.card * (-1) ^ B.card *
        gamF π (A ∪ B) (fun i => if i ∈ A then chiF π h6 i else (chiF π h6 i)⁻¹) =
      conj (aF π h6 A) * aF π h6 B * ((∏ i ∈ A, chiF π h6 i 4)⁻¹ * ∏ k ∈ B, chiF π h6 k 4) *
        gamF π (A ∪ B) (fun i => chiF π h6 i ^ 3) := by
  have hcA : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → IsCoprime (π i) (π j) := fun i hi j hj =>
    hcop i (Finset.mem_union_left _ hi) j (Finset.mem_union_left _ hj)
  have hcB : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → IsCoprime (π i) (π j) := fun i hi j hj =>
    hcop i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj)
  have hpA : ∀ i ∈ A, Primary (π i) := fun i hi => hpr i (Finset.mem_union_left _ hi)
  have hpB : ∀ i ∈ B, Primary (π i) := fun i hi => hpr i (Finset.mem_union_right _ hi)
  set mixed : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ :=
    fun i => if i ∈ A then chiF π h6 i else (chiF π h6 i)⁻¹ with hmixed
  -- the named quantities
  set g1A := gamF π A (fun i => chiF π h6 i) with hg1A
  set g2A := gamF π A (fun i => chiF π h6 i ^ 2) with hg2A
  set g1B := gamF π B (fun i => chiF π h6 i) with hg1B
  set g2B := gamF π B (fun i => chiF π h6 i ^ 2) with hg2B
  set gmB := gamF π B (fun i => (chiF π h6 i)⁻¹) with hgmB
  set g3B := gamF π B (fun i => chiF π h6 i ^ 3) with hg3B
  set g3AB := gamF π (A ∪ B) (fun i => chiF π h6 i ^ 3) with hg3AB
  set αA := ∏ i ∈ A, alphaN (π i) with hαA
  set αB := ∏ i ∈ B, alphaN (π i) with hαB
  set cA := ∏ i ∈ A, chiF π h6 i 4 with hcA'
  set cB := ∏ i ∈ B, chiF π h6 i 4 with hcB'
  set X := ∏ i ∈ A, ∏ k ∈ B, ((chiF π h6 i ^ 3) (Ideal.Quotient.mk (span {π i}) (π k)) *
    (chiF π h6 k ^ 3) (Ideal.Quotient.mk (span {π k}) (π i))) with hX
  set μA : ℂ := (-1) ^ A.card with hμA
  set μB : ℂ := (-1) ^ B.card with hμB
  -- norms and non-vanishing
  have n1A : ‖g1A‖ = 1 := norm_gamF π A hcA _ (fun i _ => chi6_ne_one (π i) (h6 i))
    (fun i _ => by have := chiF_pow_pow_six π h6 i 1; rwa [pow_one] at this)
  have n2A : ‖g2A‖ = 1 := norm_gamF π A hcA _ (fun i _ => chi6_pow_ne_one _ (h6 i) (by norm_num))
    (fun i _ => chiF_pow_pow_six π h6 i 2)
  have n1B : ‖g1B‖ = 1 := norm_gamF π B hcB _ (fun i _ => chi6_ne_one (π i) (h6 i))
    (fun i _ => by have := chiF_pow_pow_six π h6 i 1; rwa [pow_one] at this)
  have n2B : ‖g2B‖ = 1 := norm_gamF π B hcB _ (fun i _ => chi6_pow_ne_one _ (h6 i) (by norm_num))
    (fun i _ => chiF_pow_pow_six π h6 i 2)
  have nαA : ‖αA‖ = 1 := by
    rw [hαA, norm_prod]; exact Finset.prod_eq_one fun i _ => norm_alphaN (π i)
  have nαB : ‖αB‖ = 1 := by
    rw [hαB, norm_prod]; exact Finset.prod_eq_one fun i _ => norm_alphaN (π i)
  have ncA : ‖cA‖ = 1 := by
    rw [hcA', norm_prod]; exact Finset.prod_eq_one fun i _ => norm_chiF_four π h6 i
  have ncB : ‖cB‖ = 1 := by
    rw [hcB', norm_prod]; exact Finset.prod_eq_one fun i _ => norm_chiF_four π h6 i
  have ne : ∀ {z : ℂ}, ‖z‖ = 1 → z ≠ 0 := fun h h0 => by rw [h0, norm_zero] at h; norm_num at h
  have hμA2 : μA ^ 2 = 1 := by rw [hμA, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hμB2 : μB ^ 2 = 1 := by rw [hμB, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hμA0 : μA ≠ 0 := by rw [hμA]; exact pow_ne_zero _ (by norm_num)
  have hμB0 : μB ≠ 0 := by rw [hμB]; exact pow_ne_zero _ (by norm_num)
  -- the relations
  have e1 : gamF π (A ∪ B) mixed = g1A * gmB * X := by
    rw [gamF_union π A B hAB hcop mixed (fun i _ => by
      simp only [hmixed]; split_ifs
      · exact chi6_ne_one (π i) (h6 i)
      · exact inv_ne_one.2 (chi6_ne_one (π i) (h6 i))), cross_union_prod]
    have hA' : gamF π A mixed = g1A := gamF_congr π A _ _ fun i hi => by
      simp only [hmixed, ite_eq_left hi]
    have hB' : gamF π B mixed = gmB := gamF_congr π B _ _ fun i hi => by
      simp only [hmixed, ite_eq_right (Finset.disjoint_right.1 hAB hi)]
    rw [hA', hB']
    congr 1
    refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun k hk => ?_
    have hik : i ≠ k := fun h => Finset.disjoint_left.1 hAB hi (h ▸ hk)
    have hkA : k ∉ A := Finset.disjoint_right.1 hAB hk
    simp only [hmixed, ite_eq_left hi, ite_eq_right hkA]
    exact chiF_mul_inv_pair π h6 i k (hpA i hi) (hpB k hk)
      (hcop i (Finset.mem_union_left _ hi) k (Finset.mem_union_right _ hk) hik)
  have e2 : GF π h6 (A ∪ B) = GF π h6 A * GF π h6 B * X := GF_union π h6 A B hAB hcop
  have e3 : g1A * g2A = μA * αA * GF π h6 A := by
    have h := gamF_one_mul_two π h6 A hcA hpA
    have hc1 : gamF π A (fun i => chiF π h6 i ^ 1) = g1A := gamF_congr π A _ _ fun i _ => pow_one _
    rwa [hc1] at h
  have e4 : g1B * g2B = μB * αB * GF π h6 B := by
    have h := gamF_one_mul_two π h6 B hcB hpB
    have hc1 : gamF π B (fun i => chiF π h6 i ^ 1) = g1B := gamF_congr π B _ _ fun i _ => pow_one _
    rwa [hc1] at h
  have e5 : g1B * gmB = ∏ i ∈ B, chiF π h6 i (-1) := gamF_one_mul_inv π h6 B hcB
  have e6 : g3B ^ 2 = ∏ i ∈ B, chiF π h6 i (-1) := gamF_three_sq π h6 B hcB
  have e7B : GF π h6 B = cB⁻¹ * g3B := by
    rw [GF, Finset.prod_inv_distrib]
  have e7AB : GF π h6 (A ∪ B) = (cA * cB)⁻¹ * g3AB := by
    rw [GF, Finset.prod_inv_distrib, Finset.prod_union hAB, mul_inv]
  -- solve for the quantities to eliminate
  have s1 : g1A = μA * αA * GF π h6 A / g2A := by
    rw [eq_div_iff (ne n2A)]; exact e3
  have s2 : gmB = g3B ^ 2 / g1B := by
    rw [eq_div_iff (ne n1B), e6, ← e5]; ring
  have s3 : g1B = μB * αB * GF π h6 B / g2B := by
    rw [eq_div_iff (ne n2B)]; exact e4
  have s4 : g3B = cB * GF π h6 B := by
    rw [e7B, ← mul_assoc, mul_inv_cancel₀ (ne ncB), one_mul]
  have s5 : g3AB = cA * cB * (GF π h6 A * GF π h6 B * X) := by
    rw [← e2, e7AB, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (ne ncA) (ne ncB)), one_mul]
  have hGB0 : GF π h6 B ≠ 0 := by
    intro h0
    have : g3B = 0 := by rw [s4, h0, mul_zero]
    have hn3 : ‖g3B‖ = 1 := norm_gamF π B hcB _
      (fun i _ => chi6_pow_ne_one _ (h6 i) (by norm_num)) (fun i _ => chiF_pow_pow_six π h6 i 3)
    rw [this, norm_zero] at hn3; norm_num at hn3
  -- the identity
  have hconjA : conj (aF π h6 A) = αA * g2A⁻¹ := by
    rw [aF, map_mul, Complex.conj_conj, conj_eq_inv_of_norm n2A]
  have hconjB : aF π h6 B = αB⁻¹ * g2B := by
    rw [aF, conj_eq_inv_of_norm nαB]
  rw [e1, hconjA, hconjB, s2, s3, s4, s1, s5]
  have hαA0 := ne nαA
  have hαB0 := ne nαB
  have hg2A0 := ne n2A
  have hg2B0 := ne n2B
  have hcA0 := ne ncA
  have hcB0 := ne ncB
  field_simp
  linear_combination (GF π h6 A * X) * hμA2


/-- `χ_n(4)` depends only on `n mod 2`: if `∏_{i∈A} π_i ≡ ∏_{i∈A'} π_i (mod 2)` then
`∏_{i∈A} χ_i(4) = ∏_{i∈A'} χ_i(4)`. -/
theorem prod_chi6_four_eq (A A' : Finset ι) (hpr : ∀ i ∈ A, Primary (π i))
    (hpr' : ∀ i ∈ A', Primary (π i))
    (h2 : (∏ i ∈ A, π i) - ∏ i ∈ A', π i ∈ span {(2 : 𝓞 K)}) :
    ∏ i ∈ A, chiF π h6 i 4 = ∏ i ∈ A', chiF π h6 i 4 := by
  obtain ⟨u, hu3, hu2, hu⟩ := prod_chi6_four π h6 A hpr
  obtain ⟨v, hv3, hv2, hv⟩ := prod_chi6_four π h6 A' hpr'
  have huv : u = v := by
    apply cube_eq_of_mk_eq (span {(2 : 𝓞 K)}) three_not_mem_span_two hu3 hv3
    rw [hu2, hv2, Ideal.Quotient.eq]; exact h2
  rw [hu, hv, huv]

/-- **The paired factor depends only on the classes modulo `4`**: the factor
`χ_{z₁}(4)⁻¹·χ_{z₂}(4)·γ₃(z₁z₂)` of `paired_gauss` is unchanged when `z₁ = ∏_A π_i` and
`z₂ = ∏_B π_i` are replaced by products `z₁' ≡ z₁`, `z₂' ≡ z₂ (mod 4)`. -/
theorem pairFactor_eq_of_mod_four (A B A' B' : Finset ι)
    (hcop : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → IsCoprime (π i) (π j))
    (hcop' : ∀ i ∈ A' ∪ B', ∀ j ∈ A' ∪ B', i ≠ j → IsCoprime (π i) (π j))
    (hAB : Disjoint A B) (hAB' : Disjoint A' B')
    (hpr : ∀ i ∈ A ∪ B, Primary (π i)) (hpr' : ∀ i ∈ A' ∪ B', Primary (π i))
    (h1 : (∏ i ∈ A, π i) - ∏ i ∈ A', π i ∈ span {(4 : 𝓞 K)})
    (h2 : (∏ i ∈ B, π i) - ∏ i ∈ B', π i ∈ span {(4 : 𝓞 K)}) :
    (∏ i ∈ A, chiF π h6 i 4)⁻¹ * (∏ k ∈ B, chiF π h6 k 4) *
        gamF π (A ∪ B) (fun i => chiF π h6 i ^ 3) =
      (∏ i ∈ A', chiF π h6 i 4)⁻¹ * (∏ k ∈ B', chiF π h6 k 4) *
        gamF π (A' ∪ B') (fun i => chiF π h6 i ^ 3) := by
  have h42 : ∀ x : 𝓞 K, x ∈ span {(4 : 𝓞 K)} → x ∈ span {(2 : 𝓞 K)} := fun x hx => by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨2 * d, by ring⟩
  rw [prod_chi6_four_eq π h6 A A' (fun i hi => hpr i (Finset.mem_union_left _ hi))
      (fun i hi => hpr' i (Finset.mem_union_left _ hi)) (h42 _ h1),
    prod_chi6_four_eq π h6 B B' (fun i hi => hpr i (Finset.mem_union_right _ hi))
      (fun i hi => hpr' i (Finset.mem_union_right _ hi)) (h42 _ h2)]
  congr 1
  -- `γ₃` through the coordinates of `z₁z₂` modulo `4`
  obtain ⟨x, y, hxy⟩ := exists_coords ((∏ i ∈ A, π i) * ∏ i ∈ B, π i)
  have hprod : ∏ i ∈ A ∪ B, π i = (x : 𝓞 K) + (y : 𝓞 K) * ω := by
    rw [Finset.prod_union hAB, hxy]
  have h4 : ((∏ i ∈ A, π i) * ∏ i ∈ B, π i) - (∏ i ∈ A', π i) * ∏ i ∈ B', π i ∈
      span {(4 : 𝓞 K)} := by
    have : ((∏ i ∈ A, π i) * ∏ i ∈ B, π i) - (∏ i ∈ A', π i) * ∏ i ∈ B', π i =
        ((∏ i ∈ A, π i) - ∏ i ∈ A', π i) * ∏ i ∈ B, π i +
          (∏ i ∈ A', π i) * ((∏ i ∈ B, π i) - ∏ i ∈ B', π i) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h4
  obtain ⟨a, b, hab⟩ := exists_coords d
  have hprod' : ∏ i ∈ A' ∪ B', π i =
      ((x - 4 * a : ℤ) : 𝓞 K) + ((y - 4 * b : ℤ) : 𝓞 K) * ω := by
    rw [Finset.prod_union hAB']
    have : (∏ i ∈ A', π i) * ∏ i ∈ B', π i = ((∏ i ∈ A, π i) * ∏ i ∈ B, π i) - d * 4 := by
      rw [hd]; ring
    rw [this, hxy, hab]; push_cast; ring
  rw [gamF_three_eq π h6 (A ∪ B) hcop x y hprod, gamF_three_eq π h6 (A' ∪ B') hcop' _ _ hprod',
    show x - 4 * a = x + 4 * (-a) by ring, show y - 4 * b = y + 4 * (-b) by ring, quadPhi_add_four]

end Jacobi

end Eis

end

#print axioms Eis.ψc_one
#print axioms Eis.sqSum_one_left
#print axioms Eis.sqSum_mul_t
#print axioms Eis.sqSum_prod
#print axioms Eis.gamF_three_eq
#print axioms Eis.gamF_congr
#print axioms Eis.norm_gamF
#print axioms Eis.norm_alphaN
#print axioms Eis.norm_chiF_four
#print axioms Eis.prod_chi6_four
#print axioms Eis.gamN_three_sq
#print axioms Eis.gamF_three_sq
#print axioms Eis.norm_aF
#print axioms Eis.chiF_mul_inv_pair
#print axioms Eis.paired_gauss
#print axioms Eis.prod_chi6_four_eq
#print axioms Eis.pairFactor_eq_of_mod_four
