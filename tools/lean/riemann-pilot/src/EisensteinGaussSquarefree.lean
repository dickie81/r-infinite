import EisensteinGaussPrime

/-! # The companion paper's Lemma 4.1 for squarefree moduli (round 300)

S3 of round 291's plan, part 6. For `n = ∏_{i∈S} π_i`, a product of distinct primes, and characters
`χ_i` modulo `π_i`, the normalized Gauss sum `γ(n) = G_n(∏_i χ_i, 1)/|σn|` (`gamF`) is round 295's
Gauss transform at frequency `1`.

* **The Chinese remainder factorization** (**`gamF_eq`**): `γ(n) = ∏_i χ_i(n/π_i)·γ(π_i)` for
  nontrivial `χ_i`, from round 295's `gaussTr_prod_primes`. For disjoint sets of primes
  (**`gamF_union`**), `γ(ab) = γ(a)·γ(b)·∏_{i∣a} χ_i(b)·∏_{k∣b} χ_k(a)`.
* **The sextic characters** `χ_i = χ_{π_i}` of distinct primary primes `π_i ∤ 6` (`chiF`), with
  `γ_j(n)` the Gauss sum of the `χ_i^j` and `μ(n) = (−1)^{|S|}`:
  - **`gamF_two_cube`**: `γ₂(n)³ = μ(n)·∏_i α(π_i)`, and `∏_i α(π_i)` is `α(n) = σn/|σn|`;
  - **`gamF_one_mul_two`**: `γ₁(n)γ₂(n) = μ(n)·∏_i α(π_i)·G(n)`, where `G(n) = ∏_i χ_i(4)⁻¹·γ₃(n)`
    (`GF`);
  - **`gamF_one_mul_inv`**: `γ₁(n)γ₋₁(n) = ∏_i χ_i(−1)`.

  The cross phases are sixth roots of unity, so they cancel in the cube and in `γ₁γ₋₁`, and combine
  to `χ_i(n/π_i)³` in `γ₁γ₂`.
* **The multiplicative laws** for disjoint sets of primes `A, B`:
  - **`GF_union`**: `G(ab) = G(a)·G(b)·∏_{p∣a, q∣b} ρ_p(q)ρ_q(p)`. By round 298 each factor is the
    paper's `R(p, q)`.
  - **`gamF_two_union`**: `γ₂(ab) = γ₂(a)·γ₂(b)·∏_{p∣a, q∣b} χ_q(p)⁴`, by cubic reciprocity in the
    form `χ_p(q)² = χ_q(p)²` (`chi6_sq_recip`). With `α` and `ξ` multiplicative this is the paper's
    `a_ξ(ab) = a_ξ(a)a_ξ(b)χ_b(a)⁴`.
-/

open NumberField Complex Ideal

noncomputable section

namespace Eis

section Squarefree

variable {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K) [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal]

/-- The normalized Gauss sum of a family of characters modulo `n = ∏_{i∈S} π_i`:
`γ(n) = G_n(∏_i χ_i, 1)/|σn|`. -/
def gamF (S : Finset ι) (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) : ℂ :=
  gaussTr (∏ i ∈ S, π i) (fun z => ∏ i ∈ S, χ i (Ideal.Quotient.mk (span {π i}) z)) 1 /
    ((‖σO (∏ i ∈ S, π i)‖ : ℝ) : ℂ)

/-- **The Chinese remainder factorization**: `γ(n) = ∏_i χ_i(n/π_i)·γ(π_i)`. -/
theorem gamF_eq (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))
    (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) (hχ : ∀ i ∈ S, χ i ≠ 1) :
    gamF π S χ = ∏ i ∈ S, (χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k)) *
      gamN (π i) (χ i)) := by
  rw [gamF, gaussTr_prod_primes π S hcop χ hχ 1, map_prod, norm_prod, Complex.ofReal_prod,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_one, MulChar.map_one, mul_one, gamN, ψp, mul_div_assoc]

/-- **Splitting the modulus**: for disjoint `A, B`, `γ(ab) = γ(a)·γ(b)·∏_{i∈A} χ_i(b)·∏_{k∈B} χ_k(a)`. -/
theorem gamF_union (A B : Finset ι) (hAB : Disjoint A B)
    (hcop : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → IsCoprime (π i) (π j))
    (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) (hχ : ∀ i ∈ A ∪ B, χ i ≠ 1) :
    gamF π (A ∪ B) χ = gamF π A χ * gamF π B χ *
      ((∏ i ∈ A, χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ B, π k))) *
        ∏ k ∈ B, χ k (Ideal.Quotient.mk (span {π k}) (∏ i ∈ A, π i))) := by
  have hA : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → IsCoprime (π i) (π j) := fun i hi j hj =>
    hcop i (Finset.mem_union_left _ hi) j (Finset.mem_union_left _ hj)
  have hB : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → IsCoprime (π i) (π j) := fun i hi j hj =>
    hcop i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj)
  rw [gamF_eq π (A ∪ B) hcop χ hχ, gamF_eq π A hA χ (fun i hi => hχ i (Finset.mem_union_left _ hi)),
    gamF_eq π B hB χ (fun i hi => hχ i (Finset.mem_union_right _ hi)), Finset.prod_union hAB]
  have eA : ∀ i ∈ A, χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ (A ∪ B).erase i, π k)) =
      χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ A.erase i, π k)) *
        χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ B, π k)) := by
    intro i hi
    have hiB : i ∉ B := Finset.disjoint_left.1 hAB hi
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hiB,
      Finset.prod_union (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hAB), map_mul,
      map_mul]
  have eB : ∀ k ∈ B, χ k (Ideal.Quotient.mk (span {π k}) (∏ j ∈ (A ∪ B).erase k, π j)) =
      χ k (Ideal.Quotient.mk (span {π k}) (∏ j ∈ B.erase k, π j)) *
        χ k (Ideal.Quotient.mk (span {π k}) (∏ i ∈ A, π i)) := by
    intro k hk
    have hkA : k ∉ A := Finset.disjoint_right.1 hAB hk
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hkA,
      Finset.prod_union (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hAB), map_mul,
      map_mul, mul_comm (χ k (Ideal.Quotient.mk (span {π k}) (∏ i ∈ A, π i)))]
  have hA' : ∏ i ∈ A, (χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ (A ∪ B).erase i, π k)) *
      gamN (π i) (χ i)) = ∏ i ∈ A, ((χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ A.erase i, π k)) *
        gamN (π i) (χ i)) * χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ B, π k))) :=
    Finset.prod_congr rfl fun i hi => by rw [eA i hi]; ring
  have hB' : ∏ k ∈ B, (χ k (Ideal.Quotient.mk (span {π k}) (∏ j ∈ (A ∪ B).erase k, π j)) *
      gamN (π k) (χ k)) = ∏ k ∈ B, ((χ k (Ideal.Quotient.mk (span {π k}) (∏ j ∈ B.erase k, π j)) *
        gamN (π k) (χ k)) * χ k (Ideal.Quotient.mk (span {π k}) (∏ i ∈ A, π i))) :=
    Finset.prod_congr rfl fun k hk => by rw [eB k hk]; ring
  rw [hA', hB']
  simp only [Finset.prod_mul_distrib]
  ring

end Squarefree

section SexticSquarefree

variable {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K) [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal]
  (h6 : ∀ i, (6 : 𝓞 K) ∉ span {π i})

/-- The sextic characters `χ_i = χ_{π_i}`. -/
abbrev chiF (i : ι) : MulChar (𝓞 K ⧸ span {π i}) ℂ := chi6 (span {π i}) (h6 i)

/-- The paper's `G(n) = χ̄_n(4)·γ₃(n)` for `n = ∏_{i∈S} π_i`, with `χ̄_n(4) = ∏_i χ_i(4)⁻¹`. -/
def GF (S : Finset ι) : ℂ :=
  (∏ i ∈ S, (chiF π h6 i 4)⁻¹) * gamF π S (fun i => chiF π h6 i ^ 3)

/-- A residue prime to `π` is a unit modulo `π`. -/
theorem mk_ne_zero_of_coprime {a b : 𝓞 K} [(span {a} : Ideal (𝓞 K)).IsMaximal] (hab : IsCoprime a b) :
    Ideal.Quotient.mk (span {a}) b ≠ 0 := fun h =>
  not_isUnit_of_maximal a (hab.isUnit_of_dvd' dvd_rfl
    (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)))

/-- The cofactor `n/π_i` is a unit modulo `π_i`. -/
theorem mk_cofactor_ne_zero (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))
    {i : ι} (hi : i ∈ S) :
    Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k) ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.prod_mem_iff] at h
  obtain ⟨k, hk, hmem⟩ := h
  exact mk_ne_zero_of_coprime (hcop i hi k (Finset.mem_of_mem_erase hk)
    (Finset.ne_of_mem_erase hk).symm) (Ideal.Quotient.eq_zero_iff_mem.2 hmem)

theorem chi6_pow_six_of_ne_zero (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P)
    {x : 𝓞 K ⧸ P} (hx : x ≠ 0) : chi6 P hP6 x ^ 6 = 1 := by
  rw [← MulChar.pow_apply' _ (by norm_num), chi6_pow_six, MulChar.one_apply (isUnit_iff_ne_zero.2 hx)]

theorem chi6_ne_zero_of_ne_zero (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P)
    {x : 𝓞 K ⧸ P} (hx : x ≠ 0) : chi6 P hP6 x ≠ 0 := by
  intro h0
  have := chi6_pow_six_of_ne_zero P hP6 hx
  rw [h0] at this; norm_num at this

end SexticSquarefree

section LemmaSquarefree

variable {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K) [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal]
  (h6 : ∀ i, (6 : 𝓞 K) ∉ span {π i}) (S : Finset ι)
  (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))

include hcop in
/-- `γ_j(n) = ∏_i χ_i(n/π_i)^j·γ_j(π_i)` for `j = 1, 2, 3`. -/
theorem gamF_pow (j : ℕ) (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    gamF π S (fun i => chiF π h6 i ^ j) = ∏ i ∈ S,
      (chiF π h6 i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k)) ^ j *
        gamN (π i) (chiF π h6 i ^ j)) := by
  have hj0 : j ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega
  rw [gamF_eq π S hcop _ fun i _ => chi6_pow_ne_one _ (h6 i) hj]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MulChar.pow_apply' _ hj0]

include hcop in
/-- **`γ₂(n)³ = μ(n)α(n)`** for `n = ∏_{i∈S} π_i` with distinct primary primes `π_i ∤ 6`. -/
theorem gamF_two_cube (hpr : ∀ i ∈ S, Primary (π i)) :
    gamF π S (fun i => chiF π h6 i ^ 2) ^ 3 = (-1) ^ S.card * ∏ i ∈ S, alphaN (π i) := by
  rw [gamF_pow π h6 S hcop 2 (by simp), ← Finset.prod_pow, Finset.pow_card_mul_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mul_pow, gamN_two_cube (π i) (h6 i) (hpr i hi), ← pow_mul,
    show 2 * 3 = 6 by rfl, chi6_pow_six_of_ne_zero _ _ (mk_cofactor_ne_zero π S hcop hi)]
  ring

include hcop in
/-- **`γ₁(n)γ₂(n) = μ(n)α(n)G(n)`** with `G(n) = χ̄_n(4)γ₃(n)`. -/
theorem gamF_one_mul_two (hpr : ∀ i ∈ S, Primary (π i)) :
    gamF π S (fun i => chiF π h6 i ^ 1) * gamF π S (fun i => chiF π h6 i ^ 2) =
      (-1) ^ S.card * (∏ i ∈ S, alphaN (π i)) * GF π h6 S := by
  set x : ι → ℂ := fun i => chiF π h6 i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ S.erase i, π k))
    with hx
  have e1 : gamF π S (fun i => chiF π h6 i ^ 1) * gamF π S (fun i => chiF π h6 i ^ 2) =
      ∏ i ∈ S, (-alphaN (π i) * ((chiF π h6 i 4)⁻¹ *
        (x i ^ 3 * gamN (π i) (chiF π h6 i ^ 3)))) := by
    rw [gamF_pow π h6 S hcop 1 (by simp), gamF_pow π h6 S hcop 2 (by simp),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have h := gamN_one_mul_two (π i) (h6 i) (hpr i hi)
    rw [pow_one, pow_one]
    calc x i * gamN (π i) (chiF π h6 i) * (x i ^ 2 * gamN (π i) (chiF π h6 i ^ 2))
        = x i ^ 3 * (gamN (π i) (chiF π h6 i) * gamN (π i) (chiF π h6 i ^ 2)) := by ring
      _ = _ := by unfold chiF at *; rw [h]; ring
  rw [e1, GF, gamF_pow π h6 S hcop 3 (by simp), Finset.prod_mul_distrib, Finset.prod_neg,
    Finset.prod_mul_distrib]

include hcop in
/-- **`γ₁(n)γ₋₁(n) = χ_n(−1)`**. -/
theorem gamF_one_mul_inv :
    gamF π S (fun i => chiF π h6 i) * gamF π S (fun i => (chiF π h6 i)⁻¹) =
      ∏ i ∈ S, chiF π h6 i (-1) := by
  rw [gamF_eq π S hcop _ fun i _ => chi6_ne_one (π i) (h6 i),
    gamF_eq π S hcop _ fun i _ => inv_ne_one.2 (chi6_ne_one (π i) (h6 i)), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have h := gamN_one_mul_inv (π i) (h6 i)
  have hx := chi6_ne_zero_of_ne_zero _ (h6 i) (mk_cofactor_ne_zero π S hcop hi)
  rw [MulChar.inv_apply_eq_inv']
  unfold chiF at *
  rw [← h]
  field_simp

end LemmaSquarefree

section Union

variable {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K) [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal]
  (h6 : ∀ i, (6 : 𝓞 K) ∉ span {π i})

/-- **The cubic reciprocity of squares**: `χ_b(a)² = χ_a(b)²` for coprime primary primes `a, b ∤ 6`. -/
theorem chi6_sq_recip (a b : 𝓞 K) [(span {a} : Ideal (𝓞 K)).IsMaximal]
    [(span {b} : Ideal (𝓞 K)).IsMaximal] (ha6 : (6 : 𝓞 K) ∉ span {a})
    (hb6 : (6 : 𝓞 K) ∉ span {b}) (ha : Primary a) (hb : Primary b) (hab : IsCoprime a b) :
    (chi6 (span {b}) hb6 ^ 2) (Ideal.Quotient.mk _ a) =
      (chi6 (span {a}) ha6 ^ 2) (Ideal.Quotient.mk _ b) := by
  have h3a := three_not_mem_of_six (span {a}) ha6
  have h3b := three_not_mem_of_six (span {b}) hb6
  have h := cub_recip ha hb hab
  rw [cub_prime, cub_prime, chi3_eq h3b, chi3_eq h3a] at h
  rw [chi6_sq, chi6_sq]
  simp only [cubCharC, MulChar.ringHomComp_apply]
  rw [h]

omit [DecidableEq ι] hP in
/-- The cross phase of a union, as a double product over the two sets of primes. -/
theorem cross_union_prod (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) (A B : Finset ι) :
    (∏ i ∈ A, χ i (Ideal.Quotient.mk (span {π i}) (∏ k ∈ B, π k))) *
        ∏ k ∈ B, χ k (Ideal.Quotient.mk (span {π k}) (∏ i ∈ A, π i)) =
      ∏ i ∈ A, ∏ k ∈ B, (χ i (Ideal.Quotient.mk (span {π i}) (π k)) *
        χ k (Ideal.Quotient.mk (span {π k}) (π i))) := by
  simp only [map_prod, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (s := B) (t := A)]

/-- **`G(ab) = G(a)·G(b)·∏_{p∣a, q∣b} ρ_p(q)ρ_q(p)`** for disjoint sets of primes; by round 298 each
factor `ρ_p(q)ρ_q(p)` is the paper's `R(p, q) = Γ_quad(pq)/(Γ_quad(p)Γ_quad(q))`. -/
theorem GF_union (A B : Finset ι) (hAB : Disjoint A B)
    (hcop : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → IsCoprime (π i) (π j)) :
    GF π h6 (A ∪ B) = GF π h6 A * GF π h6 B *
      ∏ i ∈ A, ∏ k ∈ B, ((chiF π h6 i ^ 3) (Ideal.Quotient.mk (span {π i}) (π k)) *
        (chiF π h6 k ^ 3) (Ideal.Quotient.mk (span {π k}) (π i))) := by
  rw [GF, GF, GF, gamF_union π A B hAB hcop _ fun i _ => chi6_pow_ne_one _ (h6 i) (by simp),
    cross_union_prod, Finset.prod_union hAB]
  ring

/-- **The paper's `a_ξ(ab) = a_ξ(a)a_ξ(b)χ_b(a)⁴`**, through `γ₂`: for disjoint sets of primary primes,
`γ₂(ab) = γ₂(a)·γ₂(b)·∏_{p∣a, q∣b} χ_q(p)⁴`, by cubic reciprocity. -/
theorem gamF_two_union (A B : Finset ι) (hAB : Disjoint A B)
    (hcop : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → IsCoprime (π i) (π j))
    (hpr : ∀ i ∈ A ∪ B, Primary (π i)) :
    gamF π (A ∪ B) (fun i => chiF π h6 i ^ 2) =
      gamF π A (fun i => chiF π h6 i ^ 2) * gamF π B (fun i => chiF π h6 i ^ 2) *
        ∏ i ∈ A, ∏ k ∈ B, chiF π h6 k (Ideal.Quotient.mk (span {π k}) (π i)) ^ 4 := by
  rw [gamF_union π A B hAB hcop _ fun i _ => chi6_pow_ne_one _ (h6 i) (by simp), cross_union_prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun k hk => ?_
  have hik : i ≠ k := fun h => Finset.disjoint_left.1 hAB hi (h ▸ hk)
  have hc := hcop i (Finset.mem_union_left _ hi) k (Finset.mem_union_right _ hk) hik
  have hr := chi6_sq_recip (π k) (π i) (h6 k) (h6 i) (hpr k (Finset.mem_union_right _ hk))
    (hpr i (Finset.mem_union_left _ hi)) hc.symm
  unfold chiF
  rw [hr, MulChar.pow_apply' _ two_ne_zero]
  ring

end Union

end Eis

end

#print axioms Eis.gamF_eq
#print axioms Eis.gamF_union
#print axioms Eis.gamF_two_cube
#print axioms Eis.gamF_one_mul_two
#print axioms Eis.gamF_one_mul_inv
#print axioms Eis.chi6_sq_recip
#print axioms Eis.GF_union
#print axioms Eis.gamF_two_union
