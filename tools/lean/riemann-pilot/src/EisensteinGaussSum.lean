import EisensteinCubicRecip

/-! # S3, part 1: Gauss sums at a prime of `ℤ[ω]` (round 292)

The Gauss-sum layer of the round-291 plan starts at a single prime. For a maximal `P` and any primitive
additive character `ψ` of `𝓞/P` with values in `ℂ`:

* **The cubic Gauss sum** (`cubCharC`, the cubic character composed with the embedding `σ`):
  - **`gaussSum_cubCharC_cube`**: `g(χ_P, ψ)³ = −N(P)·π` for `P = (π)` with `π ≡ 1 (mod 3)`. Mathlib's
    `gaussSum_pow_eq_prod_jacobiSum` gives `g³ = χ(−1)·N(P)·J(χ, χ)`, and round 290's `jacobiSum_eq_neg` gives
    `J = −π`. This is the release's `cubicGauss_normalized_cube_breveE` before normalization.
  - `norm_gaussSum_cubCharC_sq`: `|g(χ_P, ψ)|² = N(P)`.
* **Duplication** (general finite fields of odd characteristic, `ρ` the quadratic character):
  - `jacobiSum_self_dup`: `χ(4)·J(χ, χ) = J(χ, ρ)`, from `4x(1 − x) = 1 − (2x − 1)²` and the count
    `#{u : u² = t} = 1 + ρ(t)` (`sum_sq_eq`, from Mathlib's `quadraticChar_card_sqrts`);
  - `gaussSum_dup`, the Hasse–Davenport product formula for `m = 2`: `χ(4)·g(χ)·g(χρ) = g(χ²)·g(ρ)`.
* **The sextic character** of round 281 (`chi6`), away from `6`:
  - `chi6_sq`: its square is the cubic character; `chi6_cube`: its cube is `ρ` (Euler's criterion,
    Mathlib's `quadraticChar_eq_pow_of_char_ne_two'`);
  - **`gaussSum_chi6`**: `χ₆(4)·g(χ₆)·N(P) = g(χ₃)²·g(ρ)`. So the sextic Gauss sum is the square of the cubic
    one times the quadratic one, up to the unit `χ₆(4)` and the factor `N(P)`.
-/

open NumberField Ideal Finset

namespace Eis

section Duplication

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R] [IsDomain R]

/-- The quadratic character with values in `R`. -/
noncomputable abbrev quadR (F R : Type*) [Field F] [Fintype F] [DecidableEq F] [CommRing R] :
    MulChar F R :=
  (quadraticChar F).ringHomComp (Int.castRingHom R)

omit [IsDomain R] in
/-- `Σ_u f(u²) = Σ_t f(t)·(1 + ρ(t))` in odd characteristic. -/
theorem sum_sq_eq (hF : ringChar F ≠ 2) (f : F → R) :
    ∑ u : F, f (u ^ 2) = ∑ t : F, f t * (1 + quadR F R t) := by
  have h1 : ∀ u : F, f (u ^ 2) = ∑ t : F, if u ^ 2 = t then f t else 0 := by
    intro u; rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have h := quadraticChar_card_sqrts hF t
  rw [Set.toFinset_ofPred] at h
  have h' : ((#{u : F | u ^ 2 = t} : ℕ) : R) = ((quadraticChar F t + 1 : ℤ) : R) := by
    rw [← h]; simp
  rw [h']; simp [add_comm]

/-- **Duplication for Jacobi sums**: `χ(4)·J(χ, χ) = J(χ, ρ)` for a nontrivial `χ` in odd
characteristic, `ρ` the quadratic character. -/
theorem jacobiSum_self_dup (hF : ringChar F ≠ 2) {χ : MulChar F R} (hχ : χ ≠ 1) :
    χ 4 * jacobiSum χ χ = jacobiSum χ (quadR F R) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  -- `4x(1 − x) = 1 − (2x − 1)²`
  have e1 : χ 4 * jacobiSum χ χ = ∑ x : F, χ (1 - (2 * x - 1) ^ 2) := by
    rw [jacobiSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_mul, ← map_mul]; congr 1; ring
  let e : F ≃ F :=
    { toFun := fun x => 2 * x - 1
      invFun := fun u => (u + 1) / 2
      left_inv := fun x => by field_simp; ring
      right_inv := fun u => by field_simp; ring }
  have e2 : ∑ x : F, χ (1 - (2 * x - 1) ^ 2) = ∑ u : F, χ (1 - u ^ 2) :=
    Fintype.sum_equiv e _ _ fun x => rfl
  rw [e1, e2, sum_sq_eq hF (fun t => χ (1 - t))]
  simp_rw [mul_add, mul_one]
  rw [Finset.sum_add_distrib]
  have e3 : ∑ t : F, χ (1 - t) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    exact Fintype.sum_equiv (Equiv.subLeft 1) _ _ fun t => rfl
  rw [e3, zero_add, jacobiSum_comm, jacobiSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm]

/-- **The Hasse–Davenport product formula for `m = 2`**: `χ(4)·g(χ)·g(χρ) = g(χ²)·g(ρ)`. -/
theorem gaussSum_dup (hF : ringChar F ≠ 2) {χ : MulChar F R} (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) (hcard : (Fintype.card F : R) ≠ 0) :
    χ 4 * gaussSum χ ψ * gaussSum (χ * quadR F R) ψ =
      gaussSum (χ ^ 2) ψ * gaussSum (quadR F R) ψ := by
  have hρ1 : quadR F R ^ 2 = 1 := by
    rw [MulChar.ringHomComp_pow]
    have := (quadraticChar_isQuadratic F).sq_eq_one
    rw [this, MulChar.ringHomComp_one]
  have hχρ : χ * quadR F R ≠ 1 := by
    intro h
    apply hχ2
    have hc : χ = (quadR F R)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hc, inv_pow, hρ1, inv_one]
  have hg0 : gaussSum χ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hχ hψ
  have k1 := jacobiSum_mul_nontrivial (show χ * χ ≠ 1 by rwa [← sq]) ψ
  have k2 := jacobiSum_mul_nontrivial hχρ ψ
  have k3 := jacobiSum_self_dup hF hχ
  apply mul_left_cancel₀ hg0
  rw [sq]
  linear_combination (-(χ 4 * gaussSum (χ * quadR F R) ψ)) * k1 +
    gaussSum (χ * quadR F R) ψ * gaussSum (χ * χ) ψ * k3 + gaussSum (χ * χ) ψ * k2

end Duplication
section GaussCube

theorem σO_injective : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) :=
  σ.injective.comp RingOfIntegers.coe_injective

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)

/-- The cubic character with values in `ℂ`, through the embedding `σ`. -/
noncomputable def cubCharC : MulChar (𝓞 K ⧸ P) ℂ :=
  (cubChar P hP3).ringHomComp (σ.comp (algebraMap (𝓞 K) K))

theorem cubCharC_pow_three : cubCharC P hP3 ^ 3 = 1 := by
  rw [cubCharC, MulChar.ringHomComp_pow, cubChar_pow_three, MulChar.ringHomComp_one]

theorem cubCharC_ne_one : cubCharC P hP3 ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff σO_injective).2 (cubChar_ne_one P hP3)

theorem orderOf_cubCharC : orderOf (cubCharC P hP3) = 3 :=
  orderOf_eq_prime (cubCharC_pow_three P hP3) (cubCharC_ne_one P hP3)

theorem cubCharC_neg_one : cubCharC P hP3 (-1) = 1 :=
  MulChar.val_neg_one_eq_one_of_odd_order ⟨1, rfl⟩ (cubCharC_pow_three P hP3)

/-- **The cube of the cubic Gauss sum**: `g(χ_P, ψ)³ = −N(P)·π` for `P = (π)`, `π` primary, and any
primitive additive character `ψ`. -/
theorem gaussSum_cubCharC_cube {π : 𝓞 K} (hπ : Primary π) (hP : P = span {π})
    {ψ : AddChar (𝓞 K ⧸ P) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (cubCharC P hP3) ψ ^ 3 = -((absNorm P : ℕ) : ℂ) * σ (π : K) := by
  have h := gaussSum_pow_eq_prod_jacobiSum (χ := cubCharC P hP3) (ψ := ψ)
    (by rw [orderOf_cubCharC]; norm_num) hψ
  rw [orderOf_cubCharC] at h
  rw [h, cubCharC_neg_one, one_mul]
  simp only [show Finset.Ico 1 (3 - 1) = {1} by rfl, Finset.prod_singleton, pow_one]
  rw [cubCharC, jacobiSum_ringHomComp, jacobiSum_eq_neg P hP3 hπ hP, absNorm_eq_card]
  simp

/-- `|g(χ_P, ψ)|² = N(P)`. -/
theorem norm_gaussSum_cubCharC_sq {ψ : AddChar (𝓞 K ⧸ P) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum (cubCharC P hP3) ψ‖ ^ 2 = (absNorm P : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card (cubCharC_ne_one P hP3) hψ
  rw [← star_gaussSum_eq, RCLike.star_def, Complex.mul_conj, ← absNorm_eq_card] at h
  rw [← Complex.normSq_eq_norm_sq]
  exact_mod_cast h

end GaussCube

/-- The residue ring `𝓞/P` has characteristic `≠ 2` when `2 ∉ P` (round 332; `ringChar_ne_two` and
`ringChar_ne_two_of_two` are its instances). -/
theorem ringChar_ne_two_of_not_mem (P : Ideal (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ P) :
    ringChar (𝓞 K ⧸ P) ≠ 2 := by
  intro h
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, show (2 : 𝓞 K) = ((2 : ℕ) : 𝓞 K) by norm_num, map_natCast,
    ringChar.spec, h]

section Sextic

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P)

omit hPm in
include hP6 in
theorem three_not_mem_of_six : (3 : 𝓞 K) ∉ P := fun h =>
  hP6 (by rw [show (6 : 𝓞 K) = 2 * 3 by norm_num]; exact P.mul_mem_left _ h)

omit hPm in
include hP6 in
theorem two_not_mem_of_six : (2 : 𝓞 K) ∉ P := fun h =>
  hP6 (by rw [show (6 : 𝓞 K) = 3 * 2 by norm_num]; exact P.mul_mem_left _ h)

omit hPm in
include hP6 in
theorem ringChar_ne_two : ringChar (𝓞 K ⧸ P) ≠ 2 :=
  ringChar_ne_two_of_not_mem P (two_not_mem_of_six P hP6)

include hP6 in
theorem m3_eq_two_mul_m6 : m3 P = 2 * m6 P := by
  have h := six_dvd_card_sub_one P hP6
  unfold m3 m6; omega

include hP6 in
/-- `χ_P(sextic)² = χ_P(cubic)`. -/
theorem chi6_sq : chi6 P hP6 ^ 2 = cubCharC P (three_not_mem_of_six P hP6) := by
  have hP3 := three_not_mem_of_six P hP6
  ext x
  obtain ⟨u, hu, hσ⟩ := chi6_spec P hP6 x
  rw [MulChar.pow_apply_coe, hσ, cubCharC, MulChar.ringHomComp_apply]
  have h3 := (cubChar_spec P hP3 x).1
  have hu2 : ((u : 𝓞 K) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, units_pow_six, Units.val_one]
  have hv : (cubChar P hP3 x) ^ 3 = 1 := (cubChar_spec P hP3 x).2
  have heq : (u : 𝓞 K) ^ 2 = cubChar P hP3 x := by
    apply cube_eq_of_mk_eq P hP3 hu2 hv
    rw [map_pow, hu, h3, ← pow_mul, m3_eq_two_mul_m6 P hP6, mul_comm]
  rw [← map_pow]
  simp only [RingHom.comp_apply]
  rw [← heq]; push_cast; rfl

open Classical in
include hP6 in
/-- `χ_P(sextic)³ = ρ`, the quadratic character (Euler's criterion). -/
theorem chi6_cube : chi6 P hP6 ^ 3 = quadR (𝓞 K ⧸ P) ℂ := by
  classical
  have hF := ringChar_ne_two P hP6
  ext x
  obtain ⟨u, hu, hσ⟩ := chi6_spec P hP6 x
  rw [MulChar.pow_apply_coe, hσ, ← map_pow]
  have hx0 : (x : 𝓞 K ⧸ P) ≠ 0 := x.ne_zero
  have hq : ((quadraticChar (𝓞 K ⧸ P) x : ℤ) : 𝓞 K ⧸ P) = (x : 𝓞 K ⧸ P) ^ (3 * m6 P) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hF]
    congr 1
    have h := six_dvd_card_sub_one P hP6
    unfold m6; omega
  have hmk : Ideal.Quotient.mk P ((u : 𝓞 K) ^ 3) =
      Ideal.Quotient.mk P (((quadraticChar (𝓞 K ⧸ P) x : ℤ) : 𝓞 K)) := by
    rw [map_pow, hu, ← pow_mul, mul_comm, map_intCast, hq]
  -- `u³ = ±1`, and `±1` are distinct modulo `P`
  have hu3 : ((u : 𝓞 K) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, units_pow_six, Units.val_one]
  have hpm : ∀ y : 𝓞 K, y ^ 2 = 1 → y = 1 ∨ y = -1 := fun y hy => by
    have : (y - 1) * (y + 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have h2P := two_not_mem_of_six P hP6
  have hdist : ∀ a b : 𝓞 K, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := by
    intro a b ha hb h
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exfalso; apply h2P
      rw [← Ideal.Quotient.eq_zero_iff_mem, show (2 : 𝓞 K) = 1 - (-1) by norm_num, map_sub, h,
        sub_self]
    · exfalso; apply h2P
      rw [← Ideal.Quotient.eq_zero_iff_mem, show (2 : 𝓞 K) = 1 - (-1) by norm_num, map_sub, h,
        sub_self]
    · rfl
  have hρ : ((quadraticChar (𝓞 K ⧸ P) x : ℤ) : 𝓞 K) = 1 ∨
      ((quadraticChar (𝓞 K ⧸ P) x : ℤ) : 𝓞 K) = -1 := by
    rcases quadraticChar_dichotomy hx0 with h | h <;> rw [h] <;> simp
  have heq := hdist _ _ (hpm _ hu3) hρ hmk
  rw [MulChar.ringHomComp_apply]
  have hcoe : ((u : 𝓞 K) : K) ^ 3 = ((((quadraticChar (𝓞 K ⧸ P) x : ℤ) : 𝓞 K)) : K) := by
    rw [← heq]; push_cast; rfl
  rw [hcoe]; simp

open Classical in
include hP6 in
/-- **The sextic Gauss sum through the cubic and the quadratic ones**:
`χ₆(4)·g(χ₆)·N(P) = g(χ₃)²·g(ρ)`, from the Hasse–Davenport product formula for `m = 2`. -/
theorem gaussSum_chi6 {ψ : AddChar (𝓞 K ⧸ P) ℂ} (hψ : ψ.IsPrimitive) :
    chi6 P hP6 4 * gaussSum (chi6 P hP6) ψ * (absNorm P : ℂ) =
      gaussSum (cubCharC P (three_not_mem_of_six P hP6)) ψ ^ 2 *
        gaussSum (quadR (𝓞 K ⧸ P) ℂ) ψ := by
  classical
  set hP3 := three_not_mem_of_six P hP6
  have hF := ringChar_ne_two P hP6
  have h2 := chi6_sq P hP6
  have h3 := chi6_cube P hP6
  have hχ2 : chi6 P hP6 ^ 2 ≠ 1 := by rw [h2]; exact cubCharC_ne_one P hP3
  have hχ1 : chi6 P hP6 ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hcard : ((Fintype.card (𝓞 K ⧸ P) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hd := gaussSum_dup hF hχ1 hχ2 hψ hcard
  have hρ : chi6 P hP6 * quadR (𝓞 K ⧸ P) ℂ = cubCharC P hP3 ^ 2 := by
    rw [← h3, ← h2, ← pow_succ', ← pow_mul]
  rw [hρ, h2] at hd
  -- `g(χ₃)·g(χ₃²) = χ₃(−1)·N = N`
  have hgg := gaussSum_mul_gaussSum_pow_orderOf_sub_one (cubCharC_ne_one P hP3) hψ
  rw [orderOf_cubCharC, cubCharC_neg_one, one_mul] at hgg
  simp only [show 3 - 1 = 2 by rfl] at hgg
  rw [absNorm_eq_card]
  calc chi6 P hP6 4 * gaussSum (chi6 P hP6) ψ * ((Fintype.card (𝓞 K ⧸ P) : ℕ) : ℂ)
      = chi6 P hP6 4 * gaussSum (chi6 P hP6) ψ *
          (gaussSum (cubCharC P hP3) ψ * gaussSum (cubCharC P hP3 ^ 2) ψ) := by rw [hgg]
    _ = gaussSum (cubCharC P hP3) ψ *
          (chi6 P hP6 4 * gaussSum (chi6 P hP6) ψ * gaussSum (cubCharC P hP3 ^ 2) ψ) := by ring
    _ = _ := by rw [hd]; ring

end Sextic

end Eis

#print axioms Eis.sum_sq_eq
#print axioms Eis.jacobiSum_self_dup
#print axioms Eis.gaussSum_dup
#print axioms Eis.orderOf_cubCharC
#print axioms Eis.gaussSum_cubCharC_cube
#print axioms Eis.norm_gaussSum_cubCharC_sq
#print axioms Eis.chi6_sq
#print axioms Eis.chi6_cube
#print axioms Eis.gaussSum_chi6
