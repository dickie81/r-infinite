import EisensteinQuadGauss

/-! # Quadratic and sextic reciprocity in `ℤ[ω]` (round 298)

S3 of round 291's plan, part 4: reciprocity from round 297's quadratic Gauss sums, as in Appendix A.1
of the release's companion paper (the proof of its Lemma 4.1).

* **Twisted quadratic sums** `S_c(t) = Σ_{x mod c} ψ_c(t·x²)` (`sqSum`). Chinese remainders
  (**`sqSum_mul`**): `S_{ab}(1) = S_a(b)·S_b(a)` for coprime `a, b`, since `x = br + as` gives
  `ψ_{ab}(x²) = ψ_a(br²)·ψ_b(as²)`.
* **At a prime** `p ∤ 2` (**`sqSum_prime`**): `S_p(t) = ρ_p(t)·g(ρ_p, ψ_p)` for `p ∤ t`, with `ρ_p` the
  quadratic character of `ℤ[ω]/p`. Each `y` has `1 + ρ_p(y)` square roots (round 292's `sum_sq_eq`),
  and `Σ_y ψ_p(ty) = 0`. At `t = 1` (**`gaussSum_quadR`**) the quadratic Gauss sum is round 297's
  `Σ_{x mod p} ψ_p(x²)`, the paper's `Γ_quad(p) = γ₃(p)`. So for `p = x + yω`,
  `g(ρ_p, ψ_p) = (|σp|/2)·Φ(x, y)` with `Φ(x, y) = 1 + i^{-y} + i^x + i^{y-x}`
  (`gaussSum_quadR_coords`).
* **The first supplementary law** (`quadR_neg_one`): `4ρ_p(−1) = Φ(x, y)²`, from Mathlib's
  `gaussSum_sq`, `g(ρ_p, ψ_p)² = ρ_p(−1)·N(p)`.
* **Quadratic reciprocity** (**`quad_recip`**, **`quad_recip_coords`**): for coprime primes `a, b ∤ 2`,
  `G(ab) = ρ_a(b)ρ_b(a)·G(a)G(b)` with `G(c) = Σ_{x mod c} ψ_c(x²)`. In coordinates,
  `ρ_a(b)ρ_b(a)·Φ(a)Φ(b) = 2Φ(ab)`, with `ab = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀ − a₁b₁)ω`.
* **Sextic reciprocity** (**`sextic_recip`**, **`sextic_recip_coords`**): round 281's sextic character
  is `χ₆ = ρ·χ₃²` (`chi6_eq_quadR_mul`, from round 292's `chi6_sq` and `chi6_cube`). With round 290's
  cubic reciprocity, for coprime primary primes `a, b ∤ 6`, `χ_b(a) = ρ_a(b)ρ_b(a)·χ_a(b)` and
  `χ_b(a)·Φ(a)Φ(b) = 2Φ(ab)·χ_a(b)`. This is the paper's `χ_b(a) = R(a, b)χ_a(b)`, with its
  `R(a, b) = Γ_quad(ab)/(Γ_quad(a)Γ_quad(b))` and `Γ_quad = Φ/2`.
-/

open NumberField Complex Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- The twisted quadratic sum `S_c(t) = Σ_{x mod c} ψ_c(t·x²)`. -/
def sqSum (c t : 𝓞 K) : ℂ := gaussTr c (fun x => ψc c (t * (x * x))) 0

theorem sqSum_one (c : 𝓞 K) : sqSum c 1 = gaussTr c (qphase c) 0 := by
  unfold sqSum qphase; simp only [one_mul]

/-- `ψ_c(c·u) = 1`. -/
theorem ψc_mul_self (c : 𝓞 K) (hc : c ≠ 0) (u : 𝓞 K) : ψc c (c * u) = 1 := by
  have := ψc_add_mul c hc 0 u
  rwa [zero_add, ψc_zero] at this

/-- **Chinese remainders for the twisted quadratic sums**: `S_{ab}(t) = S_a(tb)·S_b(ta)` for coprime
`a, b` (round 304; in this file since round 332). -/
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

/-- **Chinese remainders for the quadratic sums**: `S_{ab}(1) = S_a(b)·S_b(a)` for coprime
`a, b`, the case `t = 1` of `sqSum_mul_t` (round 332). -/
theorem sqSum_mul (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsCoprime a b) :
    sqSum (a * b) 1 = sqSum a b * sqSum b a := by
  simpa using sqSum_mul_t a b 1 ha hb hab

section Prime

variable (p : 𝓞 K) [hP : (span {p} : Ideal (𝓞 K)).IsMaximal]

omit hP in
theorem ringChar_ne_two_of_two [(span {p} : Ideal (𝓞 K)).IsMaximal]
    (h2 : (2 : 𝓞 K) ∉ span {p}) : ringChar (𝓞 K ⧸ span {p}) ≠ 2 :=
  ringChar_ne_two_of_not_mem _ h2

open Classical in
/-- **The twisted quadratic sum at a prime**: `S_p(t) = ρ_p(t)·g(ρ_p, ψ_p)` for `p ∤ 2` and
`p ∤ t`, with `ρ_p` the quadratic character of `ℤ[ω]/p`. -/
theorem sqSum_prime (h2 : (2 : 𝓞 K) ∉ span {p}) (t : 𝓞 K) (ht : t ∉ span {p}) :
    sqSum p t = quadR (𝓞 K ⧸ span {p}) ℂ (Ideal.Quotient.mk (span {p}) t) *
      gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψQ p (ne_zero_of_maximal p)) := by
  have hp := ne_zero_of_maximal p
  set ψ := ψQ p hp
  set T := Ideal.Quotient.mk (span {p}) t
  have hT : T ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hF := ringChar_ne_two_of_two p h2
  have e1 : sqSum p t = ∑ r : 𝓞 K ⧸ span {p}, ψ (T * r ^ 2) := by
    unfold sqSum
    rw [gaussTr_eq_sum p hp (fun x => ψc p (t * (x * x))) (sq_periodic p t hp) (repQ p)
      (repQ_bijective p hp) 0]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_zero, ψc_zero, mul_one, ← ψQ_mk p hp, map_mul (Ideal.Quotient.mk (span {p})),
      map_mul (Ideal.Quotient.mk (span {p})), repQ_mk, sq]
  rw [e1, sum_sq_eq hF (fun s => ψ (T * s))]
  simp_rw [mul_add, mul_one]
  rw [Finset.sum_add_distrib]
  have e2 : ∑ s : 𝓞 K ⧸ span {p}, ψ (T * s) = 0 := by
    have := AddChar.sum_eq_zero_of_ne_one (ψQ_isPrimitive p hT)
    simpa [AddChar.mulShift_apply] using this
  have e3 : ∑ s : 𝓞 K ⧸ span {p}, ψ (T * s) * quadR (𝓞 K ⧸ span {p}) ℂ s =
      gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψ.mulShift T) := by
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm]
  rw [e2, zero_add, e3]
  have hu : IsUnit T := isUnit_iff_ne_zero.2 hT
  have h4 := gaussSum_mulShift_eq (quadR (𝓞 K ⧸ span {p}) ℂ) ψ hu.unit
  rw [IsUnit.unit_spec] at h4
  rw [h4]
  congr 1
  rw [MulChar.inv_apply_eq_inv']
  have hq : quadR (𝓞 K ⧸ span {p}) ℂ T = 1 ∨ quadR (𝓞 K ⧸ span {p}) ℂ T = -1 := by
    rw [MulChar.ringHomComp_apply]
    rcases quadraticChar_dichotomy hT with h | h <;> rw [h] <;> simp
  rcases hq with h | h <;> rw [h] <;> norm_num

end Prime

section Recip

open Classical in
/-- **The quadratic Gauss sum at a prime** `p ∤ 2` is the sum of round 297:
`g(ρ_p, ψ_p) = Σ_{x mod p} ψ_p(x²)` (the paper's `Γ_quad(p) = γ₃(p)`). -/
theorem gaussSum_quadR (p : 𝓞 K) [hP : (span {p} : Ideal (𝓞 K)).IsMaximal]
    (h2 : (2 : 𝓞 K) ∉ span {p}) :
    gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψQ p (ne_zero_of_maximal p)) =
      gaussTr p (qphase p) 0 := by
  have h1 : (1 : 𝓞 K) ∉ span {p} := fun h =>
    hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  have := sqSum_prime p h2 1 h1
  rw [map_one, MulChar.map_one, one_mul, sqSum_one] at this
  exact this.symm

open Classical in
/-- **Quadratic reciprocity in `ℤ[ω]`**: for coprime primes `a, b` not dividing `2`,
`G(ab) = ρ_a(b)·ρ_b(a)·G(a)·G(b)`, where `G(c) = Σ_{x mod c} ψ_c(x²)`. -/
theorem quad_recip (a b : 𝓞 K) [(span {a} : Ideal (𝓞 K)).IsMaximal]
    [(span {b} : Ideal (𝓞 K)).IsMaximal] (ha2 : (2 : 𝓞 K) ∉ span {a})
    (hb2 : (2 : 𝓞 K) ∉ span {b}) (hab : IsCoprime a b) :
    gaussTr (a * b) (qphase (a * b)) 0 =
      quadR (𝓞 K ⧸ span {a}) ℂ (Ideal.Quotient.mk (span {a}) b) *
        quadR (𝓞 K ⧸ span {b}) ℂ (Ideal.Quotient.mk (span {b}) a) *
          (gaussTr a (qphase a) 0 * gaussTr b (qphase b) 0) := by
  have ha := ne_zero_of_maximal a
  have hb := ne_zero_of_maximal b
  have hba : b ∉ span {a} := fun h =>
    not_isUnit_of_maximal a (hab.isUnit_of_dvd' dvd_rfl (Ideal.mem_span_singleton.1 h))
  have hab' : a ∉ span {b} := fun h =>
    not_isUnit_of_maximal b (hab.isUnit_of_dvd' (Ideal.mem_span_singleton.1 h) dvd_rfl)
  rw [← sqSum_one, sqSum_mul a b ha hb hab, sqSum_prime a ha2 b hba, sqSum_prime b hb2 a hab',
    gaussSum_quadR a ha2, gaussSum_quadR b hb2]
  ring

/-- Twice the paper's `Γ_quad(x + yω)`: `Φ(x, y) = 1 + i^{-y} + i^x + i^{y-x}`. -/
def quadPhi (x y : ℤ) : ℂ := 1 + I ^ (-y) + I ^ x + I ^ (y - x)

open Classical in
/-- The quadratic Gauss sum at a prime `p = x + yω`, `p ∤ 2`: `g(ρ_p, ψ_p) = (|σp|/2)·Φ(x, y)`. -/
theorem gaussSum_quadR_coords (p : 𝓞 K) [(span {p} : Ideal (𝓞 K)).IsMaximal]
    (h2 : (2 : 𝓞 K) ∉ span {p}) (x y : ℤ) (hp : p = x + y * ω) :
    gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψQ p (ne_zero_of_maximal p)) =
      ((‖σO p‖ / 2 : ℝ) : ℂ) * quadPhi x y := by
  have h0 := ne_zero_of_maximal p
  rw [gaussSum_quadR p h2]
  subst hp
  exact quad_gauss_coords x y h0

open Classical in
/-- **The first supplementary law**: `ρ_p(−1) = Φ(x, y)²/4` for a prime `p = x + yω`, `p ∤ 2`. -/
theorem quadR_neg_one (p : 𝓞 K) [(span {p} : Ideal (𝓞 K)).IsMaximal]
    (h2 : (2 : 𝓞 K) ∉ span {p}) (x y : ℤ) (hp : p = x + y * ω) :
    4 * quadR (𝓞 K ⧸ span {p}) ℂ (-1) = quadPhi x y ^ 2 := by
  have hF := ringChar_ne_two_of_two p h2
  have hρ1 : quadR (𝓞 K ⧸ span {p}) ℂ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
      (quadraticChar_ne_one hF)
  have hq : (quadR (𝓞 K ⧸ span {p}) ℂ).IsQuadratic :=
    (quadraticChar_isQuadratic _).comp _
  have hsq := gaussSum_sq hρ1 hq (ψQ_isPrimitive p)
  rw [gaussSum_quadR_coords p h2 x y hp, ← absNorm_eq_card (P := span {p})] at hsq
  have hN : (absNorm (span {p}) : ℂ) = ((‖σO p‖ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_norm_σO, Complex.ofReal_natCast]
  rw [hN] at hsq
  have hγ : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by
    have : σO p ≠ 0 := fun h => ne_zero_of_maximal p (σO_injective (h.trans (map_zero σO).symm))
    exact_mod_cast (norm_pos_iff.2 this).ne'
  push_cast at hsq
  field_simp at hsq
  linear_combination (-1 : ℂ) * hsq

open Classical in
/-- **Quadratic reciprocity in coordinates**: for coprime primes `a = a₀ + a₁ω`, `b = b₀ + b₁ω`
not dividing `2`, `ρ_a(b)·ρ_b(a)·Φ(a)·Φ(b) = 2·Φ(ab)`, with
`ab = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀ − a₁b₁)ω`. -/
theorem quad_recip_coords (a b : 𝓞 K) [(span {a} : Ideal (𝓞 K)).IsMaximal]
    [(span {b} : Ideal (𝓞 K)).IsMaximal] (ha2 : (2 : 𝓞 K) ∉ span {a})
    (hb2 : (2 : 𝓞 K) ∉ span {b}) (hab : IsCoprime a b) (a₀ a₁ b₀ b₁ : ℤ)
    (ha : a = a₀ + a₁ * ω) (hb : b = b₀ + b₁ * ω) :
    quadR (𝓞 K ⧸ span {a}) ℂ (Ideal.Quotient.mk (span {a}) b) *
        quadR (𝓞 K ⧸ span {b}) ℂ (Ideal.Quotient.mk (span {b}) a) *
          (quadPhi a₀ a₁ * quadPhi b₀ b₁) =
      2 * quadPhi (a₀ * b₀ - a₁ * b₁) (a₀ * b₁ + a₁ * b₀ - a₁ * b₁) := by
  have h := quad_recip a b ha2 hb2 hab
  have ha0 := ne_zero_of_maximal a
  have hb0 := ne_zero_of_maximal b
  have hprod : a * b = ((a₀ * b₀ - a₁ * b₁ : ℤ) : 𝓞 K) +
      ((a₀ * b₁ + a₁ * b₀ - a₁ * b₁ : ℤ) : 𝓞 K) * ω := by
    rw [ha, hb]; push_cast; linear_combination (a₁ : 𝓞 K) * (b₁ : 𝓞 K) * ω_sq_add
  have hGab := quad_gauss_coords (a₀ * b₀ - a₁ * b₁) (a₀ * b₁ + a₁ * b₀ - a₁ * b₁)
    (by rw [← hprod]; exact mul_ne_zero ha0 hb0)
  rw [← hprod] at hGab
  have hGa := quad_gauss_coords a₀ a₁ (by rw [← ha]; exact ha0)
  rw [← ha] at hGa
  have hGb := quad_gauss_coords b₀ b₁ (by rw [← hb]; exact hb0)
  rw [← hb] at hGb
  rw [hGab, hGa, hGb, map_mul, norm_mul] at h
  have hσa : ((‖σO a‖ : ℝ) : ℂ) ≠ 0 := by
    have : σO a ≠ 0 := fun h => ha0 (σO_injective (h.trans (map_zero σO).symm))
    exact_mod_cast (norm_pos_iff.2 this).ne'
  have hσb : ((‖σO b‖ : ℝ) : ℂ) ≠ 0 := by
    have : σO b ≠ 0 := fun h => hb0 (σO_injective (h.trans (map_zero σO).symm))
    exact_mod_cast (norm_pos_iff.2 this).ne'
  unfold quadPhi
  push_cast at h
  field_simp at h
  linear_combination (-1 : ℂ) * h

end Recip

section Sextic

open Classical in
/-- `χ₆ = ρ·χ₃²`: the sextic character is the quadratic one times the square of the cubic one. -/
theorem chi6_eq_quadR_mul (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) :
    chi6 P hP6 = quadR (𝓞 K ⧸ P) ℂ * cubCharC P (three_not_mem_of_six P hP6) ^ 2 := by
  rw [← chi6_cube P hP6, ← chi6_sq P hP6, ← pow_mul, ← pow_add]
  calc chi6 P hP6 = chi6 P hP6 ^ 6 * chi6 P hP6 := by rw [chi6_pow_six, one_mul]
    _ = chi6 P hP6 ^ (3 + 2 * 2) := by rw [← pow_succ]

open Classical in
theorem quadR_sq_eq_one (P : Ideal (𝓞 K)) [P.IsMaximal] (x : 𝓞 K ⧸ P) (hx : x ≠ 0) :
    quadR (𝓞 K ⧸ P) ℂ x ^ 2 = 1 := by
  rw [MulChar.ringHomComp_apply, ← map_pow, quadraticChar_sq_one hx, map_one]

open Classical in
/-- **Sextic reciprocity in `ℤ[ω]`** (the paper's `χ_b(a) = R(a, b)·χ_a(b)`): for coprime primary
primes `a, b` not dividing `6`, `χ_b(a) = ρ_a(b)·ρ_b(a)·χ_a(b)`, by round 290's cubic reciprocity. -/
theorem sextic_recip (a b : 𝓞 K) [(span {a} : Ideal (𝓞 K)).IsMaximal]
    [(span {b} : Ideal (𝓞 K)).IsMaximal] (ha6 : (6 : 𝓞 K) ∉ span {a})
    (hb6 : (6 : 𝓞 K) ∉ span {b}) (ha : Primary a) (hb : Primary b) (hab : IsCoprime a b) :
    chi6 (span {b}) hb6 (Ideal.Quotient.mk _ a) =
      quadR (𝓞 K ⧸ span {a}) ℂ (Ideal.Quotient.mk _ b) *
        quadR (𝓞 K ⧸ span {b}) ℂ (Ideal.Quotient.mk _ a) *
          chi6 (span {a}) ha6 (Ideal.Quotient.mk _ b) := by
  have h3a := three_not_mem_of_six (span {a}) ha6
  have h3b := three_not_mem_of_six (span {b}) hb6
  have hba : Ideal.Quotient.mk (span {a}) b ≠ 0 := fun h =>
    not_isUnit_of_maximal a (hab.isUnit_of_dvd' dvd_rfl
      (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)))
  have hab' : Ideal.Quotient.mk (span {b}) a ≠ 0 := fun h =>
    not_isUnit_of_maximal b (hab.isUnit_of_dvd'
      (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)) dvd_rfl)
  have hcub : cubCharC (span {b}) h3b (Ideal.Quotient.mk _ a) =
      cubCharC (span {a}) h3a (Ideal.Quotient.mk _ b) := by
    have h := cub_recip ha hb hab
    rw [cub_prime, cub_prime, chi3_eq h3b, chi3_eq h3a] at h
    simp only [cubCharC, MulChar.ringHomComp_apply]
    rw [h]
  rw [chi6_eq_quadR_mul (span {b}) hb6, chi6_eq_quadR_mul (span {a}) ha6, MulChar.mul_apply,
    MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero, MulChar.pow_apply' _ two_ne_zero, hcub]
  have h1 := quadR_sq_eq_one (span {a}) _ hba
  linear_combination (-(quadR (𝓞 K ⧸ span {b}) ℂ (Ideal.Quotient.mk _ a) *
    cubCharC (span {a}) h3a (Ideal.Quotient.mk _ b) ^ 2)) * h1

open Classical in
/-- **Sextic reciprocity in coordinates**: for coprime primary primes `a = a₀ + a₁ω`,
`b = b₀ + b₁ω` not dividing `6`, `χ_b(a)·Φ(a)·Φ(b) = 2Φ(ab)·χ_a(b)`, i.e. `R(a, b) = 2Φ(ab)/(Φ(a)Φ(b))`
is the paper's `Γ_quad(ab)/(Γ_quad(a)Γ_quad(b))`. -/
theorem sextic_recip_coords (a b : 𝓞 K) [(span {a} : Ideal (𝓞 K)).IsMaximal]
    [(span {b} : Ideal (𝓞 K)).IsMaximal] (ha6 : (6 : 𝓞 K) ∉ span {a})
    (hb6 : (6 : 𝓞 K) ∉ span {b}) (ha : Primary a) (hb : Primary b) (hab : IsCoprime a b)
    (a₀ a₁ b₀ b₁ : ℤ) (ha' : a = a₀ + a₁ * ω) (hb' : b = b₀ + b₁ * ω) :
    chi6 (span {b}) hb6 (Ideal.Quotient.mk _ a) * (quadPhi a₀ a₁ * quadPhi b₀ b₁) =
      2 * quadPhi (a₀ * b₀ - a₁ * b₁) (a₀ * b₁ + a₁ * b₀ - a₁ * b₁) *
        chi6 (span {a}) ha6 (Ideal.Quotient.mk _ b) := by
  rw [sextic_recip a b ha6 hb6 ha hb hab, ← quad_recip_coords a b
    (two_not_mem_of_six _ ha6) (two_not_mem_of_six _ hb6) hab a₀ a₁ b₀ b₁ ha' hb']
  ring

end Sextic

end Eis

end

#print axioms Eis.sqSum_mul_t
#print axioms Eis.sqSum_mul
#print axioms Eis.sqSum_prime
#print axioms Eis.gaussSum_quadR
#print axioms Eis.quad_recip
#print axioms Eis.gaussSum_quadR_coords
#print axioms Eis.quadR_neg_one
#print axioms Eis.quad_recip_coords
#print axioms Eis.chi6_eq_quadR_mul
#print axioms Eis.sextic_recip
#print axioms Eis.sextic_recip_coords
