import EisensteinQuadRecip

/-! # The companion paper's Lemma 4.1 at a prime (round 299)

S3 of round 291's plan, part 5: the Gauss-sum identities of the companion paper's Lemma 4.1 for a
primary prime `p ∤ 6`. They concern the normalized Gauss sums `γ_j(p) = g(χ_p^j, ψ_p)/|σp|` (`gamN`) of
round 281's sextic character `χ_p`, with `α(p) = σp/|σp|` (`alphaN`) and `μ(p) = −1`.

* **`γ₂(p)³ = μ(p)α(p)`** (`gamN_two_cube`), from round 292's `gaussSum_cubCharC_cube`,
  `g(χ₃)³ = −N(p)·σp`.
* **`γ₁(p)γ₂(p) = μ(p)α(p)G(p)`** with `G(p) = χ_p(4)⁻¹γ₃(p)` (`Gp`, `gamN_one_mul_two`), from round
  292's `gaussSum_chi6`, `χ_p(4)·g(χ₆)·N(p) = g(χ₃)²·g(ρ)`.
* **`γ₁(p)γ₋₁(p) = χ_p(−1)`** (`gamN_one_mul_inv`), from Mathlib's `gaussSum_mul_gaussSum_eq_card` and
  `mul_gaussSum_inv_eq_gaussSum`.
* **`γ₃(p) = Φ(x, y)/2`** for `p = x + yω` (`gamN_three`): round 298's `gaussSum_quadR_coords`, with
  `χ₆³ = ρ`. This is the paper's `γ₃(p) = Γ_quad(p)`.
* **`χ_p(4)` through `p mod 2`** (`chi6_four`): `2` is inert (`span_two_isMaximal`, from round 284's
  `inert_of_mod_two`) and `−2` is primary (`primary_neg_two`), so round 290's cubic reciprocity gives
  `χ_p(4) = (2/p)₃ = (p/2)₃ = σ(u)` for the cube root of unity `u ≡ p (mod 2)`.
* **`G` on classes modulo `4`**: `G(p) = σ(u)⁻¹·Φ(x, y)/2` (`Gp_coords`); `|G(p)| = 1` (`norm_Gp`,
  from `|γ| = 1` for every nontrivial character, `norm_gamN`); and `G(p) = G(q)` for `p ≡ q (mod 4)`
  (`Gp_eq_of_mod_four`).
-/

open NumberField Complex Ideal

noncomputable section

namespace Eis

/-- `2` is inert in `ℤ[ω]`: `(2)` is a maximal ideal. -/
instance span_two_isMaximal : (span {(2 : 𝓞 K)} : Ideal (𝓞 K)).IsMaximal := by
  obtain ⟨P, hP, -⟩ := inert_of_mod_two Nat.prime_two (by norm_num)
  have hprod := prod_pFactors (p := 2) two_ne_zero
  rw [hP, Multiset.prod_singleton] at hprod
  have hmem : P ∈ pFactors 2 := by rw [hP]; exact Multiset.mem_singleton_self P
  have h := isMaximal_of_mem_nf hmem
  rw [hprod] at h
  simpa using h

theorem three_not_mem_span_two : (3 : 𝓞 K) ∉ span {(2 : 𝓞 K)} := by
  intro h
  have h1 : (1 : 𝓞 K) ∈ span {(2 : 𝓞 K)} := by
    have h2 : (2 : 𝓞 K) ∈ span {(2 : 𝓞 K)} := Ideal.mem_span_singleton_self _
    have := Ideal.sub_mem _ h h2
    rwa [show (3 : 𝓞 K) - 2 = 1 by norm_num] at this
  exact span_two_isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem card_quot_two : Fintype.card (𝓞 K ⧸ span {(2 : 𝓞 K)}) = 4 := by
  rw [← absNorm_eq_card]
  have := absNorm_natCast_span_sq 2
  simpa using this

theorem m3_two : m3 (span {(2 : 𝓞 K)}) = 1 := by
  unfold m3; rw [card_quot_two]

/-- `−2` is primary. -/
theorem primary_neg_two : Primary (-2 : 𝓞 K) := ⟨-1, by ring⟩

section Four

variable (p : 𝓞 K) [hP : (span {p} : Ideal (𝓞 K)).IsMaximal]

theorem isCoprime_two (hp6 : (6 : 𝓞 K) ∉ span {p}) : IsCoprime p 2 := by
  have hp0 := ne_zero_of_maximal p
  have hprime : Prime p := (Ideal.span_singleton_prime hp0).1 hP.isPrime
  exact (hprime.irreducible.coprime_iff_not_dvd).2 fun h =>
    two_not_mem_of_six _ hp6 (Ideal.mem_span_singleton.2 h)

/-- **`χ_p(4)` through `p mod 2`**: for a primary prime `p ∤ 6`, `χ_p(4) = σ(u)` for the cube root of
unity `u ≡ p (mod 2)`, by cubic reciprocity against the primary prime `−2`. -/
theorem chi6_four (hp6 : (6 : 𝓞 K) ∉ span {p}) (hpr : Primary p) :
    ∃ u : 𝓞 K, u ^ 3 = 1 ∧
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) u = Ideal.Quotient.mk (span {(2 : 𝓞 K)}) p ∧
        chi6 (span {p}) hp6 4 = σO u := by
  have h3p := three_not_mem_of_six (span {p}) hp6
  have hcop := isCoprime_two p hp6
  have hp2 : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) p ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    exact span_two_isMaximal.ne_top (Ideal.span_singleton_eq_top.2
      (hcop.isUnit_of_dvd' h dvd_rfl))
  set x : (𝓞 K ⧸ span {(2 : 𝓞 K)})ˣ := Units.mk0 _ hp2 with hx
  obtain ⟨hmk, hcube⟩ := cubChar_spec (span {(2 : 𝓞 K)}) three_not_mem_span_two x
  refine ⟨cubChar (span {(2 : 𝓞 K)}) three_not_mem_span_two x, hcube, ?_, ?_⟩
  · rw [hmk, m3_two, pow_one, hx, Units.val_mk0]
  · -- cubic reciprocity against `−2`
    have h := cub_recip hpr primary_neg_two hcop.neg_right
    rw [Ideal.span_singleton_neg, cub_prime, cub_prime, chi3_eq three_not_mem_span_two,
      chi3_neg h3p, chi3_eq h3p] at h
    -- `χ_p(4) = χ_p(2)² = χ₃,p(2)`
    have h4 : chi6 (span {p}) hp6 4 = cubCharC (span {p}) h3p (Ideal.Quotient.mk _ 2) := by
      rw [← chi6_sq (span {p}) hp6, MulChar.pow_apply' _ two_ne_zero, sq,
        ← map_mul (chi6 (span {p}) hp6), map_ofNat (Ideal.Quotient.mk (span {p})) 2]
      norm_num
    rw [h4, cubCharC, MulChar.ringHomComp_apply, ← h, hx, Units.val_mk0]

end Four

section GaussPrime

variable (p : 𝓞 K) [hP : (span {p} : Ideal (𝓞 K)).IsMaximal]

/-- The trace character `ψ_p` of `ℤ[ω]/p`. -/
def ψp : AddChar (𝓞 K ⧸ span {p}) ℂ := ψQ p (ne_zero_of_maximal p)

theorem ψp_isPrimitive : (ψp p).IsPrimitive := ψQ_isPrimitive p

/-- The normalized Gauss sum `g(χ, ψ_p)/|σp|` of a character `χ` modulo `p`. -/
def gamN (χ : MulChar (𝓞 K ⧸ span {p}) ℂ) : ℂ := gaussSum χ (ψp p) / ((‖σO p‖ : ℝ) : ℂ)

/-- `α(p) = σp/|σp|`. -/
def alphaN : ℂ := σO p / ((‖σO p‖ : ℝ) : ℂ)

theorem norm_σO_ne_zero : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by
  have : σO p ≠ 0 := fun h =>
    ne_zero_of_maximal p (σO_injective (h.trans (map_zero σO).symm))
  exact_mod_cast (norm_pos_iff.2 this).ne'

theorem card_eq_norm_sq :
    ((Fintype.card (𝓞 K ⧸ span {p}) : ℕ) : ℂ) = ((‖σO p‖ : ℝ) : ℂ) ^ 2 := by
  rw [← absNorm_eq_card, ← Complex.ofReal_pow, sq_norm_σO, Complex.ofReal_natCast]

/-- **Normalized Gauss sums have modulus `1`**: `|g(χ, ψ_p)| = |σp|` for `χ ≠ 1`. -/
theorem norm_gamN {χ : MulChar (𝓞 K ⧸ span {p}) ℂ} (hχ : χ ≠ 1) : ‖gamN p χ‖ = 1 := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (ψp_isPrimitive p)
  rw [← star_gaussSum_eq, RCLike.star_def, Complex.mul_conj, card_eq_norm_sq] at h
  have hn : ‖gaussSum χ (ψp p)‖ = ‖σO p‖ := by
    have h2 : ‖gaussSum χ (ψp p)‖ ^ 2 = ‖σO p‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hp0 : ‖σO p‖ ≠ 0 := by
    have := norm_σO_ne_zero p; exact_mod_cast this
  rw [gamN, norm_div, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self hp0]

theorem chi6_pow_ne_one (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) : chi6 P hP6 ^ j ≠ 1 := by
  classical
  have hF := ringChar_ne_two P hP6
  have hq : quadR (𝓞 K ⧸ P) ℂ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
      (quadraticChar_ne_one hF)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · intro h; apply hq; rw [← chi6_cube P hP6, pow_one] at *; rw [h, one_pow]
  · rw [chi6_sq]; exact cubCharC_ne_one P _
  · rw [chi6_cube]; exact hq

open Classical in
theorem chi6_ne_one (hp6 : (6 : 𝓞 K) ∉ span {p}) : chi6 (span {p}) hp6 ≠ 1 := by
  simpa using chi6_pow_ne_one (span {p}) hp6 (j := 1) (by simp)

/-- `χ_p(4)⁶ = 1`, so `χ_p(4) ≠ 0`. -/
theorem chi6_four_pow_six (hp6 : (6 : 𝓞 K) ∉ span {p}) : chi6 (span {p}) hp6 4 ^ 6 = 1 := by
  have hu : IsUnit (4 : 𝓞 K ⧸ span {p}) := by
    refine isUnit_iff_ne_zero.2 fun h => two_not_mem_of_six (span {p}) hp6 ?_
    have h4 : Ideal.Quotient.mk (span {p}) (4 : 𝓞 K) = 0 := by rw [map_ofNat]; exact h
    have h22 : (2 : 𝓞 K) * 2 ∈ span {p} := by
      rw [show (2 : 𝓞 K) * 2 = 4 by norm_num]; exact Ideal.Quotient.eq_zero_iff_mem.1 h4
    rcases hP.isPrime.mem_or_mem h22 with h' | h' <;> exact h'
  rw [← MulChar.pow_apply' _ (by norm_num), chi6_pow_six, MulChar.one_apply hu]

theorem chi6_four_ne_zero (hp6 : (6 : 𝓞 K) ∉ span {p}) : chi6 (span {p}) hp6 4 ≠ 0 := by
  intro h0
  have := chi6_four_pow_six p hp6
  rw [h0] at this
  norm_num at this

/-- **`γ₂(p)³ = μ(p)α(p) = −α(p)`** for a primary prime `p ∤ 6`. -/
theorem gamN_two_cube (hp6 : (6 : 𝓞 K) ∉ span {p}) (hpr : Primary p) :
    gamN p (chi6 (span {p}) hp6 ^ 2) ^ 3 = -alphaN p := by
  have hc := gaussSum_cubCharC_cube (span {p}) (three_not_mem_of_six (span {p}) hp6) hpr rfl
    (ψp_isPrimitive p)
  rw [gamN, chi6_sq, div_pow, hc, absNorm_eq_card, card_eq_norm_sq, alphaN]
  have hγ := norm_σO_ne_zero p
  field_simp
  rfl

open Classical in
/-- **`γ₁(p)γ₂(p) = μ(p)α(p)G(p)`** with `G(p) = χ_p(4)⁻¹γ₃(p)`, for a primary prime `p ∤ 6`. -/
theorem gamN_one_mul_two (hp6 : (6 : 𝓞 K) ∉ span {p}) (hpr : Primary p) :
    gamN p (chi6 (span {p}) hp6) * gamN p (chi6 (span {p}) hp6 ^ 2) =
      -alphaN p * ((chi6 (span {p}) hp6 4)⁻¹ * gamN p (chi6 (span {p}) hp6 ^ 3)) := by
  have h3p := three_not_mem_of_six (span {p}) hp6
  have hc := gaussSum_cubCharC_cube (span {p}) h3p hpr rfl (ψp_isPrimitive p)
  have h6 := gaussSum_chi6 (span {p}) hp6 (ψp_isPrimitive p)
  have h4 := chi6_four_ne_zero p hp6
  rw [gamN, gamN, gamN, chi6_sq, chi6_cube, alphaN]
  rw [absNorm_eq_card, card_eq_norm_sq] at hc h6
  have hγ := norm_σO_ne_zero p
  have hσ : σ (p : K) = σO p := rfl
  rw [hσ] at hc
  -- `χ(4)·g(χ₆)·g(χ₃) = −σ(p)·g(ρ)`, from `χ(4)·g(χ₆)·N = g(χ₃)²·g(ρ)` and `g(χ₃)³ = −N·σ(p)`
  have key : chi6 (span {p}) hp6 4 * gaussSum (chi6 (span {p}) hp6) (ψp p) *
      gaussSum (cubCharC (span {p}) h3p) (ψp p) =
        -(σO p) * gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψp p) := by
    have hN : ((‖σO p‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hγ
    apply mul_left_cancel₀ hN
    linear_combination (gaussSum (cubCharC (span {p}) h3p) (ψp p)) * h6 +
      gaussSum (quadR (𝓞 K ⧸ span {p}) ℂ) (ψp p) * hc
  field_simp
  linear_combination key

open Classical in
/-- **`γ₁(p)γ₋₁(p) = χ_p(−1)`**. -/
theorem gamN_one_mul_inv (hp6 : (6 : 𝓞 K) ∉ span {p}) :
    gamN p (chi6 (span {p}) hp6) * gamN p (chi6 (span {p}) hp6)⁻¹ = chi6 (span {p}) hp6 (-1) := by
  have h1 := gaussSum_mul_gaussSum_eq_card (chi6_ne_one p hp6) (ψp_isPrimitive p)
  have h2 := mul_gaussSum_inv_eq_gaussSum (chi6 (span {p}) hp6)⁻¹ (ψp p)
  have hneg : (chi6 (span {p}) hp6)⁻¹ (-1) = chi6 (span {p}) hp6 (-1) := by
    rw [MulChar.inv_apply', inv_neg, inv_one]
  rw [hneg] at h2
  rw [card_eq_norm_sq] at h1
  rw [gamN, gamN, ← h2]
  have hγ := norm_σO_ne_zero p
  field_simp
  linear_combination (chi6 (span {p}) hp6 (-1)) * h1

open Classical in
/-- **`γ₃(p) = Γ_quad(p) = Φ(x, y)/2`** for `p = x + yω`, `p ∤ 6`. -/
theorem gamN_three (hp6 : (6 : 𝓞 K) ∉ span {p}) (x y : ℤ) (hxy : p = x + y * ω) :
    gamN p (chi6 (span {p}) hp6 ^ 3) = quadPhi x y / 2 := by
  rw [gamN, chi6_cube, ψp, gaussSum_quadR_coords p (two_not_mem_of_six _ hp6) x y hxy]
  have hγ := norm_σO_ne_zero p
  push_cast
  field_simp

end GaussPrime

section GFun

variable (p : 𝓞 K) [hP : (span {p} : Ideal (𝓞 K)).IsMaximal]

/-- The paper's `G(p) = χ̄_p(4)·γ₃(p)`, with `χ̄_p(4) = χ_p(4)⁻¹`. -/
def Gp (hp6 : (6 : 𝓞 K) ∉ span {p}) : ℂ :=
  (chi6 (span {p}) hp6 4)⁻¹ * gamN p (chi6 (span {p}) hp6 ^ 3)

/-- **`G(p)` in coordinates**: for a primary prime `p = x + yω ∤ 6`, `G(p) = σ(u)⁻¹·Φ(x, y)/2` for the
cube root of unity `u ≡ p (mod 2)`. -/
theorem Gp_coords (hp6 : (6 : 𝓞 K) ∉ span {p}) (hpr : Primary p) (x y : ℤ)
    (hxy : p = x + y * ω) :
    ∃ u : 𝓞 K, u ^ 3 = 1 ∧
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) u = Ideal.Quotient.mk (span {(2 : 𝓞 K)}) p ∧
        Gp p hp6 = (σO u)⁻¹ * (quadPhi x y / 2) := by
  obtain ⟨u, hu3, hu2, h4⟩ := chi6_four p hp6 hpr
  exact ⟨u, hu3, hu2, by rw [Gp, h4, gamN_three p hp6 x y hxy]⟩

open Classical in
/-- `|G(p)| = 1`. -/
theorem norm_Gp (hp6 : (6 : 𝓞 K) ∉ span {p}) : ‖Gp p hp6‖ = 1 := by
  have h3 : chi6 (span {p}) hp6 ^ 3 ≠ 1 := by
    rw [chi6_cube]
    exact (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
      (quadraticChar_ne_one (ringChar_ne_two (span {p}) hp6))
  have h4 : ‖chi6 (span {p}) hp6 4‖ = 1 := by
    have h := congrArg norm (chi6_four_pow_six p hp6)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h
  rw [Gp, norm_mul, norm_inv, h4, norm_gamN p h3, inv_one, one_mul]

/-- `Φ` depends only on the coordinates modulo `4`. -/
theorem quadPhi_add_four (x y a b : ℤ) : quadPhi (x + 4 * a) (y + 4 * b) = quadPhi x y := by
  have hI : ∀ k m : ℤ, I ^ (k + 4 * m) = I ^ k := fun k m => by
    rw [zpow_add₀ I_ne_zero, zpow_mul, show (I : ℂ) ^ (4 : ℤ) = 1 by norm_num, one_zpow, mul_one]
  unfold quadPhi
  rw [show -(y + 4 * b) = -y + 4 * (-b) by ring, show y + 4 * b - (x + 4 * a) = (y - x) + 4 * (b - a)
    by ring, hI, hI, hI]

/-- **`G` depends only on the class modulo `4`**: for primary primes `p, q ∤ 6` with `p ≡ q (mod 4)`,
`G(p) = G(q)`. -/
theorem Gp_eq_of_mod_four (q : 𝓞 K) [(span {q} : Ideal (𝓞 K)).IsMaximal]
    (hp6 : (6 : 𝓞 K) ∉ span {p}) (hq6 : (6 : 𝓞 K) ∉ span {q}) (hpr : Primary p)
    (hqr : Primary q) (h4 : p - q ∈ span {(4 : 𝓞 K)}) : Gp p hp6 = Gp q hq6 := by
  obtain ⟨x, y, hxy⟩ := exists_coords p
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h4
  obtain ⟨a, b, hab⟩ := exists_coords d
  -- `q = (x − 4a) + (y − 4b)ω`
  have hq : q = ((x - 4 * a : ℤ) : 𝓞 K) + ((y - 4 * b : ℤ) : 𝓞 K) * ω := by
    have : q = p - d * 4 := by rw [hd]; ring
    rw [this, hxy, hab]; push_cast; ring
  obtain ⟨u, hu3, hu2, hGp⟩ := Gp_coords p hp6 hpr x y hxy
  obtain ⟨v, hv3, hv2, hGq⟩ := Gp_coords q hq6 hqr _ _ hq
  have huv : u = v := by
    apply cube_eq_of_mk_eq (span {(2 : 𝓞 K)}) three_not_mem_span_two hu3 hv3
    rw [hu2, hv2, Ideal.Quotient.eq]
    have : p - q = 2 * (2 * d) := by rw [← hd]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2)
  rw [hGp, hGq, huv, show x - 4 * a = x + 4 * (-a) by ring, show y - 4 * b = y + 4 * (-b) by ring,
    quadPhi_add_four]

end GFun

end Eis

end

#print axioms Eis.span_two_isMaximal
#print axioms Eis.chi6_four
#print axioms Eis.norm_gamN
#print axioms Eis.gamN_two_cube
#print axioms Eis.gamN_one_mul_two
#print axioms Eis.gamN_one_mul_inv
#print axioms Eis.gamN_three
#print axioms Eis.Gp_coords
#print axioms Eis.norm_Gp
#print axioms Eis.Gp_eq_of_mod_four
