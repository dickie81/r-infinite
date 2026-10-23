import EisensteinQuadSieveErrors

/-! # The quadratic large sieve, part 6a: the pairs with `ρ_D(−1) = −1`, and `γ(D) = 1` (round 353)

S5e of round 312's plan, the first piece of S5e-6: the main terms of `Σ_3` and `Σ_4` can cancel
only if the root number `γ(D)` of round 351's `sig3_eq_main_add` is `1`.

* **The pairs with `ρ_D(−1) = −1` vanish** (`sig3_eq_zero`, `sig4_eq_zero`): their terms of
  `Σ_3` and of `Σ_4` change sign under `m ↦ −m` (the majorant is radial, `s(−m) = s(m)`,
  `ρ_D(−m) = ρ_D(−1)ρ_D(m)`), so both are `0`.
* **`γ(D) = φ(c)/2`** (`gamD_eq_gq4`): the Gauss sum of `ρ_D` at `1` and the quadratic sum
  `S_c(1)` are both `∏_{P∈D} ρ_P(c/π_P)·g(ρ_P, ψ_P)` (`gaussTr_q2_one`, from round 295's
  `gaussTr_prod_primes`; `sqSum_prod_one`, from round 298's `sqSum_mul` and
  `sqSum_prime`), and round 344's `sqSum_one_eq` gives `S_c(1) = (|σc|/2)·φ(c)`.
* **`γ(D) = 1` when `ρ_D(−1) = 1`** (`gamD_eq_one`): `ρ_P(−1) = χ₄(N(P))` (Mathlib's
  `quadraticChar_neg_one`), so `ρ_D(−1) = χ₄(N(c))` (`q2_neg_one_eq`) and `ρ_D(−1) = 1` gives
  `N(c) ≡ 1 mod 4` (`absNorm_mod_four`). With `c = a + bω`, `N(c) = a² − ab + b²`
  (`absNorm_coords`) and `φ(c) = 1 + i^{−b} + i^a + i^{b−a}` (`gq4_coords`, from round 297's
  `quad_gauss_coords`), which is `2` on the six classes modulo `4` with `a² − ab + b² ≡ 1`
  (`gq4_val_eq_two`, a finite check).
-/

open Complex NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

/-! ### The symmetry `m ↦ −m` -/

theorem sqN_neg (m : 𝓞 K) : sqN (-m) = sqN m := by
  by_cases hm : m = 0
  · rw [hm, neg_zero]
  obtain ⟨h1, h2, h3⟩ := sqk_spec hm
  have h2' : Squarefree (span {-sqk m}) := by rwa [Ideal.span_singleton_neg]
  have hneg : -m = -sqk m * sqe m ^ 2 := by rw [neg_mul, ← h1]
  rw [hneg, sqN_sqf_mul_sq h2' h3, Ideal.span_singleton_neg]
  rfl

theorem cop_neg (G : Finset Pr) (m : 𝓞 K) :
    (∀ Q ∈ G, ¬ πP Q ∣ -m) ↔ ∀ Q ∈ G, ¬ πP Q ∣ m := by
  simp only [dvd_neg]

theorem Phi_neg_div (M : ℝ) (m : 𝓞 K) :
    Majorant.Phi (σO (-m) / (Real.sqrt M : ℂ)) = Majorant.Phi (σO m / (Real.sqrt M : ℂ)) := by
  rw [Phi_eq_norm, map_neg, neg_div, norm_neg, ← Phi_eq_norm]

theorem q2_neg (D : Finset Pr) (m : 𝓞 K) : q2 D (-m) = q2 D (-1) * q2 D m := by
  rw [← q2_mul, neg_one_mul]

/-- A series that changes sign under `m ↦ −m` vanishes. -/
theorem tsum_eq_zero_of_neg {f : 𝓞 K → ℂ} (hf : ∀ m, f (-m) = -f m) : ∑' m, f m = 0 := by
  have h : ∑' m, f m = ∑' m, f (-m) := ((Equiv.neg (𝓞 K)).tsum_eq f).symm
  rw [tsum_congr hf, tsum_neg] at h
  linear_combination h / 2

/-- **The pairs with `ρ_D(−1) = −1` contribute nothing to `Σ_3`.** -/
theorem sig3_eq_zero {M : ℝ} (G : Finset Pr) {D : Finset Pr} (hD : q2 D (-1) = -1) :
    sig3 M G D = 0 := by
  unfold sig3
  refine tsum_eq_zero_of_neg fun m => ?_
  simp only [cop_neg, Phi_neg_div, q2_neg D m, hD]
  ring

/-- **The pairs with `ρ_D(−1) = −1` contribute nothing to `Σ_4`.** -/
theorem sig4_eq_zero {M Kt : ℝ} (G : Finset Pr) {D : Finset Pr} (hD : q2 D (-1) = -1) :
    sig4 M Kt G D = 0 := by
  unfold sig4
  refine tsum_eq_zero_of_neg fun m => ?_
  simp only [sqN_neg, cop_neg, Phi_neg_div, q2_neg D m, hD]
  ring

/-! ### The Gauss sums of `ρ_D` and `γ(D)` -/

/-- **The quadratic sum as a product over the primes**:
`S_c(1) = ∏_{P∈A} ρ_P(c/π_P)·g(ρ_P, ψ_P)` for `c = ∏_{P∈A} π_P`. -/
theorem sqSum_prod_one (A : Finset Pr) :
    sqSum (∏ P ∈ A, πP P) 1 = ∏ P ∈ A,
      (quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) (∏ Q ∈ A.erase P, πP Q)) *
        gaussSum (quadR (𝓞 K ⧸ span {πP P}) ℂ) (ψQ (πP P) (ne_zero_of_maximal (πP P)))) := by
  induction A using Finset.induction_on with
  | empty => simp [sqSum_one_left]
  | insert P A hPA ih =>
    have hP0 : πP P ≠ 0 := ne_zero_of_maximal (πP P)
    have hA0 : ∏ Q ∈ A, πP Q ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun Q _ => ne_zero_of_maximal (πP Q)
    have hcop : IsCoprime (πP P) (∏ Q ∈ A, πP Q) :=
      IsCoprime.prod_right fun Q hQ => isCoprime_πP fun h => hPA (h ▸ hQ)
    have hAP := prod_not_mem hPA
    have h1A : ∀ Q ∈ A, πP P ∉ span {πP Q} := fun Q hQ =>
      not_mem_Pr_of_ne fun e => hPA (e ▸ hQ)
    rw [Finset.prod_insert hPA, sqSum_mul _ _ hP0 hA0 hcop,
      sqSum_prime (πP P) (two_not_mem_Pr P) _ hAP, sqSum_prod_πP A (πP P) h1A, ih,
      Finset.prod_insert hPA, Finset.erase_insert hPA]
    have hcross : ∀ Q ∈ A, quadR (𝓞 K ⧸ span {πP Q}) ℂ
        (Ideal.Quotient.mk (span {πP Q}) (∏ R ∈ (insert P A).erase Q, πP R)) =
        quadR (𝓞 K ⧸ span {πP Q}) ℂ (Ideal.Quotient.mk (span {πP Q}) (πP P)) *
          quadR (𝓞 K ⧸ span {πP Q}) ℂ (Ideal.Quotient.mk (span {πP Q}) (∏ R ∈ A.erase Q, πP R)) := by
      intro Q hQ
      have hne : Q ≠ P := fun e => hPA (e ▸ hQ)
      have hPn : P ∉ A.erase Q := fun h => hPA (Finset.mem_of_mem_erase h)
      rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.prod_insert hPn, map_mul, map_mul]
    have hprod : ∏ Q ∈ A, (quadR (𝓞 K ⧸ span {πP Q}) ℂ
        (Ideal.Quotient.mk (span {πP Q}) (∏ R ∈ (insert P A).erase Q, πP R)) *
          gaussSum (quadR (𝓞 K ⧸ span {πP Q}) ℂ) (ψQ (πP Q) (ne_zero_of_maximal (πP Q)))) =
        ∏ Q ∈ A, (quadR (𝓞 K ⧸ span {πP Q}) ℂ (Ideal.Quotient.mk (span {πP Q}) (πP P)) *
          (quadR (𝓞 K ⧸ span {πP Q}) ℂ (Ideal.Quotient.mk (span {πP Q}) (∏ R ∈ A.erase Q, πP R)) *
            gaussSum (quadR (𝓞 K ⧸ span {πP Q}) ℂ) (ψQ (πP Q) (ne_zero_of_maximal (πP Q))))) :=
      Finset.prod_congr rfl fun Q hQ => by rw [hcross Q hQ, mul_assoc]
    rw [hprod]
    simp only [Finset.prod_mul_distrib]

/-- **The Gauss sum of `ρ_D` at `1` as a product over the primes** (round 295's
`gaussTr_prod_primes`). -/
theorem gaussTr_q2_one (D : Finset Pr) :
    gaussTr (∏ P ∈ D, πP P) (q2 D) 1 = ∏ P ∈ D,
      (quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) (∏ Q ∈ D.erase P, πP Q)) *
        gaussSum (quadR (𝓞 K ⧸ span {πP P}) ℂ) (ψQ (πP P) (ne_zero_of_maximal (πP P)))) := by
  have h := gaussTr_prod_primes πP D (hcopPr D) (fun P => quadR (𝓞 K ⧸ span {πP P}) ℂ)
    (fun P _ => quadR_ne_one P) 1
  refine h.trans (Finset.prod_congr rfl fun P _ => ?_)
  rw [map_one, MulChar.map_one, mul_one]

/-- **The Gauss sum of `ρ_D` is the quadratic sum**: `G_c(ρ_D, 1) = S_c(1)`. -/
theorem gaussTr_q2_one_eq_sqSum (D : Finset Pr) :
    gaussTr (∏ P ∈ D, πP P) (q2 D) 1 = sqSum (∏ P ∈ D, πP P) 1 := by
  rw [gaussTr_q2_one, sqSum_prod_one]

theorem q2_one (D : Finset Pr) : q2 D 1 = 1 := by
  unfold q2
  exact Finset.prod_eq_one fun P _ => by rw [map_one, MulChar.map_one]

/-- **`γ(D) = φ(c)/2`**, with round 344's `φ(c) = gq4 c`. -/
theorem gamD_eq_gq4 (D : Finset Pr) : gamD D = gq4 (∏ P ∈ D, πP P) / 2 := by
  have h1 := gaussTr_q2_eq_q2 D 1
  rw [gaussTr_q2_one_eq_sqSum, sqSum_one_eq _ (prod_πP_ne_zero D), q2_one, one_mul,
    norm_σO_eq_sqrt, absNorm_span_prod_πP] at h1
  have hs : (((Real.sqrt (nI D)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (nI_pos D)).ne'
  push_cast at h1
  field_simp at h1 ⊢
  linear_combination -h1

/-! ### `ρ_D(−1)` and `N(c)` modulo `4` -/

theorem quadR_neg_one_Pr (P : Pr) :
    quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) (-1)) =
      ((ZMod.χ₄ (absNorm P.1 : ZMod 4) : ℤ) : ℂ) := by
  have hF := ringChar_ne_two_of_not_mem (span {πP P}) (two_not_mem_Pr P)
  rw [map_neg, map_one]
  simp only [quadR, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [quadraticChar_neg_one hF, ← absNorm_eq_card, (πP_spec P).2]

/-- **`ρ_D(−1) = χ₄(N(c))`**. -/
theorem q2_neg_one_eq (D : Finset Pr) :
    q2 D (-1) = ((ZMod.χ₄ ((absNorm (idl D) : ℕ) : ZMod 4) : ℤ) : ℂ) := by
  unfold q2
  rw [Finset.prod_congr rfl fun P _ => quadR_neg_one_Pr P, absNorm_idl, Nat.cast_prod,
    ← Int.cast_prod]
  congr 1
  exact (map_prod ZMod.χ₄.toMonoidHom _ _).symm

/-- **`ρ_D(−1) = 1` gives `N(c) ≡ 1 mod 4`.** -/
theorem absNorm_mod_four (D : Finset Pr) (h : q2 D (-1) = 1) : absNorm (idl D) % 4 = 1 := by
  rw [q2_neg_one_eq, ZMod.χ₄_nat_eq_if_mod_four] at h
  split_ifs at h with h1 h2
  · norm_num at h
  · exact h2
  · norm_num at h

/-! ### `φ(c) = 2` for `N(c) ≡ 1 mod 4` -/

theorem I_zpow_four_mul_add (q k : ℤ) : I ^ (4 * q + k) = I ^ k := by
  rw [zpow_add₀ I_ne_zero, zpow_mul]
  have : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, Complex.I_pow_four]
  rw [this, one_zpow, one_mul]

theorem gq4_val_eq_two (a b : ℤ) (h : (a ^ 2 - a * b + b ^ 2) % 4 = 1) :
    1 + I ^ (-b) + I ^ a + I ^ (b - a) = 2 := by
  obtain ⟨q, r, hr0, hr4, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 4 ∧ a = 4 * q + r :=
    ⟨a / 4, a % 4, Int.emod_nonneg a (by norm_num), Int.emod_lt_of_pos a (by norm_num),
      (Int.mul_ediv_add_emod a 4).symm⟩
  obtain ⟨s, u, hu0, hu4, rfl⟩ : ∃ s u : ℤ, 0 ≤ u ∧ u < 4 ∧ b = 4 * s + u :=
    ⟨b / 4, b % 4, Int.emod_nonneg b (by norm_num), Int.emod_lt_of_pos b (by norm_num),
      (Int.mul_ediv_add_emod b 4).symm⟩
  have hN : ((4 * q + r) ^ 2 - (4 * q + r) * (4 * s + u) + (4 * s + u) ^ 2) % 4 =
      (r ^ 2 - r * u + u ^ 2) % 4 := by
    have : (4 * q + r) ^ 2 - (4 * q + r) * (4 * s + u) + (4 * s + u) ^ 2 =
        (r ^ 2 - r * u + u ^ 2) + 4 * (4 * q ^ 2 + 2 * q * r - 4 * q * s - q * u - r * s +
          4 * s ^ 2 + 2 * s * u) := by ring
    rw [this, Int.add_mul_emod_self_left]
  rw [hN] at h
  rw [show -(4 * s + u) = 4 * (-s - 1) + (4 - u) by ring, I_zpow_four_mul_add,
    I_zpow_four_mul_add,
    show 4 * s + u - (4 * q + r) = 4 * (s - q - 1) + (4 + u - r) by ring, I_zpow_four_mul_add]
  interval_cases r <;> interval_cases u <;> norm_num at h <;> norm_num <;> ring

/-- **`φ` in coordinates** (round 344's `quad_gauss_coords`):
`φ(a + bω) = 1 + i^{−b} + i^a + i^{b−a}`. -/
theorem gq4_coords (a b : ℤ) (hc : (a : 𝓞 K) + (b : 𝓞 K) * ω ≠ 0) :
    gq4 ((a : 𝓞 K) + (b : 𝓞 K) * ω) = 1 + I ^ (-b) + I ^ a + I ^ (b - a) := by
  have h1 := quad_gauss_coords a b hc
  have h2 := sqSum_one_eq _ hc
  rw [sqSum_one, h1] at h2
  have hs : (((‖σO ((a : 𝓞 K) + (b : 𝓞 K) * ω)‖ / 2 : ℝ)) : ℂ) ≠ 0 := by
    have := σO_norm_ne_zero hc
    push_cast
    exact div_ne_zero this two_ne_zero
  exact (mul_left_cancel₀ hs h2).symm

/-- `N(a + bω) = a² − ab + b²`. -/
theorem absNorm_coords (a b : ℤ) :
    ((absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * ω}) : ℕ) : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  have h := absNorm_crd ![a, b]
  have hc : crd ![a, b] = (a : 𝓞 K) + (b : 𝓞 K) * ω := by simp [crd]
  rw [hc] at h
  have h' : ((absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * ω}) : ℕ) : ℝ) =
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    rw [h]; simp; ring
  exact_mod_cast h'

/-- **`γ(D) = 1` when `ρ_D(−1) = 1`**: then `N(c) ≡ 1 mod 4`, and `φ(c) = 2` on those classes. -/
theorem gamD_eq_one {D : Finset Pr} (h : q2 D (-1) = 1) : gamD D = 1 := by
  rw [gamD_eq_gq4]
  obtain ⟨a, b, hab⟩ := exists_coords (∏ P ∈ D, πP P)
  have hN := absNorm_mod_four D h
  rw [← span_prod_πP, hab] at hN
  have hN' : (a ^ 2 - a * b + b ^ 2) % 4 = 1 := by
    rw [← absNorm_coords]
    exact_mod_cast hN
  have hc : (a : 𝓞 K) + (b : 𝓞 K) * ω ≠ 0 := hab ▸ prod_πP_ne_zero D
  rw [hab, gq4_coords a b hc, gq4_val_eq_two a b hN']
  norm_num

end Eis

end

#print axioms Eis.sqN_neg
#print axioms Eis.cop_neg
#print axioms Eis.Phi_neg_div
#print axioms Eis.q2_neg
#print axioms Eis.tsum_eq_zero_of_neg
#print axioms Eis.sig3_eq_zero
#print axioms Eis.sig4_eq_zero
#print axioms Eis.sqSum_prod_one
#print axioms Eis.gaussTr_q2_one
#print axioms Eis.gaussTr_q2_one_eq_sqSum
#print axioms Eis.q2_one
#print axioms Eis.gamD_eq_gq4
#print axioms Eis.quadR_neg_one_Pr
#print axioms Eis.q2_neg_one_eq
#print axioms Eis.absNorm_mod_four
#print axioms Eis.I_zpow_four_mul_add
#print axioms Eis.gq4_val_eq_two
#print axioms Eis.gq4_coords
#print axioms Eis.absNorm_coords
#print axioms Eis.gamD_eq_one
