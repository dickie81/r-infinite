import EisensteinGaussSum

/-! # Round 474: the sextic symbol of a rational cube is the Jacobi symbol of its norm

Step 1 of round 471's plan for the real characters. For `d ∈ ℤ` and every ideal `𝔞` of `ℤ[ω]` of norm prime
to `6`, round 281's symbol satisfies `(d³/𝔞)₆ = J(d | N𝔞)`, the Jacobi symbol (`sym6_intCast_cube`).

* `intCast_pow_card_div_two`: Euler's criterion over a finite field `F` of odd characteristic, for a rational
  integer: `d^{q/2} = J(d | q)` in `F`, `q = |F|`. With `q = p^n`, by induction on `n` from Mathlib's
  `legendreSym.eq_pow` and `x^p = x` in `ZMod p` (`zmod_pow_eq_legendre_pow`), and `J(d | p^n) = J(d | p)^n`.
* `quadraticChar_intCast`: the same as a quadratic character, `ρ_F(d) = J(d | q)`, through Mathlib's
  `quadraticChar_eq_pow_of_char_ne_two'`.
* `chi6_intCast_cube`: at a maximal ideal `P` with `6 ∉ P`, `χ_P(d³) = χ_P(d)³ = ρ(d)`, since `χ_P³` is the
  quadratic character of `𝓞/P` (round 292's `chi6_cube`); so `χ_P(d³) = J(d | N(P))`.
* `sym6_intCast_cube`: both sides are multiplicative in `𝔞` (round 281's `sym6_mul_right`, Mathlib's
  `jacobiSym.mul_right'`), so it follows by induction on the factorization of `𝔞`.
-/

open NumberField Ideal

namespace Eis

section Euler

variable {F : Type*} [Field F] [Fintype F]

/-- `d^e = J(d | p)^{n+1}` in `ZMod p` when `p^{n+1} = 2e + 1`. -/
lemma zmod_pow_eq_legendre_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (d : ℤ) :
    ∀ n e : ℕ, p ^ (n + 1) = 2 * e + 1 → (d : ZMod p) ^ e = ((legendreSym p d ^ (n + 1) : ℤ) : ZMod p) := by
  obtain ⟨h, hh⟩ : Odd p := hp.out.odd_of_ne_two hp2
  intro n
  induction n with
  | zero =>
    intro e he
    rw [zero_add, pow_one] at he
    have : e = p / 2 := by omega
    rw [this, pow_one, legendreSym.eq_pow]
  | succ n ih =>
    intro e he
    obtain ⟨e', he'⟩ : Odd (p ^ (n + 1)) := (hp.out.odd_of_ne_two hp2).pow
    have h2 : 2 * e + 1 = p * (2 * e' + 1) := by rw [← he, ← he', pow_succ, mul_comm]
    have hee : e = p * e' + h := by
      rw [hh] at h2
      have : 2 * e = 2 * ((2 * h + 1) * e' + h) := by linarith
      rw [hh]
      omega
    rw [hee, pow_add, pow_mul, ZMod.pow_card, ih e' he', ← show ((d : ZMod p) ^ (p / 2)) = (d : ZMod p) ^ h
      by rw [show p / 2 = h by omega], ← legendreSym.eq_pow]
    push_cast
    ring

/-- **Euler's criterion over a finite field of odd characteristic, for a rational integer**:
`d^{q/2} = J(d | q)` in `F`, with `q = |F|`. -/
theorem intCast_pow_card_div_two (hF : ringChar F ≠ 2) (d : ℤ) :
    (d : F) ^ (Fintype.card F / 2) = (jacobiSym d (Fintype.card F) : F) := by
  obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
  set p := ringChar F with hpdef
  have : Fact p.Prime := ⟨hp⟩
  have hn : (n : ℕ) = ((n : ℕ) - 1) + 1 := (Nat.succ_pred_eq_of_pos n.pos).symm
  obtain ⟨e, he⟩ : Odd (p ^ (n : ℕ)) := (hp.odd_of_ne_two hF).pow
  have hq2 : Fintype.card F / 2 = e := by rw [hq, he]; omega
  have hz := zmod_pow_eq_legendre_pow hF d ((n : ℕ) - 1) e (by rw [← hn, he])
  rw [← hn] at hz
  have hJ : jacobiSym d (Fintype.card F) = legendreSym p d ^ (n : ℕ) := by
    rw [hq, jacobiSym.pow_right, jacobiSym.legendreSym.to_jacobiSym]
  rw [hq2, hJ]
  have hc : ∀ z : ℤ, (z : F) = ZMod.castHom (dvd_refl p) F (z : ZMod p) := fun z ↦ by simp
  rw [hc d, ← map_pow, hz, hc]

end Euler

section Cube

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Euler's criterion for a rational integer, as a quadratic character**: `ρ_F(d) = J(d | q)` for a finite
field `F` of odd characteristic, `q = |F|`. -/
theorem quadraticChar_intCast (hF : ringChar F ≠ 2) (d : ℤ) :
    quadraticChar F d = jacobiSym d (Fintype.card F) := by
  have h := quadraticChar_eq_pow_of_char_ne_two' hF (d : F)
  rw [intCast_pow_card_div_two hF d] at h
  have hq : quadraticChar F d ∈ ({0, 1, -1} : Set ℤ) := by
    rcases eq_or_ne (d : F) 0 with h0 | h0
    · rw [h0, quadraticChar_zero]; simp
    · rcases quadraticChar_dichotomy h0 with h1 | h1 <;> rw [h1] <;> simp
  have hJ : jacobiSym d (Fintype.card F) ∈ ({0, 1, -1} : Set ℤ) := by
    rcases jacobiSym.trichotomy d (Fintype.card F) with h1 | h1 | h1 <;> rw [h1] <;> simp
  exact Int.cast_injOn_of_ringChar_ne_two hF hq hJ h

open Classical in
/-- **`χ_P(d³) = J(d | N(P))`** for `d ∈ ℤ`, at a prime `P` away from `6`: `χ_P³` is the quadratic
character `ρ` (round 292's `chi6_cube`). -/
theorem chi6_intCast_cube (P : Ideal (𝓞 K)) [P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) (d : ℤ) :
    chi6 P hP6 (Ideal.Quotient.mk P ((d : 𝓞 K) ^ 3)) = (jacobiSym d (Fintype.card (𝓞 K ⧸ P)) : ℂ) := by
  have hF := ringChar_ne_two P hP6
  rw [map_pow, map_intCast, map_pow, ← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), chi6_cube P hP6,
    quadR, MulChar.ringHomComp_apply, quadraticChar_intCast hF d]
  simp

/-- `χ_P(d³) = J(d | N(P))` for `chiP`. -/
theorem chiP_intCast_cube {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hP6 : (6 : 𝓞 K) ∉ P) (d : ℤ) :
    chiP P ((d : 𝓞 K) ^ 3) = (jacobiSym d (absNorm P) : ℂ) := by
  unfold chiP
  split_ifs with h
  · rw [absNorm_eq_card]
    exact chi6_intCast_cube P h.2 d
  · exact absurd ⟨hP, hP6⟩ h

/-- A prime ideal of norm prime to `6` is maximal and does not contain `6`. -/
lemma isMaximal_and_six_not_mem {P : Ideal (𝓞 K)} (hP : Prime P) (hN : (absNorm P).Coprime 6) :
    P.IsMaximal ∧ (6 : 𝓞 K) ∉ P := by
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hPm : P.IsMaximal := hPp.isMaximal hP.ne_zero
  refine ⟨hPm, fun h6 ↦ ?_⟩
  have h0 : ((6 : ℕ) : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast h6
  have hd := ringChar.dvd h0
  obtain ⟨n, hp, hq⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))
  have hdq : ringChar (𝓞 K ⧸ P) ∣ absNorm P := by
    rw [absNorm_eq_card, hq]
    exact dvd_pow_self _ n.ne_zero
  exact hp.ne_one ((Nat.Coprime.coprime_dvd_left hdq hN).eq_one_of_dvd hd)

/-- **The sextic symbol of a rational cube is the Jacobi symbol of the norm**: `(d³/𝔞)₆ = J(d | N𝔞)` for
`d ∈ ℤ` and every ideal `𝔞` of `ℤ[ω]` whose norm is prime to `6`. -/
theorem sym6_intCast_cube (d : ℤ) {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    sym6 ((d : 𝓞 K) ^ 3) I = (jacobiSym d (absNorm I) : ℂ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    exfalso
    rw [Submodule.zero_eq_bot, absNorm_bot] at hI
    norm_num at hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.1 hu, absNorm_top, jacobiSym.one_right, Int.cast_one, ← Ideal.one_eq_top,
      sym6_one_right]
  | h₃ I P hI0 hP ih =>
    rw [map_mul] at hI
    have hPN : (absNorm P).Coprime 6 := Nat.Coprime.coprime_mul_right hI
    have hIN : (absNorm I).Coprime 6 := Nat.Coprime.coprime_mul_left hI
    have hP0 : absNorm P ≠ 0 := fun h ↦ by rw [h] at hPN; norm_num at hPN
    have hI0' : absNorm I ≠ 0 := fun h ↦ by rw [h] at hIN; norm_num at hIN
    obtain ⟨hPm, hP6⟩ := isMaximal_and_six_not_mem hP hPN
    have hsP : sym6 ((d : 𝓞 K) ^ 3) P = chiP P ((d : 𝓞 K) ^ 3) := by
      rw [sym6, UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible, normalize_eq,
        Multiset.map_singleton, Multiset.prod_singleton]
    rw [sym6_mul_right _ hP.ne_zero hI0, map_mul, jacobiSym.mul_right' d hP0 hI0', Int.cast_mul, ih hIN, hsP,
      chiP_intCast_cube hPm hP6]

end Cube

end Eis

#print axioms Eis.intCast_pow_card_div_two
#print axioms Eis.quadraticChar_intCast
#print axioms Eis.chi6_intCast_cube
#print axioms Eis.chiP_intCast_cube
#print axioms Eis.sym6_intCast_cube
