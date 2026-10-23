/-
# The teeth, one prime at a time (round 186)

Plain statement. Work modulo a prime `p` (more generally in a finite field `F` of odd size `q`).
Count the "teeth" of the lattice ball seen at `p`: the number of solutions of
`x² + y² = a` (2D) and `x² + y² + z² + w² = a` (4D) with coordinates mod `p`.

* 2D, `a ≠ 0`: exactly `q − χ₄(q)` teeth, where `χ₄(q) = ±1` according as `q ≡ 1` or `3 mod 4`
  (`card_two_sq`). At `a = 0`: `q + (q − 1)·χ₄(q)` (`card_two_sq_zero`).
* 4D, `a ≠ 0`: exactly `q³ − q` teeth (`card_four_sq`): the density of teeth relative to a smooth
  sphere (`q³` points per shell) is `1 − 1/q²`, the same for every nonzero `a`.

These are the local factors `δ_p` of round 182: the 2D factor `1 − χ₄(p)/p` and the 4D factor
`1 − 1/p²` are exactly the prime-`p` Euler factors of `L(1, χ₄)⁻¹` and `ζ(2)⁻¹`. The global
statement "the teeth on shell `n` = smooth sphere × ∏_p δ_p(n)" (Siegel) is NOT proved here; it
remains the numerical check of round 182 (exact for `d ≤ 8`).

Proof route: count solutions by fibres (`card_add_eq`), count square roots with the quadratic
character (`quadraticChar_card_sqrts`), and evaluate the resulting character sum as a Jacobi sum
(`jacobiSum_nontrivial_inv`: `J(χ, χ) = −χ(−1)` for the quadratic `χ`).
-/
import Mathlib

open Finset

namespace LocalTeeth

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Counting solutions of `f x + g y = a` fibre by fibre. -/
lemma card_add_eq {α β : Type*} [Fintype α] [Fintype β] (f : α → F) (g : β → F) (a : F) :
    ((univ.filter (fun p : α × β => f p.1 + g p.2 = a)).card : ℤ) =
      ∑ b : F, ((univ.filter (fun x => f x = b)).card : ℤ) *
        ((univ.filter (fun y => g y = a - b)).card : ℤ) := by
  have h1 : ((univ.filter (fun p : α × β => f p.1 + g p.2 = a)).card : ℤ) =
      ∑ x : α, ((univ.filter (fun y => g y = a - f x)).card : ℤ) := by
    rw [card_filter, ← univ_product_univ, sum_product]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun y _ => ?_
    congr 1
    exact propext ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
  rw [h1, ← sum_fiberwise univ f (fun x => ((univ.filter (fun y => g y = a - f x)).card : ℤ))]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, nsmul_eq_mul]

variable (hF : ringChar F ≠ 2)
include hF

local notation "χ" => quadraticChar F

/-- Square roots counted by the quadratic character. -/
lemma card_sqrt (b : F) : ((univ.filter (fun x : F => x ^ 2 = b)).card : ℤ) = χ b + 1 := by
  rw [← quadraticChar_card_sqrts hF b, Set.toFinset_ofPred]

/-- Teeth of the 2D ball at a finite field, as a character sum. -/
lemma card_two_sq_sum (a : F) :
    ((univ.filter (fun p : F × F => p.1 ^ 2 + p.2 ^ 2 = a)).card : ℤ) =
      ∑ b : F, (χ b + 1) * (χ (a - b) + 1) := by
  rw [card_add_eq (fun x : F => x ^ 2) (fun y : F => y ^ 2) a]
  simp only [card_sqrt hF]

lemma sum_chi_sub (a : F) : ∑ b : F, χ (a - b) = 0 := by
  rw [← quadraticChar_sum_zero hF]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)

lemma jacobi_quadratic : jacobiSum χ χ = -χ (-1) := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rwa [(quadraticChar_isQuadratic F).inv] at h

/-- **2D teeth mod `p`, nonzero shell:** `#{x² + y² = a} = q − χ(−1)`. -/
theorem card_two_sq {a : F} (ha : a ≠ 0) :
    ((univ.filter (fun p : F × F => p.1 ^ 2 + p.2 ^ 2 = a)).card : ℤ) = Fintype.card F - χ (-1) := by
  rw [card_two_sq_sum hF]
  have hJ : ∑ b : F, χ b * χ (a - b) = -χ (-1) := by
    rw [← jacobi_quadratic hF, jacobiSum]
    rw [← Fintype.sum_equiv (Equiv.mulLeft₀ a ha) (fun x => χ (a * x) * χ (a - a * x))
      (fun b => χ b * χ (a - b)) (fun x => rfl)]
    refine sum_congr rfl fun x _ => ?_
    have h2 := quadraticChar_sq_one ha
    rw [show a - a * x = a * (1 - x) by ring, map_mul, map_mul]
    linear_combination (χ x * χ (1 - x)) * h2
  have e : ∀ b : F, (χ b + 1) * (χ (a - b) + 1) = χ b * χ (a - b) + χ b + χ (a - b) + 1 :=
    fun b => by ring
  simp only [e, sum_add_distrib, hJ, quadraticChar_sum_zero hF, sum_chi_sub hF, sum_const,
    card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **2D teeth mod `p`, zero shell:** `#{x² + y² = 0} = q + (q − 1)·χ(−1)`. -/
theorem card_two_sq_zero :
    ((univ.filter (fun p : F × F => p.1 ^ 2 + p.2 ^ 2 = 0)).card : ℤ) =
      Fintype.card F + (Fintype.card F - 1) * χ (-1) := by
  rw [card_two_sq_sum hF]
  have hsq : ∀ b : F, χ b * χ (0 - b) = χ (-1) * (if b = 0 then 0 else 1) := fun b => by
    by_cases hb : b = 0
    · simp [hb]
    · rw [zero_sub, show -b = -1 * b by ring, map_mul, ite_eq_right_iff.mpr (fun h => absurd h hb)]
      have := quadraticChar_sq_one hb
      linear_combination χ (-1) * this
  have e : ∀ b : F, (χ b + 1) * (χ (0 - b) + 1) = χ b * χ (0 - b) + χ b + χ (0 - b) + 1 :=
    fun b => by ring
  simp only [e, sum_add_distrib, hsq, ← mul_sum, quadraticChar_sum_zero hF, sum_chi_sub hF,
    sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hcount : ∑ b : F, (if b = 0 then (0 : ℤ) else 1) = Fintype.card F - 1 := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one, filter_ne',
      card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub Fintype.card_pos]
    simp
  rw [hcount]
  ring

/-- **4D teeth mod `p`, nonzero shell:** `#{x² + y² + z² + w² = a} = q³ − q`. -/
theorem card_four_sq {a : F} (ha : a ≠ 0) :
    ((univ.filter (fun p : (F × F) × (F × F) =>
      (p.1.1 ^ 2 + p.1.2 ^ 2) + (p.2.1 ^ 2 + p.2.2 ^ 2) = a)).card : ℤ) =
      (Fintype.card F : ℤ) ^ 3 - Fintype.card F := by
  set q : ℤ := ((Fintype.card F : ℕ) : ℤ) with hq
  set ε : ℤ := χ (-1)
  have hε : ε ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hN : ∀ b : F, ((univ.filter (fun p : F × F => p.1 ^ 2 + p.2 ^ 2 = b)).card : ℤ) =
      (q - ε) + (if b = 0 then q * ε else 0) := fun b => by
    by_cases hb : b = 0
    · rw [ite_eq_left_iff.mpr (fun h => absurd hb h), hb, card_two_sq_zero hF]; ring
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hb), card_two_sq hF hb, add_zero]
  rw [card_add_eq (fun p : F × F => p.1 ^ 2 + p.2 ^ 2) (fun p : F × F => p.1 ^ 2 + p.2 ^ 2) a]
  simp only [hN]
  have e : ∀ b : F, ((q - ε) + (if b = 0 then q * ε else 0)) *
      ((q - ε) + (if a - b = 0 then q * ε else 0)) =
      (q - ε) ^ 2 + (q - ε) * (if b = 0 then q * ε else 0) +
        (q - ε) * (if b = a then q * ε else 0) +
        (if b = 0 then q * ε else 0) * (if b = a then q * ε else 0) := fun b => by
    have : (a - b = 0) ↔ (b = a) := ⟨fun h => (sub_eq_zero.mp h).symm, fun h => by rw [h, sub_self]⟩
    simp only [this]; ring
  have hcross : ∀ b : F, (if b = 0 then q * ε else 0) * (if b = a then q * ε else (0 : ℤ)) = 0 :=
    fun b => by
      by_cases hb : b = 0
      · simp [hb, Ne.symm ha]
      · simp [hb]
  simp only [e, hcross, sum_add_distrib, ← mul_sum, sum_ite_eq', mem_univ, ite_true, sum_const,
    card_univ, nsmul_eq_mul, add_zero]
  linear_combination (-q) * hε

omit hF in
/-- **At a prime `p`:** the 2D tooth count on a nonzero shell is `p − χ₄(p)`, and the 4D count is
`p³ − p`, i.e. tooth density `1 − 1/p²`. -/
theorem teeth_mod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ((univ.filter (fun x : ZMod p × ZMod p => x.1 ^ 2 + x.2 ^ 2 = a)).card : ℤ) = p - ZMod.χ₄ p ∧
    ((univ.filter (fun x : (ZMod p × ZMod p) × (ZMod p × ZMod p) =>
      (x.1.1 ^ 2 + x.1.2 ^ 2) + (x.2.1 ^ 2 + x.2.2 ^ 2) = a)).card : ℤ) = (p : ℤ) ^ 3 - p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  refine ⟨?_, ?_⟩
  · rw [card_two_sq hF ha, quadraticChar_neg_one hF, ZMod.card]
  · rw [card_four_sq hF ha, ZMod.card]

end LocalTeeth
