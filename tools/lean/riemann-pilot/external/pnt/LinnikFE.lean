/-
# Round 522, part 1: the functional equation of `L(s, χ)` on vertical lines

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For a primitive Dirichlet character `χ` mod `N ≥ 1` and `1/2 ≤ σ < 1`,
`|L(1 − σ − it, χ)| ≤ 6N^{σ−1/2}(e⁴|σ + it|)^{σ−1/2}|L(σ + it, χ⁻¹)|` (`norm_LFunction_one_sub_le`): the analogue for
`L(s, χ)` of round 517's `Subconvexity.norm_zeta_one_sub_le`, with the factor `N^{σ−1/2}`.

* `gaussSum_inv`, `rootNumber_inv`: `τ(χ⁻¹) = conj(χ(−1))conj(τ(χ))` and `ε(χ⁻¹) = conj ε(χ)`, for Mathlib's root
  number `ε(χ) = τ(χ)/(i^a N^{1/2})`.
* `rootNumber_mul_inv`, `norm_rootNumber`: `ε(χ)ε(χ⁻¹) = 1` for primitive `χ`, from Mathlib's functional equation
  `IsPrimitive.completedLFunction_one_sub` for `χ` at `s = −1` and for `χ⁻¹` at `s = 2`, with `Λ(2, χ) ≠ 0`; so
  `|ε(χ)| = 1`.
* `norm_Gamma_mul_sin_le`: `|Γ(s)sin(πs/2)| ≤ 3(e⁴|s|)^{σ−1/2}` on `Re s = σ ≥ 1/2`, for the odd characters
  (round 517's `Subconvexity.norm_Gamma_mul_le_of`, the bound behind its cosine case).
* `norm_Gammaℂ_mul_le`: `|Γ_ℂ(s)w| ≤ 6(e⁴|s|)^{σ−1/2}` for `w = cos(πs/2)` or `sin(πs/2)`.
* `norm_LFunction_one_sub_le`: Mathlib's `LFunction_eq_completed_div_gammaFactor` at `1 − s` and at `s`, with
  `Γ_ℝ(s)/Γ_ℝ(1 − s) = Γ_ℂ(s)cos(πs/2)` for even `χ` (Mathlib's `inv_Gammaℝ_one_sub`) and
  `Γ_ℝ(s + 1)/Γ_ℝ(2 − s) = Γ_ℂ(s)sin(πs/2)` for odd `χ` (`inv_Gammaℝ_two_sub`).
-/
import Subconvexity

open Complex Real Filter Topology

noncomputable section

namespace LinnikFE

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ### The root number -/

/-- `τ(χ⁻¹) = conj(χ(−1))·conj(τ(χ))` for the standard additive character. -/
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ ZMod.stdAddChar
      = (starRingEnd ℂ) (χ (-1)) * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) := by
  unfold gaussSum
  rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp (Equiv.neg (ZMod N))]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.neg_apply]
  have h1 : χ⁻¹ (-a) = (starRingEnd ℂ) (χ (-a)) := by
    rw [starRingEnd_apply, MulChar.star_apply']
  have h2 : χ (-a) = χ (-1) * χ a := by rw [← map_mul, neg_one_mul]
  rw [h1, AddChar.map_neg_eq_conj, h2, map_mul, map_mul]
  ring

omit [NeZero N] in
theorem even_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [MulChar.inv_apply_eq_inv', inv_eq_one]

omit [NeZero N] in
theorem odd_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Odd ↔ χ.Odd := by
  unfold DirichletCharacter.Odd
  rw [MulChar.inv_apply_eq_inv', inv_eq_iff_eq_inv, inv_neg, inv_one]

/-- `ε(χ⁻¹) = conj ε(χ)`. -/
theorem rootNumber_inv (χ : DirichletCharacter ℂ N) :
    rootNumber χ⁻¹ = (starRingEnd ℂ) (rootNumber χ) := by
  have hN : (starRingEnd ℂ) ((N : ℂ) ^ (1 / 2 : ℂ)) = (N : ℂ) ^ (1 / 2 : ℂ) := by
    have e : (N : ℂ) ^ (1 / 2 : ℂ) = (((N : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg N)]; push_cast; rfl
    rw [e, Complex.conj_ofReal]
  unfold rootNumber
  rw [gaussSum_inv, map_div₀, map_div₀, hN]
  rcases χ.even_or_odd with h | h
  · have h1 : χ (-1) = 1 := h
    have h' : χ⁻¹.Even := (even_inv_iff χ).2 h
    simp only [h, h', ↓reduceIte, pow_zero, div_one, h1, map_one, one_mul]
  · have h1 : χ (-1) = -1 := h
    have hne : ¬ χ.Even := fun he => by
      have : χ (-1) = 1 := he
      rw [h1] at this; norm_num at this
    have hne' : ¬ χ⁻¹.Even := fun he => hne ((even_inv_iff χ).1 he)
    simp only [hne, hne', ↓reduceIte, pow_one, h1, map_neg, map_one, Complex.conj_I]
    ring

/-- For primitive `χ`, `ε(χ)ε(χ⁻¹) = 1`: the functional equation for `χ` at `s = −1` and for `χ⁻¹` at `s = 2`
gives `Λ(2, χ) = ε(χ)ε(χ⁻¹)Λ(2, χ)`, and `Λ(2, χ) ≠ 0`. -/
theorem rootNumber_mul_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ * rootNumber χ⁻¹ = 1 := by
  have hχ' : χ⁻¹.IsPrimitive := by
    unfold DirichletCharacter.IsPrimitive at hχ ⊢
    rw [conductor_inv]; exact hχ
  have e1 := hχ.completedLFunction_one_sub (1 - 2)
  have e2 := hχ'.completedLFunction_one_sub 2
  rw [inv_inv] at e2
  have e3 : (1 : ℂ) - (1 - 2) = 2 := by ring
  rw [e3, e2] at e1
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hpow : (N : ℂ) ^ ((1 : ℂ) - 2 - 1 / 2) * (N : ℂ) ^ ((2 : ℂ) - 1 / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hN0]; norm_num
  have hL : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
  have hC : completedLFunction χ 2 ≠ 0 := by
    intro h0
    apply hL
    rw [LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero), h0, zero_div]
  have key : completedLFunction χ 2 * (rootNumber χ * rootNumber χ⁻¹ - 1) = 0 := by
    linear_combination (-1 : ℂ) * e1 - (rootNumber χ * rootNumber χ⁻¹ * completedLFunction χ 2) * hpow
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hC
  · linear_combination h

/-- **`|ε(χ)| = 1` for primitive `χ`.** -/
theorem norm_rootNumber {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : ‖rootNumber χ‖ = 1 := by
  have h := rootNumber_mul_inv hχ
  rw [rootNumber_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖rootNumber χ‖ ^ 2 = 1 := by exact_mod_cast h
  have h0 := norm_nonneg (rootNumber χ)
  nlinarith [sq_nonneg (‖rootNumber χ‖ - 1)]

/-! ### The factor of the functional equation -/

/-- `|sin z| ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2, Complex.norm_I, mul_one]
  have e1 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [e1, e2]; linarith

/-- `|Γ(σ + it)sin(π(σ + it)/2)| ≤ 3(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2` (round 517's
`Subconvexity.norm_Gamma_mul_le_of`, as its `norm_Gamma_mul_cos_le`). -/
theorem norm_Gamma_mul_sin_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖Complex.Gamma (σ + t * I) * Complex.sin (Real.pi * (σ + t * I) / 2)‖ ≤
      3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
  refine Subconvexity.norm_Gamma_mul_le_of hσ t ((norm_sin_le_exp _).trans (le_of_eq ?_))
  congr 1
  have : ((Real.pi : ℂ) * (σ + t * I) / 2).im = Real.pi * t / 2 := by simp
  rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- `|Γ_ℂ(s)·w| ≤ 6(e⁴|s|)^{σ − 1/2}` for `w = cos(πs/2)` or `sin(πs/2)`, `Re s = σ ≥ 1/2`. -/
theorem norm_Gammaℂ_mul_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) {w : ℂ}
    (hw : ‖Complex.Gamma (σ + t * I) * w‖ ≤ 3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2)) :
    ‖Gammaℂ (σ + t * I) * w‖ ≤ 6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-((σ : ℂ) + t * I))‖ ≤ 1 := by
    have e : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have : (-((σ : ℂ) + t * I)).re = -σ := by simp
    rw [this]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  rw [Gammaℂ_def]
  have e : 2 * (2 * (Real.pi : ℂ)) ^ (-((σ : ℂ) + t * I)) * Complex.Gamma (σ + t * I) * w
      = 2 * (2 * (Real.pi : ℂ)) ^ (-((σ : ℂ) + t * I)) * (Complex.Gamma (σ + t * I) * w) := by ring
  rw [e, norm_mul, norm_mul, Complex.norm_two]
  calc 2 * ‖(2 * (Real.pi : ℂ)) ^ (-((σ : ℂ) + t * I))‖ * ‖Complex.Gamma (σ + t * I) * w‖
      ≤ 2 * 1 * (3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2)) := by gcongr
    _ = 6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by ring

/-- **The left line from the right one, for `L(s, χ)`**: for primitive `χ` mod `N` and `1/2 ≤ σ < 1`,
`|L(1 − σ − it, χ)| ≤ 6N^{σ−1/2}(e⁴|σ + it|)^{σ−1/2}|L(σ + it, χ⁻¹)|`: Mathlib's functional equation
`IsPrimitive.completedLFunction_one_sub`, with `|ε(χ)| = 1` and Mathlib's `inv_Gammaℝ_one_sub` and
`inv_Gammaℝ_two_sub`. -/
theorem norm_LFunction_one_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hσ1 : σ < 1) (t : ℝ) :
    ‖LFunction χ (1 - (σ + t * I))‖ ≤
      6 * (N : ℝ) ^ (σ - 1 / 2) * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2)
        * ‖LFunction χ⁻¹ (σ + t * I)‖ := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpole : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have h1s0 : 1 - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hsre] at this; linarith
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  -- the completed functions
  have hL1 := LFunction_eq_completed_div_gammaFactor χ (1 - s) (Or.inl h1s0)
  have hL2 := LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inl hs0)
  have hFE := hχ.completedLFunction_one_sub s
  have hpar : gammaFactor χ⁻¹ s = gammaFactor χ s := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def, ((even_inv_iff χ).2 h).gammaFactor_def]
    · rw [h.gammaFactor_def, ((odd_inv_iff χ).2 h).gammaFactor_def]
  have hNs : ‖(N : ℂ) ^ (s - 1 / 2)‖ = (N : ℝ) ^ (σ - 1 / 2) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
    congr 1; simp [hsre]
  -- the ratio of Gamma factors
  have hratio : ‖gammaFactor χ s / gammaFactor χ (1 - s)‖ ≤
      6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def, h.gammaFactor_def, div_eq_mul_inv, inv_Gammaℝ_one_sub hpole]
      have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; linarith)
      have e : Gammaℝ s * (Gammaℂ s * Complex.cos (Real.pi * s / 2) * (Gammaℝ s)⁻¹)
          = Gammaℂ s * Complex.cos (Real.pi * s / 2) := by field_simp
      rw [e]
      exact norm_Gammaℂ_mul_le hσ t (Subconvexity.norm_Gamma_mul_cos_le hσ t)
    · rw [h.gammaFactor_def, h.gammaFactor_def, show 1 - s + 1 = 2 - s by ring, div_eq_mul_inv,
        inv_Gammaℝ_two_sub hpole]
      have hG : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hsre]; linarith)
      have e : Gammaℝ (s + 1) * (Gammaℂ s * Complex.sin (Real.pi * s / 2) * (Gammaℝ (s + 1))⁻¹)
          = Gammaℂ s * Complex.sin (Real.pi * s / 2) := by field_simp
      rw [e]
      exact norm_Gammaℂ_mul_le hσ t (norm_Gamma_mul_sin_le hσ t)
  -- assemble
  have hgf : gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; linarith)
    · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp [hsre]; linarith)
  have hC2 : completedLFunction χ⁻¹ s = gammaFactor χ s * LFunction χ⁻¹ s := by
    rw [hL2, hpar]; field_simp
  have hmain : LFunction χ (1 - s) = (N : ℂ) ^ (s - 1 / 2) * rootNumber χ
      * (gammaFactor χ s / gammaFactor χ (1 - s)) * LFunction χ⁻¹ s := by
    rw [hL1, hFE, hC2]; ring
  rw [hmain, norm_mul, norm_mul, norm_mul, hNs, norm_rootNumber hχ, mul_one]
  have hLn := norm_nonneg (LFunction χ⁻¹ s)
  have hNn : 0 ≤ (N : ℝ) ^ (σ - 1 / 2) := by positivity
  calc (N : ℝ) ^ (σ - 1 / 2) * ‖gammaFactor χ s / gammaFactor χ (1 - s)‖ * ‖LFunction χ⁻¹ s‖
      ≤ (N : ℝ) ^ (σ - 1 / 2) * (6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2))
          * ‖LFunction χ⁻¹ s‖ := by gcongr
    _ = 6 * (N : ℝ) ^ (σ - 1 / 2) * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2)
          * ‖LFunction χ⁻¹ s‖ := by ring

end LinnikFE

#print axioms LinnikFE.rootNumber_inv
#print axioms LinnikFE.rootNumber_mul_inv
#print axioms LinnikFE.norm_rootNumber
#print axioms LinnikFE.norm_Gamma_mul_sin_le
#print axioms LinnikFE.norm_LFunction_one_sub_le
