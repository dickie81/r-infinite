import Mathlib
import RealDirichlet

/-! # Prime races mod 3, 4 and 8, unconditionally (rounds 223–224)

`χ₋₃`, `χ₋₄` and `χ₋₈` are primitive and quadratic, and their partial sums are nonnegative
(`sum_chi3`, `sum_chi4`, `sum_chi8`: periodic with values `{0, 1}`, `{0, 1}`, `{0, 1, 2}`). So
`RealDirichlet.psiChi_omega_of_sums_nonneg` applies with no hypotheses: for every `0 < θ < ½` the
`log p`-weighted race changes lead infinitely often, by more than `c·x^θ` each way.
* `race_three_half`: `ψ(x; 3, 1) − ψ(x; 3, 2)`.
* `race_four_half`: `ψ(x; 4, 1) − ψ(x; 4, 3)`.
* `race_eight_half`: `ψ(x; 8, 1) + ψ(x; 8, 3) − ψ(x; 8, 5) − ψ(x; 8, 7)`.
* `hadamard_chi4`: the Hadamard product for `L(s, χ₄)`.

`χ₈` (values `1, −1, −1, 1` on `1, 3, 5, 7`) is excluded: its partial sums reach `−1`.

No bearing on RH. -/

open Real Complex Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open DirichletCharacter

theorem summ_nonneg_of_sum {g : ℕ → ℝ} (h : ∀ n, 0 ≤ ∑ k ∈ Finset.Icc 1 n, g k) (x : ℝ) :
    0 ≤ summ g x := h _

/-! ## Mod 4: `χ₋₄` -/

theorem chi4_isQuadratic : chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp _

theorem chi4_isPrimitive : chi4.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi4
  have hle : conductor chi4 ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 1 ≤ conductor chi4 := Nat.pos_of_ne_zero (conductor_ne_zero chi4)
  interval_cases h : conductor chi4
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) chi4_ne_one
  · exfalso
    have hf := factorsThrough_conductor chi4
    rw [h] at hf
    have e := congrArg (fun χ : DirichletCharacter ℂ 4 => χ ((3 : ℤ) : ZMod 4)) hf.eq_changeLevel
    rw [changeLevel_eq_cast_of_dvd' _ _ (by norm_num : IsCoprime (3 : ℤ) (4 : ℕ))] at e
    rw [show ((3 : ℤ) : ZMod 2) = 1 by decide, map_one] at e
    have : chi4 ((3 : ℤ) : ZMod 4) = -1 := by
      rw [show ((3 : ℤ) : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide, chi4_nat,
        ZMod.χ₄_nat_eq_if_mod_four]; norm_num
    rw [this] at e; norm_num at e
  · exact absurd hd (by decide)
  · rfl

theorem sum_chi4 (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, cR chi4 k = if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, cR, chi4_nat, ZMod.χ₄_nat_eq_if_mod_four]
    have e1 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
    have e2 : (n + 1) % 2 = (n % 4 + 1) % 2 := by omega
    rw [e1, e2]
    have h4 := Nat.mod_lt n (show 0 < 4 by norm_num)
    interval_cases n % 4 <;> norm_num

/-- **The race mod 4.** For every `0 < θ < ½` and `c`, `ψ(x; 4, 1) − ψ(x; 4, 3)` exceeds `c·x^θ`
and falls below `−c·x^θ` at arbitrarily large `x`. -/
theorem race_four_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < psiAP 4 1 x - psiAP 4 3 x) ∧
      (∃ x, X < x ∧ psiAP 4 1 x - psiAP 4 3 x < -(c * x ^ θ)) := by
  simpa only [summ_fχ_chi4] using psiChi_omega_of_sums_nonneg chi4_ne_one chi4_isQuadratic
    chi4_isPrimitive (summ_nonneg_of_sum fun n => by rw [sum_chi4]; split_ifs <;> norm_num)
    hθ hθ2 c X

/-- **The Hadamard product for `L(s, χ₄)`**, the first input of a Weil-positivity chain for
`χ₄`: `L(½, χ₄) > 0` supplies `f(0) ≠ 0`. -/
theorem hadamard_chi4 : Pilot1ca.HadamardW (fG chi4) (fun i : Pilot1ca.ZeroIdx (Pilot1ca.sqF (fG chi4)) => i.1⁻¹) :=
  hadamard_fG chi4_ne_one chi4_isQuadratic chi4_isPrimitive (by
    simpa using LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic
      (summ_nonneg_of_sum fun n => by rw [sum_chi4]; split_ifs <;> norm_num) (σ := 1 / 2) (by norm_num))

/-! ## Mod 3: `χ₋₃` -/

/-- The character mod 3 of `ℚ(√−3)`: `1 ↦ 1`, `2 ↦ −1`. -/
@[simps]
def χ₃ : MulChar (ZMod 3) ℤ where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

theorem isQuadratic_χ₃ : χ₃.IsQuadratic := by unfold MulChar.IsQuadratic; decide

theorem χ₃_nat (n : ℕ) : χ₃ n = if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  have help : ∀ m : ℕ, m < 3 → χ₃ m = if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 := by
    decide
  rw [← ZMod.natCast_mod n 3, help _ (Nat.mod_lt _ (by norm_num)), Nat.mod_mod]

/-- `χ₋₃` as a Dirichlet character. -/
def chi3 : DirichletCharacter ℂ 3 := χ₃.ringHomComp (Int.castRingHom ℂ)

theorem chi3_nat (n : ℕ) : chi3 n = ((χ₃ n : ℤ) : ℂ) := rfl

theorem chi3_isQuadratic : chi3.IsQuadratic := isQuadratic_χ₃.comp _

theorem chi3_ne_one : chi3 ≠ 1 := fun h => by
  have h2 : IsUnit ((2 : ℕ) : ZMod 3) := by
    rw [← ZMod.coe_unitOfCoprime 2 (by norm_num : Nat.Coprime 2 3)]; exact Units.isUnit _
  have := congrArg (fun χ : DirichletCharacter ℂ 3 => χ (2 : ℕ)) h
  simp only [MulChar.one_apply h2, chi3_nat, χ₃_nat] at this
  norm_num at this

theorem chi3_isPrimitive : chi3.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi3
  have hle : conductor chi3 ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 1 ≤ conductor chi3 := Nat.pos_of_ne_zero (conductor_ne_zero chi3)
  interval_cases h : conductor chi3
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) chi3_ne_one
  · exact absurd hd (by decide)
  · rfl

theorem sum_chi3 (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cR chi3 k = if n % 3 = 1 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, cR, chi3_nat, χ₃_nat]
    have e1 : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
    rw [e1]
    have h3 := Nat.mod_lt n (show 0 < 3 by norm_num)
    interval_cases n % 3 <;> norm_num

theorem summ_fχ_chi3 (x : ℝ) : summ (fχ chi3) x = psiAP 3 1 x - psiAP 3 2 x := by
  unfold summ psiAP
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fχ, chi3_nat, χ₃_nat]
  have h3 := Nat.mod_lt k (show 0 < 3 by norm_num)
  interval_cases hk : k % 3 <;> simp_all

/-- **The race mod 3.** For every `0 < θ < ½` and `c`, `ψ(x; 3, 1) − ψ(x; 3, 2)` exceeds `c·x^θ`
and falls below `−c·x^θ` at arbitrarily large `x`. -/
theorem race_three_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < psiAP 3 1 x - psiAP 3 2 x) ∧
      (∃ x, X < x ∧ psiAP 3 1 x - psiAP 3 2 x < -(c * x ^ θ)) := by
  simpa only [summ_fχ_chi3] using psiChi_omega_of_sums_nonneg chi3_ne_one chi3_isQuadratic
    chi3_isPrimitive (summ_nonneg_of_sum fun n => by rw [sum_chi3]; split_ifs <;> norm_num)
    hθ hθ2 c X

/-! ## Mod 8: `χ₋₈ = χ₈'` -/

/-- `χ₋₈` (Mathlib's `χ₈'`): `1, 3 ↦ 1`, `5, 7 ↦ −1`. -/
def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

theorem chi8_nat (n : ℕ) : chi8 n = ((ZMod.χ₈' n : ℤ) : ℂ) := rfl

theorem chi8_isQuadratic : chi8.IsQuadratic := ZMod.isQuadratic_χ₈'.comp _

theorem chi8_five : chi8 ((5 : ℤ) : ZMod 8) = -1 := by
  rw [show ((5 : ℤ) : ZMod 8) = ((5 : ℕ) : ZMod 8) by decide, chi8_nat,
    ZMod.χ₈'_nat_eq_if_mod_eight]; norm_num

theorem chi8_ne_one : chi8 ≠ 1 := fun h => by
  have h5 : IsUnit ((5 : ℤ) : ZMod 8) := by
    rw [show ((5 : ℤ) : ZMod 8) = ((5 : ℕ) : ZMod 8) by decide,
      ← ZMod.coe_unitOfCoprime 5 (by norm_num : Nat.Coprime 5 8)]; exact Units.isUnit _
  have := chi8_five
  rw [h, MulChar.one_apply h5] at this; norm_num at this

theorem not_factorsThrough_four : ¬ FactorsThrough chi8 4 := fun hf => by
  have e := congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((5 : ℤ) : ZMod 8)) hf.eq_changeLevel
  rw [changeLevel_eq_cast_of_dvd' _ _ (by norm_num : IsCoprime (5 : ℤ) (8 : ℕ))] at e
  rw [show ((5 : ℤ) : ZMod 4) = 1 by decide, map_one] at e
  simp only [chi8_five] at e; norm_num at e

theorem chi8_isPrimitive : chi8.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi8
  have hle : conductor chi8 ≤ 8 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 1 ≤ conductor chi8 := Nat.pos_of_ne_zero (conductor_ne_zero chi8)
  have hf := factorsThrough_conductor chi8
  interval_cases h : conductor chi8
  · exact absurd (FactorsThrough.mono chi8 hf (by norm_num) (by norm_num)) not_factorsThrough_four
  · exact absurd (FactorsThrough.mono chi8 hf (by norm_num) (by norm_num)) not_factorsThrough_four
  · exact absurd hd (by decide)
  · exact absurd hf not_factorsThrough_four
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · rfl

theorem sum_chi8 (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cR chi8 k =
    if n % 8 = 0 ∨ n % 8 = 7 then 0 else if n % 8 = 3 ∨ n % 8 = 4 then 2 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, cR, chi8_nat, ZMod.χ₈'_nat_eq_if_mod_eight]
    have e1 : (n + 1) % 8 = (n % 8 + 1) % 8 := by omega
    have e2 : (n + 1) % 2 = (n % 8 + 1) % 2 := by omega
    rw [e1, e2]
    have h8 := Nat.mod_lt n (show 0 < 8 by norm_num)
    interval_cases n % 8 <;> norm_num

theorem summ_fχ_chi8 (x : ℝ) :
    summ (fχ chi8) x = psiAP 8 1 x + psiAP 8 3 x - (psiAP 8 5 x + psiAP 8 7 x) := by
  unfold summ psiAP
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fχ, chi8_nat, ZMod.χ₈'_nat_eq_if_mod_eight]
  have h8 := Nat.mod_lt k (show 0 < 8 by norm_num)
  have h2 : k % 2 = k % 8 % 2 := (Nat.mod_mod_of_dvd k (by norm_num)).symm
  interval_cases hk : k % 8 <;> simp_all

/-- **The race mod 8** between `{1, 3}` and `{5, 7}`: for every `0 < θ < ½` and `c`,
`ψ(x; 8, 1) + ψ(x; 8, 3) − ψ(x; 8, 5) − ψ(x; 8, 7)` exceeds `c·x^θ` and falls below `−c·x^θ` at
arbitrarily large `x`. -/
theorem race_eight_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < psiAP 8 1 x + psiAP 8 3 x - (psiAP 8 5 x + psiAP 8 7 x)) ∧
      (∃ x, X < x ∧ psiAP 8 1 x + psiAP 8 3 x - (psiAP 8 5 x + psiAP 8 7 x) < -(c * x ^ θ)) := by
  simpa only [summ_fχ_chi8] using psiChi_omega_of_sums_nonneg chi8_ne_one chi8_isQuadratic
    chi8_isPrimitive (summ_nonneg_of_sum fun n => by rw [sum_chi8]; split_ifs <;> norm_num)
    hθ hθ2 c X

end PsiOmega

#print axioms PsiOmega.race_three_half
#print axioms PsiOmega.race_four_half
#print axioms PsiOmega.race_eight_half
#print axioms PsiOmega.hadamard_chi4
