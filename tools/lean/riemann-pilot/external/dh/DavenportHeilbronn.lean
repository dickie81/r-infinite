import Mathlib
import WeilChi

/-! # Davenport–Heilbronn in Lean, stage 1 (round 253)

Round 165 computed the Weil form of the Davenport–Heilbronn function numerically and certified
`λ₁ < 0` at `2a = 3.45, 3.6, 4.0` in ball arithmetic, outside Lean. This file puts the function itself
into Lean, on Mathlib's Dirichlet L-functions.

**For any primitive `χ ≠ 1` mod `N`.** Mathlib's functional equation
`Λ(1 − s, χ) = N^{s − ½} ε_χ Λ(s, χ⁻¹)` applied twice at `s = 2`, where `Λ(2, χ) ≠ 0`, gives
`ε_χ ε_{χ⁻¹} = 1` (`rootNumber_mul_rootNumber_inv`). The combination
`DH_χ(s) = (1 + ε_{χ⁻¹}) L(s, χ) + (1 + ε_χ) L(s, χ⁻¹)` (`dhL`) has the self-dual completion
`Λ_{DH}` (`dhLam`) with `Λ_{DH}(1 − s) = Λ_{DH}(s)` (`dhLam_one_sub`); `Ξ_{DH}(t) = Λ_{DH}(½ + it)` is
even and entire (`XiDH_even`, `differentiable_XiDH`); for odd `χ`, `Λ_{DH} = N^{s/2} Γ_ℝ(s + 1) DH_χ`
on `Re s > 0` (`dhLam_eq`). Along the real axis `DH_χ(x) → 2 + ε_χ + ε_{χ⁻¹} = (1 + ε_χ)²/ε_χ`
(`dhL_tendsto`), so `DH_χ ≢ 0` as soon as `ε_χ ≠ −1` (`dhL_ne_zero`).

**The character.** `chi5 : DirichletCharacter ℂ 5` with `χ(2) = i`, built from a `ℤ[i]`-valued table so
multiplicativity is decidable; `chi5_ne_one`, `chi5_odd`, `chi5_isPrimitive`. Its Gauss sum has real
part `−2 sin(π/5) < 0` (`gaussSum_chi5_re`), so its root number is not `−1`
(`rootNumber_chi5_ne_neg_one`).

**The function.** `dh := dhL chi5` is the Davenport–Heilbronn function up to a positive real factor:
with `ε_χ = e^{iθ}`, `1 + ε̄_χ = 2 cos(θ/2) e^{−iθ/2}`, so `dh = 4 cos²(θ/2)·[((1 − iκ)/2) L(s, χ) +
((1 + iκ)/2) L(s, χ̄)]` with `κ = tan(θ/2)`; the identity with round 165's closed form of `κ` is
numerical and not needed. `dh ≢ 0`, `Λ_{dh}(1 − s) = Λ_{dh}(s)`, `Ξ_{dh}` even and entire, zeros
symmetric under `s ↦ 1 − s` in the strip `0 < Re s < 1` (`dh_ne_zero`, `dh_functional_equation`, `XiDH_chi5_even`,
`dh_zero_symm`).

**Not here.** Conjugation symmetry (`ε_{χ⁻¹} = conj ε_χ`, a Gauss-sum identity); the growth bound and
Hadamard product of `Ξ_{dh}` (round 225's chain is stated for quadratic `χ`); the explicit formula
(the prime side is the Dirichlet series of `−dh′/dh`, no Euler product, and `dh` has zeros with
`Re s > 1`); and the certificate itself. See the README, round 253.
-/

open Real Complex DirichletCharacter Filter Topology

noncomputable section

namespace PsiOmega

open Pilot1ca Pilot1bt

/-! ## A Dirichlet character mod 5 with `χ(2) = i` -/

/-- Integer-valued model of the character: values in the Gaussian integers `ℤ[i]`,
where multiplicativity is decidable. -/
def chi5Gauss (a : ZMod 5) : GaussianInt :=
  match a with
  | 0 => 0
  | 1 => 1
  | 2 => ⟨0, 1⟩
  | 3 => ⟨0, -1⟩
  | 4 => -1

theorem chi5Gauss_mul : ∀ a b : ZMod 5, chi5Gauss (a * b) = chi5Gauss a * chi5Gauss b := by
  decide

theorem zmod5_mul_cube : ∀ a : ZMod 5, a ≠ 0 → a * (a * (a * a)) = 1 := by
  decide

/-- The Dirichlet character mod 5 sending `2 ↦ i`, `3 ↦ -i`, `4 ↦ -1`. -/
def chi5 : DirichletCharacter ℂ 5 where
  toFun a := GaussianInt.toComplex (chi5Gauss a)
  map_one' := by
    show GaussianInt.toComplex (chi5Gauss 1) = 1
    rw [show chi5Gauss 1 = 1 from rfl, map_one]
  map_mul' a b := by
    show GaussianInt.toComplex (chi5Gauss (a * b)) =
      GaussianInt.toComplex (chi5Gauss a) * GaussianInt.toComplex (chi5Gauss b)
    rw [chi5Gauss_mul, map_mul]
  map_nonunit' a ha := by
    show GaussianInt.toComplex (chi5Gauss a) = 0
    by_cases h0 : a = 0
    · subst h0
      rw [show chi5Gauss 0 = 0 from rfl, map_zero]
    · exact absurd (IsUnit.of_mul_eq_one _ (zmod5_mul_cube a h0)) ha

@[simp] theorem chi5_apply_zero : chi5 (0 : ZMod 5) = 0 := by
  show GaussianInt.toComplex (chi5Gauss 0) = 0
  rw [show chi5Gauss 0 = 0 from rfl, map_zero]

@[simp] theorem chi5_apply_one : chi5 (1 : ZMod 5) = 1 := by
  show GaussianInt.toComplex (chi5Gauss 1) = 1
  rw [show chi5Gauss 1 = 1 from rfl, map_one]

@[simp] theorem chi5_apply_two : chi5 (2 : ZMod 5) = I := by
  show GaussianInt.toComplex (chi5Gauss 2) = I
  rw [show chi5Gauss 2 = ⟨0, 1⟩ from rfl, GaussianInt.toComplex_def']
  simp

@[simp] theorem chi5_apply_three : chi5 (3 : ZMod 5) = -I := by
  show GaussianInt.toComplex (chi5Gauss 3) = -I
  rw [show chi5Gauss 3 = ⟨0, -1⟩ from rfl, GaussianInt.toComplex_def']
  simp

@[simp] theorem chi5_apply_four : chi5 (4 : ZMod 5) = -1 := by
  show GaussianInt.toComplex (chi5Gauss 4) = -1
  rw [show chi5Gauss 4 = -1 from rfl, map_neg, map_one]

theorem isUnit_two_zmod5 : IsUnit (2 : ZMod 5) :=
  IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide : (2 : ZMod 5) * 3 = 1)

theorem chi5_ne_one : chi5 ≠ 1 := by
  intro h
  have h2 : chi5 (2 : ZMod 5) = (1 : DirichletCharacter ℂ 5) 2 := by rw [h]
  rw [chi5_apply_two, MulChar.one_apply isUnit_two_zmod5] at h2
  simpa using congrArg Complex.re h2

theorem zmod5_neg_one : (-1 : ZMod 5) = 4 := by decide

theorem chi5_odd : chi5.Odd := by
  show chi5 (-1) = -1
  rw [zmod5_neg_one, chi5_apply_four]

theorem chi5_isPrimitive : chi5.IsPrimitive := isPrimitive_of_prime_level Nat.prime_five chi5_ne_one

theorem chi5_inv_apply (a : ZMod 5) : chi5⁻¹ a = (starRingEnd ℂ) (chi5 a) := by
  rw [← MulChar.star_apply']
  rfl

theorem chi5_inv_ne_one : chi5⁻¹ ≠ 1 := fun h => chi5_ne_one (inv_eq_one.mp h)

theorem chi5_inv_odd : chi5⁻¹.Odd := by
  show chi5⁻¹ (-1) = -1
  rw [chi5_inv_apply, zmod5_neg_one, chi5_apply_four, map_neg, map_one]

theorem chi5_inv_isPrimitive : chi5⁻¹.IsPrimitive := by
  show conductor chi5⁻¹ = 5
  rw [conductor_inv]
  exact chi5_isPrimitive

/-! ## The Gauss sum -/

theorem zmod5_univ : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide

theorem stdAddChar_zmod5_one :
    ZMod.stdAddChar (1 : ZMod 5) = exp (2 * π * I / 5) := by
  simpa using ZMod.stdAddChar_coe (N := 5) 1

theorem stdAddChar_zmod5_two :
    ZMod.stdAddChar (2 : ZMod 5) = exp (2 * π * I * 2 / 5) := by
  simpa using ZMod.stdAddChar_coe (N := 5) 2

theorem stdAddChar_zmod5_three :
    ZMod.stdAddChar (3 : ZMod 5) = exp (2 * π * I * 3 / 5) := by
  simpa using ZMod.stdAddChar_coe (N := 5) 3

theorem stdAddChar_zmod5_four :
    ZMod.stdAddChar (4 : ZMod 5) = exp (2 * π * I * 4 / 5) := by
  simpa using ZMod.stdAddChar_coe (N := 5) 4

theorem gaussSum_chi5 :
    gaussSum chi5 ZMod.stdAddChar =
      exp (2 * π * I / 5) + I * exp (2 * π * I * 2 / 5)
        - I * exp (2 * π * I * 3 / 5) - exp (2 * π * I * 4 / 5) := by
  rw [gaussSum, zmod5_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [chi5_apply_zero, chi5_apply_one, chi5_apply_two, chi5_apply_three, chi5_apply_four,
    stdAddChar_zmod5_one, stdAddChar_zmod5_two, stdAddChar_zmod5_three, stdAddChar_zmod5_four]
  ring

theorem gaussSum_chi5_re :
    (gaussSum chi5 ZMod.stdAddChar).re = -2 * Real.sin (π / 5) := by
  have e1 : exp (2 * π * I / 5) = exp (((2 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e2 : exp (2 * π * I * 2 / 5) = exp (((4 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e3 : exp (2 * π * I * 3 / 5) = exp (((6 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e4 : exp (2 * π * I * 4 / 5) = exp (((8 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have c8 : Real.cos (8 * π / 5) = Real.cos (2 * π / 5) := by
    rw [show 8 * π / 5 = 2 * π - 2 * π / 5 by ring, Real.cos_two_pi_sub]
  have s4 : Real.sin (4 * π / 5) = Real.sin (π / 5) := by
    rw [show 4 * π / 5 = π - π / 5 by ring, Real.sin_pi_sub]
  have s6 : Real.sin (6 * π / 5) = -Real.sin (π / 5) := by
    rw [show 6 * π / 5 = π / 5 + π by ring, Real.sin_add_pi]
  rw [gaussSum_chi5, e1, e2, e3, e4]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [c8, s4, s6]
  ring

/-! ## The root number -/

theorem cpow_five_half : (5 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
  push_cast
  rfl

theorem rootNumber_chi5_ne_neg_one : rootNumber chi5 ≠ -1 := by
  intro h
  rw [rootNumber, ite_eq_right chi5_odd.not_even, pow_one, Nat.cast_ofNat, cpow_five_half] at h
  have hs : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  rw [div_div, div_eq_iff (mul_ne_zero I_ne_zero hs)] at h
  have hre := congrArg Complex.re h
  have hzero : (-1 * (I * ((Real.sqrt 5 : ℝ) : ℂ))).re = 0 := by simp
  rw [hzero, gaussSum_chi5_re] at hre
  have hpos : 0 < Real.sin (π / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  linarith

theorem one_add_rootNumber_chi5_ne_zero : 1 + rootNumber chi5 ≠ 0 := by
  intro h
  exact rootNumber_chi5_ne_neg_one (by linear_combination h)

/-! ## The Davenport–Heilbronn combination of a primitive character -/

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
theorem isPrimitive_inv (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  unfold IsPrimitive at *; rw [conductor_inv]; exact hprim

omit [NeZero N] in
theorem odd_inv (hodd : χ.Odd) : χ⁻¹.Odd := by
  show χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', hodd]; norm_num

theorem completedLFunction_two_ne_zero (hχ : χ ≠ 1) : completedLFunction χ 2 ≠ 0 := by
  intro h0
  have h := LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero)
  rw [h0, zero_div] at h
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num) h

/-- **The root numbers of `χ` and `χ⁻¹` are inverse**: the functional equation applied twice at
`s = 2`, where `Λ(2, χ) ≠ 0`. -/
theorem rootNumber_mul_rootNumber_inv (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    rootNumber χ * rootNumber χ⁻¹ = 1 := by
  have hprim' := isPrimitive_inv χ hprim
  have h1 := hprim.completedLFunction_one_sub (1 - 2)
  have h2 := hprim'.completedLFunction_one_sub 2
  rw [inv_inv] at h2
  rw [h2, show (1 : ℂ) - (1 - 2) = 2 by ring] at h1
  have hpow : (N : ℂ) ^ ((1 : ℂ) - 2 - 1 / 2) * (N : ℂ) ^ ((2 : ℂ) - 1 / 2) = 1 := by
    rw [← cpow_add _ _ natCast_ne_zero']; norm_num
  have hL := completedLFunction_two_ne_zero χ hχ
  have : completedLFunction χ 2 * (rootNumber χ * rootNumber χ⁻¹ - 1) = 0 := by
    linear_combination (-1 : ℂ) * h1
      - (rootNumber χ * rootNumber χ⁻¹ * completedLFunction χ 2) * hpow
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hL)

/-- The Davenport–Heilbronn combination `(1 + ε')L(s, χ) + (1 + ε)L(s, χ⁻¹)`, `ε, ε'` the root
numbers of `χ, χ⁻¹`. -/
def dhL (s : ℂ) : ℂ :=
  (1 + rootNumber χ⁻¹) * LFunction χ s + (1 + rootNumber χ) * LFunction χ⁻¹ s

/-- Its completion `(1 + ε')Λ*(s, χ) + (1 + ε)Λ*(s, χ⁻¹)`, `Λ* = N^{s/2}Λ`. -/
def dhLam (s : ℂ) : ℂ :=
  (1 + rootNumber χ⁻¹) * LamG χ s + (1 + rootNumber χ) * LamG χ⁻¹ s

/-- `Ξ_{DH}(t) = Λ_{DH}(½ + it)`. -/
def XiDH (t : ℂ) : ℂ := dhLam χ (1 / 2 + I * t)

/-- **The functional equation `Λ_{DH}(1 − s) = Λ_{DH}(s)`**, from Mathlib's functional equation for
`χ` and `χ⁻¹` and `εε' = 1`. -/
theorem dhLam_one_sub (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    dhLam χ (1 - s) = dhLam χ s := by
  have hprim' := isPrimitive_inv χ hprim
  have heps := rootNumber_mul_rootNumber_inv χ hχ hprim
  have h1 := hprim.completedLFunction_one_sub s
  have h2 := hprim'.completedLFunction_one_sub s
  rw [inv_inv] at h2
  have e : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ natCast_ne_zero']; congr 1; ring
  unfold dhLam LamG
  rw [h1, h2]
  linear_combination ((rootNumber χ + rootNumber χ * rootNumber χ⁻¹) * completedLFunction χ⁻¹ s
      + (rootNumber χ⁻¹ + rootNumber χ * rootNumber χ⁻¹) * completedLFunction χ s) * e
    + ((N : ℂ) ^ (s / 2) * (completedLFunction χ s + completedLFunction χ⁻¹ s)) * heps

theorem XiDH_even (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℂ) : XiDH χ (-t) = XiDH χ t := by
  have := dhLam_one_sub χ hχ hprim (1 / 2 + I * t)
  rw [show (1 : ℂ) - (1 / 2 + I * t) = 1 / 2 + I * (-t) by ring] at this
  exact this

theorem differentiable_dhLam (hχ : χ ≠ 1) : Differentiable ℂ (dhLam χ) :=
  ((differentiable_LamG hχ).const_mul _).add ((differentiable_LamG (inv_ne_one.2 hχ)).const_mul _)

theorem differentiable_dhL (hχ : χ ≠ 1) : Differentiable ℂ (dhL χ) :=
  ((differentiable_LFunction hχ).const_mul _).add
    ((differentiable_LFunction (inv_ne_one.2 hχ)).const_mul _)

theorem differentiable_XiDH (hχ : χ ≠ 1) : Differentiable ℂ (XiDH χ) :=
  (differentiable_dhLam χ hχ).comp ((differentiable_id.const_mul I).const_add (1 / 2))

/-- **`Λ_{DH} = N^{s/2} Γ_ℝ(s + 1) · DH`** on `Re s > 0` for odd `χ`. -/
theorem dhLam_eq (hodd : χ.Odd) {s : ℂ} (hs : 0 < s.re) :
    dhLam χ s = (N : ℂ) ^ (s / 2) * Gammaℝ (s + 1) * dhL χ s := by
  have hodd' := odd_inv χ hodd
  unfold dhLam LamG dhL
  rw [completed_eq_mul hs, completed_eq_mul hs, hodd.gammaFactor_def, hodd'.gammaFactor_def]
  ring

/-- Zeros of `Λ_{DH}` are symmetric under `s ↦ 1 − s`. -/
theorem dhLam_one_sub_eq_zero_iff (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    dhLam χ (1 - s) = 0 ↔ dhLam χ s = 0 := by rw [dhLam_one_sub χ hχ hprim]

/-- On `Re s > 0` the zeros of `DH` are those of `Λ_{DH}`. -/
theorem dhL_eq_zero_iff (hodd : χ.Odd) {s : ℂ} (hs : 0 < s.re) :
    dhL χ s = 0 ↔ dhLam χ s = 0 := by
  rw [dhLam_eq χ hodd hs]
  have h1 : (N : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => natCast_ne_zero' h.1
  have h2 : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (mul_ne_zero h1 h2)
    · exact h'

/-! ## Nondegeneracy: `DH(x) → 2 + ε + ε'` as `x → ∞` -/

omit [NeZero N] in
theorem abscissa_chi_lt_top : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ :=
  lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun _ _ => norm_le_one (χ := χ) _⟩)
    (EReal.coe_lt_top 1)

theorem LFunction_tendsto : Tendsto (fun x : ℝ => LFunction χ x) atTop (𝓝 1) := by
  have h := LSeries.tendsto_atTop (abscissa_chi_lt_top χ)
  simp only [Nat.cast_one, map_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [LFunction_eq_LSeries χ (by simpa using hx)]

theorem dhL_tendsto :
    Tendsto (fun x : ℝ => dhL χ x) atTop (𝓝 (2 + rootNumber χ + rootNumber χ⁻¹)) := by
  have h1 := (LFunction_tendsto χ).const_mul (1 + rootNumber χ⁻¹)
  have h2 := (LFunction_tendsto χ⁻¹).const_mul (1 + rootNumber χ)
  have h := h1.add h2
  simp only [mul_one] at h
  convert h using 2
  · rfl
  · ring

theorem two_add_rootNumber_ne_zero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (h : 1 + rootNumber χ ≠ 0) : 2 + rootNumber χ + rootNumber χ⁻¹ ≠ 0 := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ hprim
  intro h0
  have : (1 + rootNumber χ) ^ 2 = 0 := by linear_combination rootNumber χ * h0 - heps
  exact h (pow_eq_zero_iff (two_ne_zero) |>.1 this)

/-- **`DH` is not identically zero** when `ε ≠ −1`: its limit along the real axis is
`2 + ε + ε' = (1 + ε)²/ε`. -/
theorem dhL_ne_zero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (h : 1 + rootNumber χ ≠ 0) :
    dhL χ ≠ 0 := by
  intro h0
  have ht := dhL_tendsto χ
  rw [h0] at ht
  simp only [Pi.zero_apply] at ht
  exact two_add_rootNumber_ne_zero χ hχ hprim h (tendsto_nhds_unique ht tendsto_const_nhds)

/-! ## The Davenport–Heilbronn function -/

/-- **The Davenport–Heilbronn function** `dh = (1 + ε')L(s, χ₅) + (1 + ε)L(s, χ₅⁻¹)`, the classical
function up to a positive real factor. -/
def dh : ℂ → ℂ := dhL chi5

theorem differentiable_dh : Differentiable ℂ dh := differentiable_dhL chi5 chi5_ne_one

/-- **`dh` is not identically zero.** -/
theorem dh_ne_zero : dh ≠ 0 :=
  dhL_ne_zero chi5 chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero

/-- **The functional equation** `Λ_{dh}(1 − s) = Λ_{dh}(s)`. -/
theorem dh_functional_equation (s : ℂ) : dhLam chi5 (1 - s) = dhLam chi5 s :=
  dhLam_one_sub chi5 chi5_ne_one chi5_isPrimitive s

theorem XiDH_chi5_even (t : ℂ) : XiDH chi5 (-t) = XiDH chi5 t :=
  XiDH_even chi5 chi5_ne_one chi5_isPrimitive t

theorem differentiable_XiDH_chi5 : Differentiable ℂ (XiDH chi5) :=
  differentiable_XiDH chi5 chi5_ne_one

theorem dh_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : dh s = 0 ↔ dhLam chi5 s = 0 :=
  dhL_eq_zero_iff chi5 chi5_odd hs

/-- **Zeros of `dh` in the strip are symmetric under `s ↦ 1 − s`.** -/
theorem dh_zero_symm {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) : dh (1 - s) = 0 ↔ dh s = 0 := by
  have h1 : 0 < (1 - s).re := by simp; linarith
  rw [dh_eq_zero_iff h1, dh_eq_zero_iff hs, dh_functional_equation]

theorem dh_tendsto :
    Tendsto (fun x : ℝ => dh x) atTop (𝓝 (2 + rootNumber chi5 + rootNumber chi5⁻¹)) :=
  dhL_tendsto chi5

end PsiOmega

#print axioms PsiOmega.rootNumber_mul_rootNumber_inv
#print axioms PsiOmega.dhLam_one_sub
#print axioms PsiOmega.XiDH_even
#print axioms PsiOmega.dhLam_eq
#print axioms PsiOmega.dhL_ne_zero
#print axioms PsiOmega.chi5_isPrimitive
#print axioms PsiOmega.chi5_odd
#print axioms PsiOmega.gaussSum_chi5_re
#print axioms PsiOmega.rootNumber_chi5_ne_neg_one
#print axioms PsiOmega.dh_ne_zero
#print axioms PsiOmega.dh_functional_equation
#print axioms PsiOmega.dh_zero_symm
