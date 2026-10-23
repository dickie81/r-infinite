import KubotaLamCube

/-! # The translation law at the cusps `γ_±` (round 460)

S5f-15 of round 360's plan, part 1. Round 361's display asks for θ's expansions at the cusps
`γ_± = (1, 0; ω^{±1}, 1)`. This round proves how θ∘γ_t transforms under the translations by `3ℤ[ω]`, for
`t = ω` and `t = ω²`, and what that says about its Fourier modes:

* **The conjugated translations** (`lowT`, `cuspPar`, definitions; `lowT_coe`, `cuspPar_coe`, `cuspPar_mem`,
  `lowT_mul_slT`, `primary_one_sub` and **`kub_cuspPar`**):
  `γ_t·T_{3x}·γ_t⁻¹ = (1 − 3tx, 3x; −3t²x, 1 + 3tx)` lies in `Γ_1(3)`, and its lower left entry is `t·(a − 1)`
  for `a = 1 − 3tx`, so Kubota's character takes the value `(t/a)₃` there.
* **The character** (`chiT`, a definition; `chiT_eq_kub`, `cuspPar_add`, `chiT_add`, `chiT_zero`, `norm_chiT`,
  `chiT_mul_conj`, `chiT_neg`, `chiT_nsmul` and `chiT_zsmul_eq_one`): `χ_t(x) = (t/(1 − 3tx))₃` is a character
  of `x ∈ ℤ[ω]` with values on the unit circle.
* **The translation law** (**`thS_lowT_add`**): `θ(γ_t(w + 3x)) = χ_t(x)·θ(γ_t w)` for θ's Fourier series.
* **The character on `λℤ[ω]` and at `1`** (`cub_omega_of_norm`, `absNorm_crd_eq`, `crd_eq`, `cub_omega_sq`,
  `chiT_lam`, **`chiT_lam_mul`** and **`chiT_one`**): through round 362's `(ω/b)₃ = ω^{(N(b)−1)/3}` at the
  elements `1 − 3tx` of norm `28`, `19`, `37` and `13`, `χ_t` is trivial on `λℤ[ω]` and `χ_t(1) = σ(t)`.
* **The class of the modes** (`ebr_third`, `ebr_neg_third`, `varpi_eq_ebr`, `ebr_one_eq_one`, `ebr_lam_mul`,
  `ebr_add_period`, `ebr_nsmul`, **`exists_cuspClass`** and **`thS_lowT_twist_add`**): there is `m₀ = ±1` with
  `ĕ(m₀·3x/9) = χ_t(x)` for every `x`, so `z ↦ θ(γ_t(z, v))·ĕ(−m₀z/9)` is periodic under `3ℤ[ω]`. The sign of
  `m₀` is fixed by whether `σ(ω)` is `ĕ(1/3)` or `ĕ(−1/3)`.
* **The conjugated character** (`kubT`, a definition; `lowT_conj_mem`, `isUChar_kubT`, `kubT_slT` and
  **`isAut_comp_lowT`**): `κ_t(γ) = κ(γ_t·γ·γ_t⁻¹)` is a unitary character on `Γ_1(3)`,
  `κ_t(T_{3x}) = χ_t(x)`, and `u∘γ_t` is automorphic with `κ_t` when `u` is automorphic with Kubota's
  character.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-! ### The cusp matrices and the conjugated translations -/

/-- The cusp matrix `γ_t = (1, 0; t, 1)`. As matrices, `γ_ω` and `γ_{ω²}` are round 361's `gamPlus` and
`gamMinus` by definition. -/
def lowT (t : 𝓞 K) : SL(2, 𝓞 K) := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

/-- `γ_t` as a matrix. -/
theorem lowT_coe (t : 𝓞 K) : (lowT t : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, 0; t, 1] := rfl

/-- The conjugated translation `γ_t·T_{3x}·γ_t⁻¹`. -/
def cuspPar (t x : 𝓞 K) : SL(2, 𝓞 K) := lowT t * slT (3 * x) * (lowT t)⁻¹

/-- `γ_t·T_{3x}·γ_t⁻¹ = (1 − 3tx, 3x; −3t²x, 1 + 3tx)`. -/
theorem cuspPar_coe (t x : 𝓞 K) : (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
    !![1 - 3 * t * x, 3 * x; -(3 * t ^ 2 * x), 1 + 3 * t * x] := by
  unfold cuspPar
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, lowT_coe, slT, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `γ_t·T_{3x}·γ_t⁻¹ ∈ Γ_1(3)` (round 382's `mem_Gam3`). -/
theorem cuspPar_mem (t x : 𝓞 K) : cuspPar t x ∈ Gam3 := by
  rw [mem_Gam3, cuspPar_coe]
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-(t * x), by simp; ring⟩
  · exact ⟨x, by simp⟩
  · exact ⟨-(t ^ 2 * x), by simp; ring⟩
  · exact ⟨t * x, by simp; ring⟩

/-- `γ_t·T_{3x} = (γ_t·T_{3x}·γ_t⁻¹)·γ_t`. -/
theorem lowT_mul_slT (t x : 𝓞 K) : lowT t * slT (3 * x) = cuspPar t x * lowT t := by
  unfold cuspPar
  group

/-- `1 − 3tx` is primary. -/
theorem primary_one_sub (t x : 𝓞 K) : Primary (1 - 3 * t * x) := ⟨-(t * x), by ring⟩

/-- **Kubota's character at `γ_t·T_{3x}·γ_t⁻¹`** (round 361's `kub`, round 369's `kub_of_ne`):
`κ = (t/(1 − 3tx))₃`. The lower left entry is `t·(a − 1)` for `a = 1 − 3tx`, and `((a − 1)/a)₃ = (−1/a)₃ = 1`
(round 362's `cub_congr`, `cub_neg` and `cub_one`); for `tx = 0` both sides are `1`. -/
theorem kub_cuspPar (t x : 𝓞 K) :
    kub (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) = σO (cub t (span {1 - 3 * t * x})) := by
  have ha := primary_one_sub t x
  have h10 : (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = -(3 * t ^ 2 * x) := by
    rw [cuspPar_coe]; simp
  have h00 : (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = 1 - 3 * t * x := by
    rw [cuspPar_coe]; simp
  by_cases h0 : (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0
  · have hk : kub (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) = 1 := by
      unfold kub
      simp only [h0, ↓reduceIte]
    rw [hk]
    rw [h10] at h0
    have htx : t * x = 0 := by
      have : (3 : 𝓞 K) * (t * (t * x)) = 0 := by linear_combination -h0
      rcases mul_eq_zero.1 this with h3 | h3
      · exfalso
        have := congrArg σO h3
        rw [map_ofNat, map_zero] at this
        norm_num at this
      · rcases mul_eq_zero.1 h3 with ht | ht
        · rw [ht, zero_mul]
        · exact ht
    rw [show (1 : 𝓞 K) - 3 * t * x = 1 by linear_combination (-3) * htx, cub_one_right, map_one]
  · rw [kub_of_ne h0, h10, h00]
    congr 1
    rw [show -(3 * t ^ 2 * x) = t * ((1 - 3 * t * x) - 1) by ring, cub_mul_left,
      cub_congr (show (1 - 3 * t * x) ∣ ((1 - 3 * t * x) - 1) - (-1) from ⟨1, by ring⟩), cub_neg ha,
      cub_one ha, mul_one]

/-- **The translation character at the cusp `γ_t`**: `χ_t(x) = (t/(1 − 3tx))₃`. -/
def chiT (t x : 𝓞 K) : ℂ := σO (cub t (span {1 - 3 * t * x}))

/-- `χ_t(x) = κ(γ_t·T_{3x}·γ_t⁻¹)`. -/
theorem chiT_eq_kub (t x : 𝓞 K) : chiT t x = kub (cuspPar t x : Matrix (Fin 2) (Fin 2) (𝓞 K)) :=
  (kub_cuspPar t x).symm

/-- `x ↦ γ_t·T_{3x}·γ_t⁻¹` is a homomorphism. -/
theorem cuspPar_add (t x y : 𝓞 K) : cuspPar t (x + y) = cuspPar t x * cuspPar t y := by
  have h : slT (3 * (x + y)) = slT (3 * x) * slT (3 * y) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [slT, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_comm]
  unfold cuspPar
  rw [h]
  group

/-- **`χ_t` is a character**: `χ_t(x + y) = χ_t(x)·χ_t(y)` (round 382's `kub_mul_Gam3`). -/
theorem chiT_add (t x y : 𝓞 K) : chiT t (x + y) = chiT t x * chiT t y := by
  rw [chiT_eq_kub, chiT_eq_kub, chiT_eq_kub, cuspPar_add]
  exact kub_mul_Gam3 (cuspPar_mem t x) (cuspPar_mem t y)

/-- `χ_t(0) = 1`. -/
theorem chiT_zero (t : 𝓞 K) : chiT t 0 = 1 := by
  unfold chiT
  rw [mul_zero, sub_zero, cub_one_right, map_one]

/-- `|χ_t(x)| = 1` (round 387's `norm_kub`). -/
theorem norm_chiT (t x : 𝓞 K) : ‖chiT t x‖ = 1 := by
  rw [chiT_eq_kub]
  exact norm_kub (cuspPar t x).2 (mem_Gam3.1 (cuspPar_mem t x))

/-- `χ_t(x)·conj χ_t(x) = 1`. -/
theorem chiT_mul_conj (t x : 𝓞 K) : chiT t x * conj (chiT t x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_chiT]
  norm_num

/-! ### The translation law -/

/-- **The translation law at `γ_t`**: `θ(γ_t(w + 3x)) = χ_t(x)·θ(γ_t w)` for θ's Fourier series (round
437's `isAut_thS`). -/
theorem thS_lowT_add {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (t x : 𝓞 K) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    thS r Y hY (slAct (lowT t) (z + σO (3 * x), v)) = chiT t x * thS r Y hY (slAct (lowT t) (z, v)) := by
  have hp : (z, v) ∈ UHS := hv
  have e : (z + σO (3 * x), v) = slAct (slT (3 * x)) (z, v) := by rw [slAct_slT]
  rw [e, ← slAct_mul _ _ hp, lowT_mul_slT, slAct_mul _ _ hp, chiT_eq_kub]
  exact isAut_thS hr hY _ (cuspPar_mem t x) _ (slAct_mem _ hp)

/-! ### The character on `λℤ[ω]` and at `1` -/

/-- `χ_t(−x)·χ_t(x) = 1`. -/
theorem chiT_neg (t x : 𝓞 K) : chiT t (-x) * chiT t x = 1 := by
  rw [← chiT_add, neg_add_cancel, chiT_zero]

/-- `χ_t(nx) = χ_t(x)^n` for `n ∈ ℕ`. -/
theorem chiT_nsmul (t x : 𝓞 K) (n : ℕ) : chiT t (n * x) = chiT t x ^ n := by
  induction n with
  | zero => simp [chiT_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, chiT_add, ih, pow_succ]

/-- If `χ_t(x) = 1`, then `χ_t(nx) = 1` for every `n ∈ ℤ`. -/
theorem chiT_zsmul_eq_one {t x : 𝓞 K} (hx : chiT t x = 1) (n : ℤ) : chiT t (n * x) = 1 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [Int.cast_natCast, chiT_nsmul, hx, one_pow]
  · have h := chiT_neg t ((k : 𝓞 K) * x)
    rw [chiT_nsmul, hx, one_pow, mul_one] at h
    rw [Int.cast_neg, Int.cast_natCast, neg_mul, h]

/-- Round 362's `cub_omega` at a given norm: `(ω/b)₃ = ω^{(n−1)/3}` for `N(b) = n`. -/
theorem cub_omega_of_norm {b : 𝓞 K} (hb : Primary b) {n : ℕ} (hn : absNorm (span {b}) = n) :
    cub ω (span {b}) = ω ^ ((n - 1) / 3) := by
  rw [cub_omega hb, hn]

/-- `N(a + bω) = n` from round 308's `absNorm_crd`. -/
theorem absNorm_crd_eq (a b : ℤ) {n : ℕ} (hn : ((a : ℝ) - (b : ℝ) / 2) ^ 2 + 3 / 4 * (b : ℝ) ^ 2 = n) :
    absNorm (span {crd ![a, b]}) = n := by
  have h := absNorm_crd ![a, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [hn] at h
  exact_mod_cast h

/-- `crd (a, b) = a + bω`. -/
theorem crd_eq (a b : ℤ) : crd ![a, b] = (a : 𝓞 K) + (b : 𝓞 K) * ω := by
  simp [crd]

/-- `(ω²/b)₃ = (ω/b)₃²`. -/
theorem cub_omega_sq (b : 𝓞 K) : cub (ω ^ 2) (span {b}) = cub ω (span {b}) ^ 2 := by
  rw [sq, cub_mul_left, sq]

/-- `χ_t(λ) = χ_t(ωλ) = 1` for `t = ω` and `t = ω²`: the elements `1 − 3ωλ = 4 + 6ω`, `1 − 3ω²λ = −5 − 3ω`
and `1 − 3λ = 4 − 3ω` have norms `28`, `19` and `37`, and `(28 − 1)/3`, `(19 − 1)/3` and `2·(37 − 1)/3` are
divisible by `3`. -/
theorem chiT_lam (t : 𝓞 K) (ht : t = ω ∨ t = ω ^ 2) : chiT t (ω - 1) = 1 ∧ chiT t (ω * (ω - 1)) = 1 := by
  have hω := ω_cube
  have hs := ω_sq_add
  have e1 : (1 : 𝓞 K) - 3 * ω * (ω - 1) = crd ![4, 6] := by
    rw [crd_eq]; push_cast; linear_combination (-3) * hs
  have e2 : (1 : 𝓞 K) - 3 * ω * (ω * (ω - 1)) = crd ![-5, -3] := by
    rw [crd_eq]; push_cast; linear_combination 3 * hs - 3 * hω
  have e3 : (1 : 𝓞 K) - 3 * ω ^ 2 * (ω - 1) = crd ![-5, -3] := by
    rw [crd_eq]; push_cast; linear_combination 3 * hs - 3 * hω
  have e4 : (1 : 𝓞 K) - 3 * ω ^ 2 * (ω * (ω - 1)) = crd ![4, -3] := by
    rw [crd_eq]; push_cast; linear_combination (3 - 3 * ω) * hω
  have n1 : absNorm (span {crd ![(4 : ℤ), 6]}) = 28 := absNorm_crd_eq 4 6 (by norm_num)
  have n2 : absNorm (span {crd ![(-5 : ℤ), -3]}) = 19 := absNorm_crd_eq (-5) (-3) (by norm_num)
  have n4 : absNorm (span {crd ![(4 : ℤ), -3]}) = 37 := absNorm_crd_eq 4 (-3) (by norm_num)
  have p1 : Primary (crd ![(4 : ℤ), 6]) := by rw [← e1]; exact primary_one_sub _ _
  have p2 : Primary (crd ![(-5 : ℤ), -3]) := by rw [← e2]; exact primary_one_sub _ _
  have p4 : Primary (crd ![(4 : ℤ), -3]) := by rw [← e4]; exact primary_one_sub _ _
  have w9 : (ω : 𝓞 K) ^ 9 = 1 := by rw [show 9 = 3 * 3 by rfl, pow_mul, hω, one_pow]
  have w6 : (ω : 𝓞 K) ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, hω, one_pow]
  have w12 : (ω : 𝓞 K) ^ 12 = 1 := by rw [show 12 = 3 * 4 by rfl, pow_mul, hω, one_pow]
  unfold chiT
  rcases ht with rfl | rfl
  · rw [e1, e2, cub_omega_of_norm p1 n1, cub_omega_of_norm p2 n2]
    norm_num [w9, w6]
  · rw [e3, e4, cub_omega_sq, cub_omega_sq, cub_omega_of_norm p2 n2, cub_omega_of_norm p4 n4]
    norm_num [w6, w12]

/-- **`χ_t` is trivial on `λℤ[ω]`**, for `t = ω` and `t = ω²`. -/
theorem chiT_lam_mul (t : 𝓞 K) (ht : t = ω ∨ t = ω ^ 2) (y : 𝓞 K) : chiT t ((ω - 1) * y) = 1 := by
  obtain ⟨h1, h2⟩ := chiT_lam t ht
  obtain ⟨a, b, rfl⟩ := exists_coords y
  rw [show (ω - 1 : 𝓞 K) * (a + b * ω) = a * (ω - 1) + b * (ω * (ω - 1)) by ring, chiT_add,
    chiT_zsmul_eq_one h1, chiT_zsmul_eq_one h2, one_mul]

/-- `χ_t(1) = σ(t)` for `t = ω` and `t = ω²`: `N(1 − 3ω) = N(1 − 3ω²) = 13`. -/
theorem chiT_one (t : 𝓞 K) (ht : t = ω ∨ t = ω ^ 2) : chiT t 1 = σO t := by
  have hω := ω_cube
  have hs := ω_sq_add
  have e1 : (1 : 𝓞 K) - 3 * ω * 1 = crd ![1, -3] := by rw [crd_eq]; push_cast; ring
  have e2 : (1 : 𝓞 K) - 3 * ω ^ 2 * 1 = crd ![4, 3] := by
    rw [crd_eq]; push_cast; linear_combination (-3) * hs
  have n1 : absNorm (span {crd ![(1 : ℤ), -3]}) = 13 := absNorm_crd_eq 1 (-3) (by norm_num)
  have n2 : absNorm (span {crd ![(4 : ℤ), 3]}) = 13 := absNorm_crd_eq 4 3 (by norm_num)
  have p1 : Primary (crd ![(1 : ℤ), -3]) := by rw [← e1]; exact primary_one_sub _ _
  have p2 : Primary (crd ![(4 : ℤ), 3]) := by rw [← e2]; exact primary_one_sub _ _
  unfold chiT
  rcases ht with rfl | rfl
  · rw [e1, cub_omega_of_norm p1 n1, show ((13 - 1) / 3 : ℕ) = 3 + 1 by norm_num, pow_succ, hω, one_mul]
  · rw [e2, cub_omega_sq, cub_omega_of_norm p2 n2]
    congr 1
    rw [← pow_mul, show (13 - 1) / 3 * 2 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]

/-! ### The class of the modes -/

/-- `ĕ(1/3) = −1/2 − (√3/2)i`. -/
theorem ebr_third : ebr (1 / 3) = -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  unfold ebr
  have e : 2 * (Real.pi : ℂ) * Complex.I * (((2 * (1 / 3 : ℂ).re : ℝ)) : ℂ) =
      ((Real.pi / 3 + Real.pi : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.div_re, Complex.one_re, Complex.normSq_ofNat]
    push_cast
    norm_num
    ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `ĕ(−1/3) = −1/2 + (√3/2)i`. -/
theorem ebr_neg_third : ebr (-1 / 3) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  unfold ebr
  have e : 2 * (Real.pi : ℂ) * Complex.I * (((2 * (-1 / 3 : ℂ).re : ℝ)) : ℂ) =
      ((-(Real.pi / 3 + Real.pi) : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.div_re, Complex.neg_re, Complex.one_re, Complex.normSq_ofNat]
    push_cast
    norm_num
    ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `ϖ = σ(ω)` is `ĕ(1/3)` or `ĕ(−1/3)` (round 294's `varpi_re_im`). -/
theorem varpi_eq_ebr : varpi = ebr (1 / 3) ∨ varpi = ebr (-1 / 3) := by
  obtain ⟨hre, him⟩ := varpi_re_im
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h : (varpi.im + Real.sqrt 3 / 2) * (varpi.im - Real.sqrt 3 / 2) = 0 := by nlinarith
  rcases mul_eq_zero.1 h with h1 | h1
  · left
    rw [ebr_third]
    refine Complex.ext ?_ ?_
    · simp [hre]
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      norm_num
      linarith
  · right
    rw [ebr_neg_third]
    refine Complex.ext ?_ ?_
    · simp [hre]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      norm_num
      linarith

/-- `ĕ(1) = 1`. -/
theorem ebr_one_eq_one : ebr 1 = 1 := by
  unfold ebr
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((2 * (1 : ℂ).re : ℝ)) : ℂ) =
      (2 : ℤ) * (2 * Real.pi * Complex.I) by simp; ring]
  exact Complex.exp_int_mul_two_pi_mul_I 2

/-- The phase `ĕ(m₀·3x/9)` of `m₀ ∈ ℤ[ω]` is `1` at `x ∈ λℤ[ω]` (round 428's `ebr_period`). -/
theorem ebr_lam_mul (m₀ y : 𝓞 K) : ebr (σO m₀ * σO (3 * ((ω - 1) * y)) / 9) = 1 := by
  have e : σO m₀ * σO (3 * ((ω - 1) * y)) / 9 = σO (δ3 * (-ω ^ 2 * m₀ * y)) * σO (3 * 1) / 9 := by
    rw [← map_mul, ← map_mul]
    congr 2
    unfold δ3
    linear_combination (3 * m₀ * y) * ω_sq_add + (6 * m₀ * y) * ω_cube
  rw [e, ebr_period]

/-- `x ↦ ĕ(m₀·3x/9)` is a character (round 363's `ebr_add`). -/
theorem ebr_add_period (m₀ x y : 𝓞 K) :
    ebr (σO m₀ * σO (3 * (x + y)) / 9) = ebr (σO m₀ * σO (3 * x) / 9) * ebr (σO m₀ * σO (3 * y) / 9) := by
  rw [← ebr_add]
  congr 1
  simp only [map_mul, map_add]
  ring

/-- `ĕ(m₀·3nx/9) = ĕ(m₀·3x/9)^n` for `n ∈ ℕ`. -/
theorem ebr_nsmul (m₀ x : 𝓞 K) (n : ℕ) :
    ebr (σO m₀ * σO (3 * (n * x)) / 9) = ebr (σO m₀ * σO (3 * x) / 9) ^ n := by
  induction n with
  | zero => simp [ebr_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ebr_add_period, ih, pow_succ]

/-- **The class of the modes at `γ_t`**: for `t = ω` and `t = ω²` there is `m₀ = ±1` with
`ĕ(m₀·3x/9) = χ_t(x)` for every `x`. Both sides are characters of `x`, trivial on `λℤ[ω]`, so they agree once
they agree at `1`, and `χ_t(1) = σ(t)` is `ĕ(1/3)` or `ĕ(−1/3)`. -/
theorem exists_cuspClass (t : 𝓞 K) (ht : t = ω ∨ t = ω ^ 2) :
    ∃ m₀ : 𝓞 K, (m₀ = 1 ∨ m₀ = -1) ∧ ∀ x : 𝓞 K, ebr (σO m₀ * σO (3 * x) / 9) = chiT t x := by
  -- the value at `1`
  have h1 : ∃ m₀ : 𝓞 K, (m₀ = 1 ∨ m₀ = -1) ∧ ebr (σO m₀ * σO (3 * 1) / 9) = chiT t 1 := by
    rw [chiT_one t ht]
    have h3 : σO 3 = 3 := map_ofNat σO 3
    have e1 : ebr (σO 1 * σO (3 * 1) / 9) = ebr (1 / 3) := by
      congr 1; rw [mul_one, map_one, one_mul, h3]; norm_num
    have e2 : ebr (σO (-1) * σO (3 * 1) / 9) = ebr (-1 / 3) := by
      congr 1; rw [mul_one, map_neg, map_one, h3]; norm_num
    have hsq : ebr (1 / 3) ^ 2 = ebr (-1 / 3) := by
      rw [sq, ← ebr_add, show (1 / 3 + 1 / 3 : ℂ) = -1 / 3 + 1 by ring, ebr_add, ebr_one_eq_one, mul_one]
    have hcube : ebr (1 / 3) ^ 3 = 1 := by
      rw [pow_succ, hsq, ← ebr_add, show (-1 / 3 + 1 / 3 : ℂ) = 0 by ring, ebr_zero]
    have hsq' : ebr (-1 / 3) ^ 2 = ebr (1 / 3) := by
      rw [← hsq, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hcube, one_mul]
    rcases ht with rfl | rfl <;> rcases varpi_eq_ebr with hv | hv
    · exact ⟨1, Or.inl rfl, by rw [e1, σO_ω, hv]⟩
    · exact ⟨-1, Or.inr rfl, by rw [e2, σO_ω, hv]⟩
    · exact ⟨-1, Or.inr rfl, by rw [e2, map_pow, σO_ω, hv, hsq]⟩
    · exact ⟨1, Or.inl rfl, by rw [e1, map_pow, σO_ω, hv, hsq']⟩
  obtain ⟨m₀, hm₀, hv⟩ := h1
  refine ⟨m₀, hm₀, fun x => ?_⟩
  have hnat : ∀ k : ℕ, ebr (σO m₀ * σO (3 * ((k : 𝓞 K) * 1)) / 9) = chiT t ((k : 𝓞 K) * 1) := by
    intro k
    rw [ebr_nsmul, chiT_nsmul, hv]
  have key : ∀ n : ℤ, ebr (σO m₀ * σO (3 * ((n : 𝓞 K) * 1)) / 9) = chiT t ((n : 𝓞 K) * 1) := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · rw [Int.cast_natCast]
      exact hnat k
    · rw [Int.cast_neg, Int.cast_natCast, neg_mul]
      have hc := chiT_neg t ((k : 𝓞 K) * 1)
      have he : ebr (σO m₀ * σO (3 * (-((k : 𝓞 K) * 1))) / 9) *
          ebr (σO m₀ * σO (3 * ((k : 𝓞 K) * 1)) / 9) = 1 := by
        rw [← ebr_add_period, neg_add_cancel, mul_zero, map_zero, mul_zero, zero_div, ebr_zero]
      rw [hnat k] at he
      have hne : chiT t ((k : 𝓞 K) * 1) ≠ 0 := by
        intro h0
        have := norm_chiT t ((k : 𝓞 K) * 1)
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      exact mul_right_cancel₀ hne (he.trans hc.symm)
  obtain ⟨a, b, rfl⟩ := exists_coords x
  have hx : (a : 𝓞 K) + b * ω = ((a + b : ℤ) : 𝓞 K) * 1 + (ω - 1) * b := by push_cast; ring
  rw [hx, chiT_add, ebr_add_period, chiT_lam_mul t ht, ebr_lam_mul, key]

/-- **The twisted function is periodic**: for `m₀` in the class, `z ↦ θ(γ_t(z, v))·ĕ(−m₀z/9)` is periodic
under `3ℤ[ω]` (round 363's `conj_ebr`). -/
theorem thS_lowT_twist_add {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (t : 𝓞 K) {m₀ : 𝓞 K}
    (hm : ∀ x : 𝓞 K, ebr (σO m₀ * σO (3 * x) / 9) = chiT t x) (x : 𝓞 K) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    thS r Y hY (slAct (lowT t) (z + σO (3 * x), v)) * ebr (-(σO m₀ * (z + σO (3 * x))) / 9) =
      thS r Y hY (slAct (lowT t) (z, v)) * ebr (-(σO m₀ * z) / 9) := by
  rw [thS_lowT_add hr hY t x z hv, show -(σO m₀ * (z + σO (3 * x))) / 9 =
    -(σO m₀ * z) / 9 + -(σO m₀ * σO (3 * x) / 9) by ring, ebr_add, ← conj_ebr, hm]
  have h := chiT_mul_conj t x
  linear_combination (thS r Y hY (slAct (lowT t) (z, v)) * ebr (-(σO m₀ * z) / 9)) * h

/-! ### The conjugated character -/

/-- **The conjugated character** `κ_t(γ) = κ(γ_t·γ·γ_t⁻¹)`. -/
def kubT (t : 𝓞 K) (g : SL(2, 𝓞 K)) : ℂ := kub ↑(lowT t * g * (lowT t)⁻¹)

/-- `γ_t·γ·γ_t⁻¹ ∈ Γ_1(3)` for `γ ∈ Γ_1(3)` (round 382's `gam3_normal`). -/
theorem lowT_conj_mem (t : 𝓞 K) {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : lowT t * g * (lowT t)⁻¹ ∈ Gam3 :=
  gam3_normal.conj_mem g hg (lowT t)

/-- `κ_t` is a unitary character on `Γ_1(3)` (round 421's `IsUChar`). -/
theorem isUChar_kubT (t : 𝓞 K) : IsUChar Gam3 (kubT t) where
  map_mul g hg h hh := by
    unfold kubT
    rw [show lowT t * (g * h) * (lowT t)⁻¹ = (lowT t * g * (lowT t)⁻¹) * (lowT t * h * (lowT t)⁻¹) by group]
    exact kub_mul_Gam3 (lowT_conj_mem t hg) (lowT_conj_mem t hh)
  norm_eq g hg := norm_kub (lowT t * g * (lowT t)⁻¹).2 (mem_Gam3.1 (lowT_conj_mem t hg))

/-- `κ_t(T_{3x}) = χ_t(x)`. -/
theorem kubT_slT (t x : 𝓞 K) : kubT t (slT (3 * x)) = chiT t x := (chiT_eq_kub t x).symm

/-- **The translate by `γ_t` of an automorphic function**: if `u` is automorphic with Kubota's character, then
`u∘γ_t` is automorphic with `κ_t` (round 422's `IsAut`). -/
theorem isAut_comp_lowT (t : 𝓞 K) {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) :
    IsAut Gam3 (kubT t) fun p => u (slAct (lowT t) p) := by
  intro γ hγ p hp
  show u (slAct (lowT t) (slAct γ p)) = kubT t γ * u (slAct (lowT t) p)
  rw [← slAct_mul _ _ hp, show lowT t * γ = (lowT t * γ * (lowT t)⁻¹) * lowT t by group,
    slAct_mul _ _ hp]
  exact hu _ (lowT_conj_mem t hγ) _ (slAct_mem _ hp)

end Eis

end

#print axioms Eis.lowT_coe
#print axioms Eis.cuspPar_coe
#print axioms Eis.cuspPar_mem
#print axioms Eis.lowT_mul_slT
#print axioms Eis.primary_one_sub
#print axioms Eis.kub_cuspPar
#print axioms Eis.chiT_eq_kub
#print axioms Eis.cuspPar_add
#print axioms Eis.chiT_add
#print axioms Eis.chiT_zero
#print axioms Eis.norm_chiT
#print axioms Eis.chiT_mul_conj
#print axioms Eis.thS_lowT_add
#print axioms Eis.chiT_neg
#print axioms Eis.chiT_nsmul
#print axioms Eis.chiT_zsmul_eq_one
#print axioms Eis.cub_omega_of_norm
#print axioms Eis.absNorm_crd_eq
#print axioms Eis.crd_eq
#print axioms Eis.cub_omega_sq
#print axioms Eis.chiT_lam
#print axioms Eis.chiT_lam_mul
#print axioms Eis.chiT_one
#print axioms Eis.ebr_third
#print axioms Eis.ebr_neg_third
#print axioms Eis.varpi_eq_ebr
#print axioms Eis.ebr_one_eq_one
#print axioms Eis.ebr_lam_mul
#print axioms Eis.ebr_add_period
#print axioms Eis.ebr_nsmul
#print axioms Eis.exists_cuspClass
#print axioms Eis.thS_lowT_twist_add
#print axioms Eis.lowT_conj_mem
#print axioms Eis.isUChar_kubT
#print axioms Eis.kubT_slT
#print axioms Eis.isAut_comp_lowT
