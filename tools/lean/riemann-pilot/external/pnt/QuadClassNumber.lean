/-
# Round 488: class numbers, the least inert and split primes and the Euler–Kronecker constant of a quadratic field

Imports Mathlib and the pilot's `QuadKronecker` and `ExplicitConstants`.

Plain statement. Let `K` be a number field of degree `2` with discriminant `D_K` (Mathlib's `discr K`), class number
`h_K`, `w_K` roots of unity and regulator `R_K`, and let `c = e^{−2·10²¹}`.

* `classNumber_ge`, `classNumber_le`: for `K` imaginary, `cw_K√|D_K|/(2π log log(|D_K| + 16)) ≤ h_K ≤
  w_K√|D_K| log log(|D_K| + 16)/(2πc)`, from round 487's `QuadKronecker.classNumber_formula` and round 484's
  `ExplicitConstants.norm_LFunction_one_ge_explicit` and `ExplicitConstants.norm_LFunction_one_le_explicit`.
* `classNumber_ge_sqrt`, `classNumber_ge_loglog`: `h_K ≥ c√|D_K|/(2π log log(|D_K| + 16))` by `w_K ≥ 1`, and
  `h_K ≥ c√|D_K|/(80π log log |D_K|)` by `log log(x + 16) ≤ 40 log log x` for `x ≥ 3` (`loglog_add_le`) and
  `|D_K| ≥ 3` (Mathlib's `NumberField.abs_discr_gt_two`).
* `regulator_mul_classNumber_ge`, `regulator_mul_classNumber_le`, `regulator_mul_classNumber_ge_sqrt`,
  `regulator_mul_classNumber_ge_loglog`: for `K` real, the same with `4R_Kh_K` in place of `2πh_K`, from round 485's
  `QuadIdeals.LFunction_one_eq_residue` and `QuadIdeals.residue_eq_real`.
* `exists_inert_le`, `exists_split_le`: for every `A > 12`, an inert prime and a split prime, neither dividing `D_K`,
  below `C_A(log(|D_K| + 2))^A`, with the constant `C_A` (`CA`) of round 484's
  `ExplicitConstants.exists_prime_eq_explicit`; `exists_inert_le_13`, `exists_split_le_13`: below
  `10²⁹⁸(log(|D_K| + 2))¹³`, from `ExplicitConstants.exists_prime_eq_13`.
* `eulerKronecker`: as `s → 1⁺` along the reals, `ζ_K(s) − ρ_K/(s − 1)` tends to `ρ_Kγ_K` with `γ_K = γ + L′/L(1, χ_K)`,
  where `ρ_K` is the residue of Mathlib's class number formula and `γ` is Euler's constant; and
  `|γ_K − γ| ≤ 10²¹ log log(|D_K| + 16)`, from `ExplicitConstants.norm_logDeriv_one_le_explicit`; and
  `|γ_K| ≤ 5·10²² log log |D_K|`, by `γ < 2/3` (Mathlib's `Real.eulerMascheroniConstant_lt_two_thirds`) and
  `loglog_add_le`.
-/
import Mathlib
import QuadKronecker
import ExplicitConstants

open NumberField Filter Topology

namespace QuadClassNumber

variable {K : Type*} [Field K] [NumberField K]

/-! ### The modulus `|D_K|` -/

lemma natCast_eq_abs {N : ℕ} (h : (N : ℤ) = |discr K|) : (N : ℝ) = |(discr K : ℝ)| := by
  have := congrArg (fun z : ℤ ↦ (z : ℝ)) h
  push_cast at this
  exact this

lemma natAbs_eq {N : ℕ} (h : (N : ℤ) = |discr K|) : N = (discr K).natAbs := by
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

lemma not_dvd_discr {N : ℕ} (h : (N : ℤ) = |discr K|) {p : ℕ} (hp : ¬ p ∣ N) : ¬ (p : ℤ) ∣ discr K := by
  intro hd
  apply hp
  rw [natAbs_eq h]
  exact Int.natCast_dvd_natCast.1 (Int.dvd_natAbs.2 hd)

lemma sqrt_abs_discr_pos : 0 < Real.sqrt |(discr K : ℝ)| :=
  Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))

lemma loglog_pos {N : ℕ} (h : (N : ℤ) = |discr K|) :
    0 < Real.log (Real.log (|(discr K : ℝ)| + 16)) := by
  rw [← natCast_eq_abs h]
  linarith [Littlewood.one_lt_loglog N]

/-! ### Class numbers -/

/-- For an imaginary quadratic field, `‖L(1, χ_K)‖ = 2πh_K/(w_K√|D_K|)`. -/
lemma exists_norm_imag (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N),
      (N : ℤ) = |discr K| ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ‖DirichletCharacter.LFunction χ 1‖ =
        2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  obtain ⟨N, hN, χ, hND, hq, hχ, hL⟩ := QuadKronecker.classNumber_formula hK hc
  refine ⟨N, hN, χ, hND, hq, hχ, ?_⟩
  rw [hL, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **The class number of an imaginary quadratic field, from below**:
`h_K ≥ w_K√|D_K|e^{−2·10²¹}/(2π log log(|D_K| + 16))`. -/
theorem classNumber_ge (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| * Real.exp (-(2 * 10 ^ 21)) /
      (2 * Real.pi * Real.log (Real.log (|(discr K : ℝ)| + 16))) ≤ classNumber K := by
  obtain ⟨N, hN, χ, hND, hq, hχ, hL⟩ := exists_norm_imag hK hc
  have hlow := ExplicitConstants.norm_LFunction_one_ge_explicit N χ hq hχ
  rw [hL, natCast_eq_abs hND] at hlow
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := sqrt_abs_discr_pos (K := K)
  have hl := loglog_pos hND
  rw [div_le_div_iff₀ hl (by positivity)] at hlow
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **The class number of an imaginary quadratic field, from above**:
`h_K ≤ w_K√|D_K|e^{2·10²¹} log log(|D_K| + 16)/(2π)`. -/
theorem classNumber_le (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    (classNumber K : ℝ) ≤ (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
      Real.exp (2 * 10 ^ 21) * Real.log (Real.log (|(discr K : ℝ)| + 16)) / (2 * Real.pi) := by
  obtain ⟨N, hN, χ, hND, hq, hχ, hL⟩ := exists_norm_imag hK hc
  have hup := ExplicitConstants.norm_LFunction_one_le_explicit N χ hq hχ
  rw [hL, natCast_eq_abs hND] at hup
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := sqrt_abs_discr_pos (K := K)
  rw [div_le_iff₀ (by positivity)] at hup
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

lemma one_le_torsionOrder : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
  exact Nat.one_le_cast.mpr (Units.torsionOrder_pos K)

/-- **Door 4(b)'s bound for imaginary quadratic fields**:
`h_K ≥ e^{−2·10²¹}√|D_K|/(2π log log(|D_K| + 16))`. -/
theorem classNumber_ge_sqrt (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)| /
      (2 * Real.pi * Real.log (Real.log (|(discr K : ℝ)| + 16))) ≤ classNumber K := by
  refine le_trans ?_ (classNumber_ge hK hc)
  obtain ⟨N, -, -, hND, -, -, -⟩ := QuadKronecker.classNumber_formula hK hc
  have hl := loglog_pos hND
  have hr := sqrt_abs_discr_pos (K := K)
  have hw := one_le_torsionOrder (K := K)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  calc Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|
      = 1 * (Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|) := by ring
    _ ≤ (Units.torsionOrder K : ℝ) * (Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| * Real.exp (-(2 * 10 ^ 21)) := by ring

/-- For a real quadratic field, `‖L(1, χ_K)‖ = 4R_K h_K/(w_K√D_K)`. -/
lemma exists_norm_real (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrComplexPlaces K = 0) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N),
      (N : ℤ) = |discr K| ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ‖DirichletCharacter.LFunction χ 1‖ =
        4 * Units.regulator K * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  obtain ⟨N, hN, χ, hND, hq, hχ, -, hz⟩ := QuadKronecker.exists_kronecker hK
  refine ⟨N, hN, χ, hND, hq, hχ, ?_⟩
  have hR := Units.regulator_pos K
  rw [QuadIdeals.LFunction_one_eq_residue χ hχ hz, QuadIdeals.residue_eq_real hK hc, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **The class number and regulator of a real quadratic field, from below**:
`R_K h_K ≥ w_K√D_K e^{−2·10²¹}/(4 log log(D_K + 16))`. -/
theorem regulator_mul_classNumber_ge (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| * Real.exp (-(2 * 10 ^ 21)) /
      (4 * Real.log (Real.log (|(discr K : ℝ)| + 16))) ≤ Units.regulator K * classNumber K := by
  obtain ⟨N, hN, χ, hND, hq, hχ, hL⟩ := exists_norm_real hK hc
  have hlow := ExplicitConstants.norm_LFunction_one_ge_explicit N χ hq hχ
  rw [hL, natCast_eq_abs hND] at hlow
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := sqrt_abs_discr_pos (K := K)
  have hl := loglog_pos hND
  rw [div_le_div_iff₀ hl (by positivity)] at hlow
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The class number and regulator of a real quadratic field, from above**:
`R_K h_K ≤ w_K√D_K e^{2·10²¹} log log(D_K + 16)/4`. -/
theorem regulator_mul_classNumber_le (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    Units.regulator K * classNumber K ≤ (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
      Real.exp (2 * 10 ^ 21) * Real.log (Real.log (|(discr K : ℝ)| + 16)) / 4 := by
  obtain ⟨N, hN, χ, hND, hq, hχ, hL⟩ := exists_norm_real hK hc
  have hup := ExplicitConstants.norm_LFunction_one_le_explicit N χ hq hχ
  rw [hL, natCast_eq_abs hND] at hup
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := sqrt_abs_discr_pos (K := K)
  rw [div_le_iff₀ (by positivity)] at hup
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Door 4(b)'s bound for real quadratic fields**: `R_K h_K ≥ e^{−2·10²¹}√D_K/(4 log log(D_K + 16))`. -/
theorem regulator_mul_classNumber_ge_sqrt (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)| /
      (4 * Real.log (Real.log (|(discr K : ℝ)| + 16))) ≤ Units.regulator K * classNumber K := by
  refine le_trans ?_ (regulator_mul_classNumber_ge hK hc)
  obtain ⟨N, -, -, hND, -, -, -⟩ := exists_norm_real hK hc
  have hl := loglog_pos hND
  have hr := sqrt_abs_discr_pos (K := K)
  have hw := one_le_torsionOrder (K := K)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  calc Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|
      = 1 * (Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|) := by ring
    _ ≤ (Units.torsionOrder K : ℝ) * (Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)|) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| * Real.exp (-(2 * 10 ^ 21)) := by ring

/-! ### The form `c√|D_K|/log log |D_K|` -/

/-- `log 3 > 12/11`, from `e¹² < 3¹¹`. -/
lemma log_three_gt : (12 : ℝ) / 11 < Real.log 3 := by
  have h12 : Real.exp 12 < 3 ^ 11 := by
    have he : Real.exp 12 = Real.exp 1 ^ 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    calc Real.exp 1 ^ 12 < 2.7182818286 ^ 12 := by
          gcongr
          exact Real.exp_one_lt_d9
      _ < 3 ^ 11 := by norm_num
  have h : (12 : ℝ) < Real.log (3 ^ 11) := (Real.lt_log_iff_exp_lt (by norm_num)).2 h12
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- **`log log(x + 16) ≤ 40 log log x` for `x ≥ 3`.** -/
lemma loglog_add_le {x : ℝ} (hx : 3 ≤ x) :
    Real.log (Real.log (x + 16)) ≤ 40 * Real.log (Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hu1 : 12 / 11 < Real.log x :=
    lt_of_lt_of_le log_three_gt (Real.log_le_log (by norm_num) hx)
  set u := Real.log x with hu
  have hu0 : 0 < u := by linarith
  have h7 : Real.log 7 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    nlinarith [Real.exp_one_gt_d9]
  have hlx : Real.log (x + 16) ≤ 2 + u := by
    calc Real.log (x + 16) ≤ Real.log (7 * x) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 7 + u := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ 2 + u := by linarith
  have hb : 1 + 39 * (u - 1) ≤ u ^ 39 := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) 39
    simpa using this
  have hpow : 2 + u ≤ u ^ 40 := by
    calc 2 + u ≤ u * (1 + 39 * (u - 1)) := by nlinarith [mul_pos (sub_pos.2 hu1) hu0]
      _ ≤ u * u ^ 39 := by gcongr
      _ = u ^ 40 := by ring
  have hlpos : 0 < Real.log (x + 16) := Real.log_pos (by linarith)
  calc Real.log (Real.log (x + 16)) ≤ Real.log (u ^ 40) := Real.log_le_log hlpos (hlx.trans hpow)
    _ = 40 * Real.log u := by
      rw [Real.log_pow]
      norm_num

/-- `|D_K| ≥ 3` for a quadratic field (Mathlib's `NumberField.abs_discr_gt_two`). -/
lemma three_le_abs_discr (hK : Module.finrank ℚ K = 2) : (3 : ℝ) ≤ |(discr K : ℝ)| := by
  have h := abs_discr_gt_two (K := K) (by omega)
  have h3 : (3 : ℤ) ≤ |discr K| := h
  exact_mod_cast h3

/-- **Door 4(b)'s bound for imaginary quadratic fields, in the form `c√|D_K|/log log |D_K|`**:
`h_K ≥ e^{−2·10²¹}√|D_K|/(80π log log |D_K|)`. -/
theorem classNumber_ge_loglog (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)| /
      (80 * Real.pi * Real.log (Real.log |(discr K : ℝ)|)) ≤ classNumber K := by
  refine le_trans ?_ (classNumber_ge_sqrt hK hc)
  obtain ⟨N, -, -, hND, -, -, -⟩ := QuadKronecker.classNumber_formula hK hc
  have hl := loglog_pos hND
  have hll := loglog_add_le (three_le_abs_discr hK)
  have h2 := mul_le_mul_of_nonneg_left hll (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-- **Door 4(b)'s bound for real quadratic fields, in the form `c√D_K/log log D_K`**:
`R_K h_K ≥ e^{−2·10²¹}√D_K/(160 log log D_K)`. -/
theorem regulator_mul_classNumber_ge_loglog (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    Real.exp (-(2 * 10 ^ 21)) * Real.sqrt |(discr K : ℝ)| /
      (160 * Real.log (Real.log |(discr K : ℝ)|)) ≤ Units.regulator K * classNumber K := by
  refine le_trans ?_ (regulator_mul_classNumber_ge_sqrt hK hc)
  obtain ⟨N, -, -, hND, -, -, -⟩ := exists_norm_real hK hc
  have hl := loglog_pos hND
  have hll := loglog_add_le (three_le_abs_discr hK)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-! ### The least inert and split primes -/

/-- The constant of round 484's `ExplicitConstants.exists_prime_eq_explicit`. -/
noncomputable def CA (A : ℝ) : ℝ :=
  101 + (4 * (2 * 10 ^ 11 / (min (1 / 12 - 1 / A) (1 / 24)) ^ 5 + 11)) ^ A

/-- The splitting type at a prime `p` with `χ_K(p) = ±1`. -/
lemma type_of_eq {N : ℕ} {χ : DirichletCharacter ℂ N}
    (htype : ∀ p : ℕ, p.Prime → (χ p = 1 ∧ QuadIdeals.Split K p) ∨ (χ p = -1 ∧ QuadIdeals.Inert K p) ∨
      (χ p = 0 ∧ QuadIdeals.Ramified K p))
    {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hχp : χ p = ε) :
    (ε = 1 ∧ QuadIdeals.Split K p) ∨ (ε = -1 ∧ QuadIdeals.Inert K p) := by
  rcases htype p hp with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hχp
  · exact Or.inl ⟨by exact_mod_cast hχp.symm, h'⟩
  · exact Or.inr ⟨by exact_mod_cast hχp.symm, h'⟩
  · exfalso
    rcases hε with rfl | rfl <;> norm_num at hχp

/-- **An inert prime below `C_A(log(|D_K| + 2))^A`**, for every `A > 12`. -/
theorem exists_inert_le (hK : Module.finrank ℚ K = 2) {A : ℝ} (hA : 12 < A) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ discr K ∧ QuadIdeals.Inert K p ∧
      (p : ℝ) ≤ CA A * Real.log (|(discr K : ℝ)| + 2) ^ A := by
  obtain ⟨N, hN, χ, hND, hq, hχ, htype, -⟩ := QuadKronecker.exists_kronecker hK
  obtain ⟨p, hp, hpN, hχp, hple⟩ :=
    ExplicitConstants.exists_prime_eq_explicit hA N χ hq hχ (ε := -1) (Or.inr rfl)
  rcases type_of_eq htype hp (Or.inr rfl) hχp with ⟨h, -⟩ | ⟨-, h⟩
  · norm_num at h
  · exact ⟨p, hp, not_dvd_discr hND hpN, h, by rw [CA, ← natCast_eq_abs hND]; exact hple⟩

/-- **A split prime below `C_A(log(|D_K| + 2))^A`**, for every `A > 12`. -/
theorem exists_split_le (hK : Module.finrank ℚ K = 2) {A : ℝ} (hA : 12 < A) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ discr K ∧ QuadIdeals.Split K p ∧
      (p : ℝ) ≤ CA A * Real.log (|(discr K : ℝ)| + 2) ^ A := by
  obtain ⟨N, hN, χ, hND, hq, hχ, htype, -⟩ := QuadKronecker.exists_kronecker hK
  obtain ⟨p, hp, hpN, hχp, hple⟩ :=
    ExplicitConstants.exists_prime_eq_explicit hA N χ hq hχ (ε := 1) (Or.inl rfl)
  rcases type_of_eq htype hp (Or.inl rfl) hχp with ⟨-, h⟩ | ⟨h, -⟩
  · exact ⟨p, hp, not_dvd_discr hND hpN, h, by rw [CA, ← natCast_eq_abs hND]; exact hple⟩
  · norm_num at h

/-- **An inert prime below `10²⁹⁸(log(|D_K| + 2))¹³`.** -/
theorem exists_inert_le_13 (hK : Module.finrank ℚ K = 2) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ discr K ∧ QuadIdeals.Inert K p ∧
      (p : ℝ) ≤ 10 ^ 298 * Real.log (|(discr K : ℝ)| + 2) ^ 13 := by
  obtain ⟨N, hN, χ, hND, hq, hχ, htype, -⟩ := QuadKronecker.exists_kronecker hK
  obtain ⟨p, hp, hpN, hχp, hple⟩ := ExplicitConstants.exists_prime_eq_13 N χ hq hχ (ε := -1) (Or.inr rfl)
  rcases type_of_eq htype hp (Or.inr rfl) hχp with ⟨h, -⟩ | ⟨-, h⟩
  · norm_num at h
  · exact ⟨p, hp, not_dvd_discr hND hpN, h, by rw [← natCast_eq_abs hND]; exact hple⟩

/-- **A split prime below `10²⁹⁸(log(|D_K| + 2))¹³`.** -/
theorem exists_split_le_13 (hK : Module.finrank ℚ K = 2) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ discr K ∧ QuadIdeals.Split K p ∧
      (p : ℝ) ≤ 10 ^ 298 * Real.log (|(discr K : ℝ)| + 2) ^ 13 := by
  obtain ⟨N, hN, χ, hND, hq, hχ, htype, -⟩ := QuadKronecker.exists_kronecker hK
  obtain ⟨p, hp, hpN, hχp, hple⟩ := ExplicitConstants.exists_prime_eq_13 N χ hq hχ (ε := 1) (Or.inl rfl)
  rcases type_of_eq htype hp (Or.inl rfl) hχp with ⟨-, h⟩ | ⟨h, -⟩
  · exact ⟨p, hp, not_dvd_discr hND hpN, h, by rw [← natCast_eq_abs hND]; exact hple⟩
  · norm_num at h

/-! ### The Euler–Kronecker constant -/

/-- **The Euler–Kronecker constant of a quadratic field.** As `s → 1⁺`, `ζ_K(s) − ρ_K/(s − 1)` tends to
`ρ_Kγ_K`, where `ρ_K` is the residue in Mathlib's class number formula and `γ_K = γ + L′/L(1, χ_K)`; and
`|γ_K − γ| ≤ 10²¹ log log(|D_K| + 16)` and `|γ_K| ≤ 5·10²² log log |D_K|`. -/
theorem eulerKronecker (hK : Module.finrank ℚ K = 2) :
    ∃ γK : ℂ, Tendsto (fun s : ℝ ↦ dedekindZeta K s - (dedekindZeta_residue K : ℂ) / ((s : ℂ) - 1))
        (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K : ℂ) * γK)) ∧
      ‖γK - Real.eulerMascheroniConstant‖ ≤ 10 ^ 21 * Real.log (Real.log (|(discr K : ℝ)| + 16)) ∧
      ‖γK‖ ≤ 5 * 10 ^ 22 * Real.log (Real.log |(discr K : ℝ)|) := by
  obtain ⟨N, hN, χ, hND, hq, hχ, -, hz⟩ := QuadKronecker.exists_kronecker hK
  have hres := QuadIdeals.LFunction_one_eq_residue χ hχ hz
  have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 := by
    rw [hres]
    exact_mod_cast (dedekindZeta_residue_pos K).ne'
  have hd : ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      10 ^ 21 * Real.log (Real.log (|(discr K : ℝ)| + 16)) := by
    have h := ExplicitConstants.norm_logDeriv_one_le_explicit N χ hq hχ
    rwa [natCast_eq_abs hND] at h
  refine ⟨Real.eulerMascheroniConstant +
    deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1, ?_, ?_, ?_⟩
  · have hof : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 1) := by
      have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hof ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h1
      have := Complex.ofReal_injective (h1.trans Complex.ofReal_one.symm)
      exact (ne_of_gt (Set.mem_Ioi.1 hs)) this
    have hdiff := DirichletCharacter.differentiable_LFunction hχ
    have hz1 := tendsto_riemannZeta_sub_one_div.comp hmap
    have hcont : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
        (𝓝 (DirichletCharacter.LFunction χ 1)) := (hdiff.continuous.tendsto 1).comp hof
    have hslope := (hasDerivAt_iff_tendsto_slope.1 (hdiff 1).hasDerivAt).comp hmap
    have hsum := (hz1.mul hcont).add hslope
    have heq : ((fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) ∘ (fun s : ℝ ↦ (s : ℂ))) *
        (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ)) +
        (slope (DirichletCharacter.LFunction χ) 1 ∘ (fun s : ℝ ↦ (s : ℂ))) =ᶠ[𝓝[>] 1]
        fun s : ℝ ↦ dedekindZeta K s - (dedekindZeta_residue K : ℂ) / ((s : ℂ) - 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : (s : ℂ) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        have := Complex.ofReal_injective (h1.trans Complex.ofReal_one.symm)
        exact (ne_of_gt (Set.mem_Ioi.1 hs)) this
      simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply]
      rw [hz s (by simpa using hs), slope_def_field, ← hres]
      field_simp
      ring
    refine (hsum.congr' heq).trans (le_of_eq ?_)
    congr 1
    rw [← hres]
    field_simp
  · simpa using hd
  · have hl1 : 1 < Real.log (Real.log (|(discr K : ℝ)| + 16)) := by
      rw [← natCast_eq_abs hND]
      exact Littlewood.one_lt_loglog N
    have hll := loglog_add_le (three_le_abs_discr hK)
    have hγ := Real.eulerMascheroniConstant_lt_two_thirds
    have hγ0 := Real.one_half_lt_eulerMascheroniConstant
    have hn : ‖(Real.eulerMascheroniConstant : ℂ) +
        deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        Real.eulerMascheroniConstant + 10 ^ 21 * Real.log (Real.log (|(discr K : ℝ)| + 16)) := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith [hd]
    linarith

end QuadClassNumber
