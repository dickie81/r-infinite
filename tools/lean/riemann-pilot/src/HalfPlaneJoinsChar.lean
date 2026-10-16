import LFunctionGrowth
import DirichletCharHalfPlane
import HalfPlaneJoinsFinal
import WeilTwinGeneral

/-! # The band for every `L(s, χ)` and the twin-form rates at `11/12` (round 509)

Round 468 (HalfPlaneJoinsFinal.lean) has the band `|2 Re ρ − 1| ≤ 5/6` for the zeros of `ζ` and of `L(s, χ₋₃)`, and
the rate `−C e^{5λ/6}` for the twin forms of `ζ`, `L(s, χ₋₃)` and `ζ·ζ_{ℚ(√−3)}`. Round 495's half-plane for every
Dirichlet character (`Eis.LFunction_ne_zero_of_re_gt`), at `s` for `χ` and at `1 − s` for `χ⁻¹` through the
reflection `Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)` of a primitive `χ` (`PsiOmega.LamG_one_sub'`), gives:
* `LFunction_band_of_isPrimitive`, `LFunction_band_eleven_twelfths`: every zero `ρ` of `L(s, χ)`,
  `χ ≠ 1`, with `0 < Re ρ < 1` has `|2 Re ρ − 1| ≤ 5/6`. Mathlib's `LFunction_changeLevel` carries the band from
  the primitive character inducing `χ` to `χ`: the Euler factors `1 − χ'(p)p^{−s}` it adds do not vanish on
  `Re s > 0` (round 477's `Eis.RealChar.one_sub_mul_cpow_ne_zero`);
* `chi4_rate_eleven_twelfths`, `chi8_rate_eleven_twelfths`, `QK4_rate_eleven_twelfths`: the twin forms of
  `L(s, χ₋₄)`, of `L(s, χ₋₈)` and of `ζ·ζ_{ℚ(i)}` (`Dedekind4.QK`) are at least `−C e^{5λ/6}` at `λ ≥ 0`;
* `QC_rate_eleven_twelfths`, `QKχ_rate_eleven_twelfths`: the same for `L(s, χ)` and for `ζ·L(s, χ)`, for every good
  character `χ` with `L(σ, χ) ≠ 0` on `0 < σ < 1`, the hypothesis of round 225's `twins_rate`;
* `realRooted_rate_eleven_twelfths`: `ζ`'s twin form at every real-rooted monotone base probe
  (`WeilTwinGeneral.twins_rate_realRooted`); round 468's `weil_rate_eleven_twelfths` is the base probe `box 1`.
-/

open Complex
open Pilot1ca Pilot1bt PilotWeil PsiOmega HalfPlaneS0

namespace HalfPlaneJoins

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A zero of `L(s, χ)` with `0 < Re s < 1`, `χ` primitive, reflects to a zero of `L(1 − s, χ⁻¹)`. -/
theorem LFunction_inv_one_sub_eq_zero (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - s) = 0 := by
  by_contra hne
  have h1' : 0 < (1 - s).re := by simp; linarith
  have hL := LamG_ne_zero h1' hne
  rw [LamG_one_sub' (isPrimitive_inv χ hprim), inv_inv] at hL
  apply hL
  have hz : LamG χ s = 0 := by
    unfold LamG
    rw [completed_eq_mul h0, hs, mul_zero, mul_zero]
  rw [hz, mul_zero]

/-- **The band for a primitive `χ ≠ 1`**: round 495's half-plane at `s` for `χ` and at `1 − s` for `χ⁻¹`. -/
theorem LFunction_band_of_isPrimitive (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 5 / 6 := by
  have hup : s.re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ (lt_of_not_ge h) (Or.inl hχ) hs
  have hlow : (1 - s).re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ⁻¹ (lt_of_not_ge h) (Or.inl (inv_ne_one.2 hχ))
      (LFunction_inv_one_sub_eq_zero hprim hs h0 h1)
  simp only [sub_re, one_re] at hlow
  rw [abs_le]
  constructor <;> linarith

/-- **The band `|2 Re ρ − 1| ≤ 5/6` for every `L(s, χ)`, `χ ≠ 1`**: every zero `ρ` with `0 < Re ρ < 1` has
`1/12 ≤ Re ρ ≤ 11/12`. -/
theorem LFunction_band_eleven_twelfths (hχ : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 5 / 6 := by
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, DirichletCharacter.changeLevel_one]
  have hfac := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inl hχ')
  rw [DirichletCharacter.changeLevel_primitiveCharacter, hs] at hfac
  have hprod : ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact Eis.RealChar.one_sub_mul_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp)
      (DirichletCharacter.norm_le_one _ _) h0
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
    rcases mul_eq_zero.1 hfac.symm with h | h
    · exact h
    · exact absurd h hprod
  exact LFunction_band_of_isPrimitive hχ' (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    hL h0 h1

/-- **`L(s, χ₋₄)`'s twin form**: `Q_{χ₋₄}(twin (box 1) λ) ≥ −C e^{5λ/6}`. -/
theorem chi4_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC chi4 (l + 1) (twin (box 1) l) :=
  (twins_rate_chi4 (by norm_num)).2 fun _ hs h0 h1 => LFunction_band_eleven_twelfths chi4_ne_one hs h0 h1

/-- **`L(s, χ₋₈)`'s twin form**: rate at most `5/6`. -/
theorem chi8_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC chi8 (l + 1) (twin (box 1) l) :=
  (twins_rate good_chi8 (fun _ hσ _ =>
      LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ) (by norm_num)).2
    fun _ hs h0 h1 => LFunction_band_eleven_twelfths chi8_ne_one hs h0 h1

/-- **The twin form `2Q_ζ + Q_{χ₋₄}` of `ζ·ζ_{ℚ(i)}`**: rate at most `5/6`. -/
theorem QK4_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ Dedekind4.QK (l + 1) (twin (box 1) l) :=
  (Dedekind4.QK_twins_rate (by norm_num)).2 ⟨fun _ hs => zeta_band_eleven_twelfths hs,
    fun _ hs h0 h1 => LFunction_band_eleven_twelfths chi4_ne_one hs h0 h1⟩

/-- **Every good character**: `Q_χ(twin (box 1) λ) ≥ −C e^{5λ/6}` when `L(σ, χ) ≠ 0` on `(0, 1)`. -/
theorem QC_rate_eleven_twelfths (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC χ (l + 1) (twin (box 1) l) :=
  (twins_rate hG hS (by norm_num)).2 fun _ hs h0 h1 => LFunction_band_eleven_twelfths hG.ne_one hs h0 h1

/-- **The twin form `2Q_ζ + Q_χ` of `ζ·L(χ)`, every good character**: rate at most `5/6`. -/
theorem QKχ_rate_eleven_twelfths (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) :
    ∃ C, ∀ l : ℝ, 0 ≤ l →
      -(C * Real.exp (5 / 6 * l)) ≤ WeilTwinGeneral.QKχ χ (l + 1) (twin (box 1) l) :=
  (WeilTwinGeneral.QKχ_twins_rate hG hS (by norm_num)).2
    ⟨fun _ hs => zeta_band_eleven_twelfths hs,
      fun _ hs h0 h1 => LFunction_band_eleven_twelfths hG.ne_one hs h0 h1⟩

/-- **Every real-rooted monotone base probe**: `Q(twin g₀ λ) ≥ −C e^{5λ/6}`. -/
theorem realRooted_rate_eleven_twelfths {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Set.Icc 0 b)) (hnn : ∀ u ∈ Set.Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ weilQ (l + b) (twin g₀ l) :=
  (WeilTwinGeneral.twins_rate_realRooted hb hp hmono hnn hRR (by norm_num)).2
    fun _ hs => zeta_band_eleven_twelfths hs

end HalfPlaneJoins

#print axioms HalfPlaneJoins.LFunction_band_of_isPrimitive
#print axioms HalfPlaneJoins.LFunction_band_eleven_twelfths
#print axioms HalfPlaneJoins.chi4_rate_eleven_twelfths
#print axioms HalfPlaneJoins.chi8_rate_eleven_twelfths
#print axioms HalfPlaneJoins.QK4_rate_eleven_twelfths
#print axioms HalfPlaneJoins.QC_rate_eleven_twelfths
#print axioms HalfPlaneJoins.QKχ_rate_eleven_twelfths
#print axioms HalfPlaneJoins.realRooted_rate_eleven_twelfths
