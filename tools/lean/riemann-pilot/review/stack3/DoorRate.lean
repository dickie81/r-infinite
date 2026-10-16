import WeilDedekind
import HalfPlaneJoinsFinal
import DirichletCharHalfPlane

/-! # Stack review 3, door D2: the twin-form rates at `11/12` for `χ₋₄`, `χ₋₈` and `ζ_{ℚ(i)}`

Round 468 (`HalfPlaneJoinsFinal`) has the rate `−C e^{5λ/6}` for the twin forms of `ζ`, `L(s, χ₋₃)` and
`ζ·ζ_{ℚ(√−3)}` only. Round 495's half-plane for every Dirichlet character, with the reflection `s ↦ 1 − s` of a
primitive real character (round 224's `LamG_one_sub`), gives the band `1/12 ≤ Re ρ ≤ 11/12` for the zeros of
`L(s, χ)` in the critical strip, hence the rates for `χ₋₄`, `χ₋₈` and Dedekind4's twin form.

Not compiled by any build script. Compile it as `DoorAP.lean` (7 s at round 508's head; the six printed axiom
lists are `[propext, Classical.choice, Quot.sound]`). -/

open Complex
open Pilot1ca Pilot1bt PilotWeil PsiOmega HalfPlaneS0

namespace StackReview3

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A zero of `L(s, χ)` in the critical strip, `χ` primitive and real, reflects to `1 − s`. -/
theorem LFunction_one_sub_eq_zero (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    DirichletCharacter.LFunction χ (1 - s) = 0 := by
  by_contra hne
  have h1' : 0 < (1 - s).re := by simp; linarith
  have hL := LamG_ne_zero h1' hne
  rw [LamG_one_sub hq hprim] at hL
  apply hL
  have hz : LamG χ s = 0 := by
    unfold LamG
    rw [completed_eq_mul h0, hs, mul_zero, mul_zero]
  rw [hz, mul_zero]

/-- **The band `|2 Re ρ − 1| ≤ 5/6`** for the zeros in the critical strip of `L(s, χ)`, `χ ≠ 1` primitive and real:
round 495's half-plane at `s` and at `1 − s`. -/
theorem band_eleven_twelfths (hχ : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 5 / 6 := by
  have hup : s.re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ (lt_of_not_ge h) (Or.inl hχ) hs
  have hlow : (1 - s).re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ (lt_of_not_ge h) (Or.inl hχ)
      (LFunction_one_sub_eq_zero hq hprim hs h0 h1)
  simp only [sub_re, one_re] at hlow
  rw [abs_le]
  constructor <;> linarith

/-- **`L(s, χ₋₄)`'s twin form**: `Q_{χ₋₄}(twin (box 1) λ) ≥ −C e^{5λ/6}`. -/
theorem chi4_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC chi4 (l + 1) (twin (box 1) l) :=
  (twins_rate_chi4 (by norm_num)).2 fun _ hs h0 h1 =>
    band_eleven_twelfths chi4_ne_one chi4_isQuadratic chi4_isPrimitive hs h0 h1

/-- **`L(s, χ₋₈)`'s twin form**: rate at most `5/6`. -/
theorem chi8_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC chi8 (l + 1) (twin (box 1) l) :=
  (twins_rate good_chi8 (fun _ hσ _ =>
      LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ) (by norm_num)).2
    fun _ hs h0 h1 => band_eleven_twelfths chi8_ne_one chi8_isQuadratic good_chi8.prim hs h0 h1

/-- **The Dedekind twin form `2Q_ζ + Q_{χ₋₄}` of `ζ·ζ_{ℚ(i)}`**: rate at most `5/6`. -/
theorem QK_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ Dedekind4.QK (l + 1) (twin (box 1) l) :=
  (Dedekind4.QK_twins_rate (by norm_num)).2 ⟨fun _ hs => HalfPlaneJoins.zeta_band_eleven_twelfths hs,
    fun _ hs h0 h1 => band_eleven_twelfths chi4_ne_one chi4_isQuadratic chi4_isPrimitive hs h0 h1⟩

/-- **Every good character**: `Q_χ(twin (box 1) λ) ≥ −C e^{5λ/6}` when `L(σ, χ) ≠ 0` on `(0, 1)`. -/
theorem QC_rate_eleven_twelfths (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC χ (l + 1) (twin (box 1) l) :=
  (twins_rate hG hS (by norm_num)).2 fun _ hs h0 h1 =>
    band_eleven_twelfths hG.ne_one hG.quad hG.prim hs h0 h1

/-- **The twin form `2Q_ζ + Q_χ` of `ζ·L(χ)`, every good character**: rate at most `5/6`. -/
theorem QKχ_rate_eleven_twelfths (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) :
    ∃ C, ∀ l : ℝ, 0 ≤ l →
      -(C * Real.exp (5 / 6 * l)) ≤ WeilTwinGeneral.QKχ χ (l + 1) (twin (box 1) l) :=
  (WeilTwinGeneral.QKχ_twins_rate hG hS (by norm_num)).2
    ⟨fun _ hs => HalfPlaneJoins.zeta_band_eleven_twelfths hs,
      fun _ hs h0 h1 => band_eleven_twelfths hG.ne_one hG.quad hG.prim hs h0 h1⟩

end StackReview3

#print axioms StackReview3.band_eleven_twelfths
#print axioms StackReview3.chi4_rate_eleven_twelfths
#print axioms StackReview3.chi8_rate_eleven_twelfths
#print axioms StackReview3.QK_rate_eleven_twelfths
#print axioms StackReview3.QC_rate_eleven_twelfths
#print axioms StackReview3.QKχ_rate_eleven_twelfths
