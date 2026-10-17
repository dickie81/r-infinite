import HalfPlaneJoins
import BohrJoins
import KubotaThetaProof

/-! # The half-plane's joins with no hypothesis (round 468)

Round 279's `HalfPlaneJoins` fed round 278's `SmoothBound θ` to the stack's sockets for a fixed zero-free
strip. Round 466 proved the family's mean square at every `σ > 0` (`Eis.meanSquare`). Through round 288's
`Eis.weightedBound_of_meanSquare` and round 285's `Eis.smoothBound_of_weightedBound` it gives
`SmoothBound ((11 + 5σ)/12)` for every `σ > 0`. For a given `ε > 0`, `σ = 6ε/5` with `ε/2` in that bound gives
the exponent `11/12 + ε`:
* `smoothBound_eleven_twelfths`: `SmoothBound (11/12)`.

Round 279's joins at `θ = 11/12`:
* `zeta_band_eleven_twelfths`, `chi3_band_eleven_twelfths`: every nontrivial zero of `ζ`, and every zero of
  `L(s, χ₋₃)` in the critical strip, has `|2 Re ρ − 1| ≤ 5/6`, so `1/12 ≤ Re ρ ≤ 11/12`;
* `abs_im_tau_le_five_twelfths`: every zero `τ` of `Ξ` has `|Im τ| ≤ 5/12`;
* `weil_rate_eleven_twelfths`, `chi3_rate_eleven_twelfths`, `QK3_rate_eleven_twelfths`: the twin forms of `ζ`,
  of `L(s, χ₋₃)` and of `ζ·ζ_{ℚ(√−3)}` are at least `−C e^{5λ/6}` at `λ ≥ 0`;
* `lam_prefactor_eleven_twelfths`: `λ₁(a) ≤ K(a + 1)e^{(59/6)a − 4πe^{2a}}` for `a ≥ 4`.

Round 398's join with the Kubota–Patterson display, at round 466's `Eis.kubotaTheta`:
* `BohrJoins.shell_eleven_twelfths`: every nontrivial zero `ρ` has `‖v_F(11/12)‖ ≤ ‖v_F(ρ)‖ ≤ ‖v_F(1/12)‖` for
  every nonempty finite set `F` of primes (`BohrJoins.shell_of_kubotaTheta`).
-/

open Complex
open Pilot1ca Pilot1bt PilotWeil PsiOmega HalfPlaneS0

namespace HalfPlaneJoins

/-- **S0's hypothesis at `11/12`**, from round 466's mean square. -/
theorem smoothBound_eleven_twelfths : SmoothBound (11 / 12) := by
  intro W hW ε hε
  have hσ : (0 : ℝ) < 6 * ε / 5 := by positivity
  have h := Eis.smoothBound_of_weightedBound (by positivity)
    (Eis.weightedBound_of_meanSquare hσ.le (Eis.meanSquare hσ)) W hW (ε / 2) (by positivity)
  have e : (11 + 5 * (6 * ε / 5)) / 12 + ε / 2 = 11 / 12 + ε := by ring
  rw [e] at h
  exact h

/-- Every nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ 5/6`. -/
theorem zeta_band_eleven_twelfths {s : ℂ} (hs : IsNontrivialZero s) : |2 * s.re - 1| ≤ 5 / 6 := by
  have := zeta_band smoothBound_eleven_twelfths hs
  norm_num at this ⊢
  linarith

/-- Every zero of `L(s, χ₋₃)` in the critical strip has `|2 Re ρ − 1| ≤ 5/6`. -/
theorem chi3_band_eleven_twelfths {s : ℂ} (hs : DirichletCharacter.LFunction chi3 s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) : |2 * s.re - 1| ≤ 5 / 6 := by
  have := chi3_band smoothBound_eleven_twelfths hs h0 h1
  norm_num at this ⊢
  linarith

/-- Every zero `τ` of `Ξ` has `|Im τ| ≤ 5/12`. -/
theorem abs_im_tau_le_five_twelfths (i : ZeroIdx (sqF Xi)) : |(tau i).im| ≤ 5 / 12 := by
  have := abs_im_tau_le smoothBound_eleven_twelfths i
  norm_num at this ⊢
  linarith

/-- **`ζ`'s twin form**: `Q(twin (box 1) λ) ≥ −C e^{5λ/6}`. -/
theorem weil_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ weilQ (l + 1) (twin (box 1) l) := by
  have := weil_rate_of_smoothBound smoothBound_eleven_twelfths (by norm_num)
  have e : 2 * (11 / 12 : ℝ) - 1 = 5 / 6 := by norm_num
  rw [e] at this
  exact this

/-- **`L(s, χ₋₃)`'s twin form**: rate at most `5/6`. -/
theorem chi3_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ QC chi3 (l + 1) (twin (box 1) l) := by
  have := chi3_rate_of_smoothBound smoothBound_eleven_twelfths (by norm_num)
  have e : 2 * (11 / 12 : ℝ) - 1 = 5 / 6 := by norm_num
  rw [e] at this
  exact this

/-- **The twin form `2Q_ζ + Q_{χ₋₃}` of `ζ·ζ_{ℚ(√−3)}`**: rate at most `5/6`. -/
theorem QK3_rate_eleven_twelfths :
    ∃ C, ∀ l : ℝ, 0 ≤ l →
      -(C * Real.exp (5 / 6 * l)) ≤ WeilTwinGeneral.QKχ chi3 (l + 1) (twin (box 1) l) := by
  have := QK3_rate_of_smoothBound smoothBound_eleven_twelfths (by norm_num)
  have e : 2 * (11 / 12 : ℝ) - 1 = 5 / 6 := by norm_num
  rw [e] at this
  exact this

/-- **Round 164's prefactor**: `λ₁(a) ≤ K(a + 1)e^{(59/6)a − 4πe^{2a}}` for `a ≥ 4`. -/
theorem lam_prefactor_eleven_twelfths :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a →
      lam a ≤ K * (a + 1) * Real.exp (59 / 6 * a - 4 * Real.pi * Real.exp (2 * a)) := by
  have := lam_prefactor_of_smoothBound smoothBound_eleven_twelfths (by norm_num)
  have e : (8 + 2 * (11 / 12 : ℝ)) = 59 / 6 := by norm_num
  rw [e] at this
  exact this

end HalfPlaneJoins

namespace BohrJoins

open BohrSphere

/-- **The Bohr shell at `11/12`**: round 398's `shell_of_kubotaTheta` at round 466's `Eis.kubotaTheta`. -/
theorem shell_eleven_twelfths {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ}
    (hρ : Pilot1bt.IsNontrivialZero ρ) :
    ‖vF F ((11 / 12 : ℝ) : ℂ)‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 / 12 : ℝ) : ℂ)‖ :=
  shell_of_kubotaTheta Eis.kubotaTheta hF hρ

end BohrJoins

#print axioms HalfPlaneJoins.smoothBound_eleven_twelfths
#print axioms HalfPlaneJoins.zeta_band_eleven_twelfths
#print axioms HalfPlaneJoins.chi3_band_eleven_twelfths
#print axioms HalfPlaneJoins.abs_im_tau_le_five_twelfths
#print axioms HalfPlaneJoins.weil_rate_eleven_twelfths
#print axioms HalfPlaneJoins.chi3_rate_eleven_twelfths
#print axioms HalfPlaneJoins.QK3_rate_eleven_twelfths
#print axioms HalfPlaneJoins.lam_prefactor_eleven_twelfths
#print axioms BohrJoins.shell_eleven_twelfths
