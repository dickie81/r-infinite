import Mathlib

/-! # The electron's charge from the cascade's hypercharge rule (round 407)

Part IVb's Theorem `thm:sector-fundamental-y`: a matter state in the sector `V₁₂ ⊗ V₁₃ ⊗ V₁₄`, with
`V₁₂ ∈ {1, 3}`, `V₁₃ ∈ {1, 2}`, carries the phase `a·c₃/3 + b·c₂/2 + η(a,b)·q` (in turns) under the diagonal
element `(ζ₃^a, ζ₂^b, e^{2πiη(a,b)})`, with `η(a,b) = −(a/3 + b/2)` and `c₃, c₂` the indicators of `3` and `2`.
Here `q` is the integer `U(1)` charge and `Y = q/6` the hypercharge.

* The diagonal `ℤ₆` acts trivially exactly when `q ≡ c₃ (mod 3)` and `q ≡ c₂ (mod 2)` (`z6Trivial_iff`).
* The least nonzero `|q|` in a sector is `6/(dim V₁₂·dim V₁₃)`, so `|Y|` is at least `1/(dim V₁₂·dim V₁₃)`
  (`minimal_charge`): `1/6, 1/3, 1/2, 1` in the sectors `(3,2), (3,1), (1,2), (1,1)`.
* With the sector minima, `Y_H = ½`, and gauge invariance of the lepton Yukawa singlet `L̄He_R`, a nonzero
  `Y_e` forces `Y_L = −½` and `Y_e = −1` (`lepton_hypercharges`). With `Q = T₃ + Y`, the electron has charge
  `−1` in both chiralities and the neutrino `0` (`electron_charge`).
* Checks: the six Standard Model hypercharges pass the `ℤ₆` test (`sm_z6Trivial`); `2Q_u + Q_d + Q_e = 0`
  (`hydrogen_neutral`); the four anomaly sums of one generation vanish (`anomaly_free`).

The gauge group, the sector list, the `ℤ₆` requirement, the minimal-charge rule, `Q = T₃ + Y` and the overall
sign are the series' inputs, displayed here as definitions and hypotheses.
-/

namespace Electron

/-- The phase, in turns, of `(ζ₃^a, ζ₂^b, e^{2πiη(a,b)})` with `η(a,b) = −(a/3 + b/2)` on a state with
indicators `c₃, c₂` and `U(1)` charge `q`. -/
def z6Phase (c3 c2 q a b : ℤ) : ℚ := a * c3 / 3 + b * c2 / 2 - (a / 3 + b / 2) * q

/-- The diagonal `ℤ₆` acts trivially. -/
def Z6Trivial (c3 c2 q : ℤ) : Prop := ∀ a b : ℤ, ∃ n : ℤ, z6Phase c3 c2 q a b = n

theorem z6Trivial_iff (c3 c2 q : ℤ) : Z6Trivial c3 c2 q ↔ q ≡ c3 [ZMOD 3] ∧ q ≡ c2 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h 1 0
    obtain ⟨m, hm⟩ := h 0 1
    simp only [z6Phase] at hn hm
    push_cast at hn hm
    have h3 : (c3 : ℚ) - q = 3 * n := by linarith
    have h2 : (c2 : ℚ) - q = 2 * m := by linarith
    have h3' : c3 - q = 3 * n := by exact_mod_cast h3
    have h2' : c2 - q = 2 * m := by exact_mod_cast h2
    exact ⟨Int.modEq_iff_dvd.2 ⟨n, h3'⟩, Int.modEq_iff_dvd.2 ⟨m, h2'⟩⟩
  · rintro ⟨h3, h2⟩
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h3.symm
    obtain ⟨l, hl⟩ := Int.modEq_iff_dvd.1 h2.symm
    intro a b
    refine ⟨-(a * k) - b * l, ?_⟩
    have hk' : (q : ℚ) - c3 = 3 * k := by exact_mod_cast hk
    have hl' : (q : ℚ) - c2 = 2 * l := by exact_mod_cast hl
    simp only [z6Phase]
    push_cast
    linear_combination (-(a : ℚ) / 3) * hk' + (-(b : ℚ) / 2) * hl'

/-- `dim V₁₂ = 1 + 2c₃` and `dim V₁₃ = 1 + c₂`. -/
def dimV12 (c3 : ℤ) : ℤ := 1 + 2 * c3
def dimV13 (c2 : ℤ) : ℤ := 1 + c2

/-- **The sector-fundamental rule**: in each sector the least nonzero `|q|` is `6/(dim V₁₂·dim V₁₃)`. -/
theorem minimal_charge (c3 c2 : ℤ) (h3 : c3 = 0 ∨ c3 = 1) (h2 : c2 = 0 ∨ c2 = 1) :
    (∃ q, q ≠ 0 ∧ Z6Trivial c3 c2 q ∧ |q| * (dimV12 c3 * dimV13 c2) = 6) ∧
      ∀ q, q ≠ 0 → Z6Trivial c3 c2 q → 6 ≤ |q| * (dimV12 c3 * dimV13 c2) := by
  simp only [z6Trivial_iff, Int.ModEq, dimV12, dimV13]
  rcases h3 with rfl | rfl <;> rcases h2 with rfl | rfl
  · refine ⟨⟨6, by norm_num, by decide, by norm_num⟩, fun q hq ⟨a, b⟩ => ?_⟩
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · refine ⟨⟨3, by norm_num, by decide, by norm_num⟩, fun q hq ⟨a, b⟩ => ?_⟩
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · refine ⟨⟨-2, by norm_num, by decide, by norm_num⟩, fun q hq ⟨a, b⟩ => ?_⟩
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · refine ⟨⟨1, by norm_num, by decide, by norm_num⟩, fun q hq ⟨a, b⟩ => ?_⟩
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- The hypercharge `Y = q/6`. -/
def hyper (q : ℤ) : ℚ := q / 6

/-- The six Standard Model fields of one generation, by sector and `U(1)` charge: `Q_L (3,2), q = 1`;
`u_R (3,1), q = 4`; `d_R (3,1), q = −2`; `L_L (1,2), q = −3`; `e_R (1,1), q = −6`; `H (1,2), q = 3`. All pass
the `ℤ₆` test, and their hypercharges are `1/6, 2/3, −1/3, −1/2, −1, 1/2`. -/
theorem sm_z6Trivial :
    Z6Trivial 1 1 1 ∧ Z6Trivial 1 0 4 ∧ Z6Trivial 1 0 (-2) ∧ Z6Trivial 0 1 (-3) ∧
      Z6Trivial 0 0 (-6) ∧ Z6Trivial 0 1 3 := by
  simp only [z6Trivial_iff]
  decide

theorem sm_hypercharges :
    hyper 1 = 1 / 6 ∧ hyper 4 = 2 / 3 ∧ hyper (-2) = -1 / 3 ∧ hyper (-3) = -1 / 2 ∧
      hyper (-6) = -1 ∧ hyper 3 = 1 / 2 := by
  simp only [hyper]; norm_num

/-- In the `(3,2)` sector the minimum `q = 1` has one sign: `q = −1` fails the `ℤ₆` test. -/
theorem quark_doublet_sign : Z6Trivial 1 1 1 ∧ ¬ Z6Trivial 1 1 (-1) := by
  simp only [z6Trivial_iff]
  decide

/-- **The lepton hypercharges.** With the sector minima `Y_L = ±½`, the Higgs at `Y_H = ½`, and gauge
invariance of `L̄He_R` (`Y_e = Y_L − Y_H`), a nonzero `Y_e` forces `Y_L = −½` and `Y_e = −1`. -/
theorem lepton_hypercharges (YL Ye : ℚ) (hL : YL = 1 / 2 ∨ YL = -1 / 2) (hyuk : Ye = YL - 1 / 2)
    (he : Ye ≠ 0) : YL = -1 / 2 ∧ Ye = -1 := by
  rcases hL with h | h
  · exact absurd (by rw [hyuk, h]; norm_num) he
  · exact ⟨h, by rw [hyuk, h]; norm_num⟩

/-- The electric charge `Q = T₃ + Y`. -/
def elCharge (T3 Y : ℚ) : ℚ := T3 + Y

/-- **The electron's charge**: `−1` for `e_L` (`T₃ = −½`, `Y = −½`) and for `e_R` (`T₃ = 0`, `Y = −1`);
the neutrino (`T₃ = ½`, `Y = −½`) is neutral. -/
theorem electron_charge :
    elCharge (-1 / 2) (-1 / 2) = -1 ∧ elCharge 0 (-1) = -1 ∧ elCharge (1 / 2) (-1 / 2) = 0 := by
  simp only [elCharge]; norm_num

/-- The quark charges: `u` at `2/3` and `d` at `−1/3`, in both chiralities. -/
theorem quark_charges :
    elCharge (1 / 2) (1 / 6) = 2 / 3 ∧ elCharge (-1 / 2) (1 / 6) = -1 / 3 ∧
      elCharge 0 (2 / 3) = 2 / 3 ∧ elCharge 0 (-1 / 3) = -1 / 3 := by
  simp only [elCharge]; norm_num

/-- `2Q_u + Q_d + Q_e = 0`: hydrogen (`uud` plus `e`) is neutral. -/
theorem hydrogen_neutral : 2 * (2 / 3 : ℚ) + (-1 / 3) + (-1) = 0 := by norm_num

/-- The four anomaly sums of one generation, over left-handed Weyl fields `Q (3,2,1/6)`, `uᶜ (3̄,1,−2/3)`,
`dᶜ (3̄,1,1/3)`, `L (1,2,−1/2)`, `eᶜ (1,1,1)`: `U(1)³`, gravitational, `SU(3)²U(1)`, `SU(2)²U(1)`. -/
theorem anomaly_free :
    6 * (1 / 6 : ℚ) ^ 3 + 3 * (-2 / 3) ^ 3 + 3 * (1 / 3) ^ 3 + 2 * (-1 / 2) ^ 3 + 1 ^ 3 = 0 ∧
      6 * (1 / 6 : ℚ) + 3 * (-2 / 3) + 3 * (1 / 3) + 2 * (-1 / 2) + 1 = 0 ∧
      2 * (1 / 6 : ℚ) + (-2 / 3) + (1 / 3) = 0 ∧
      3 * (1 / 6 : ℚ) + (-1 / 2) = 0 := by
  norm_num

end Electron

#print axioms Electron.z6Trivial_iff
#print axioms Electron.minimal_charge
#print axioms Electron.sm_z6Trivial
#print axioms Electron.quark_doublet_sign
#print axioms Electron.lepton_hypercharges
#print axioms Electron.electron_charge
#print axioms Electron.anomaly_free
#print axioms Electron.sm_hypercharges
#print axioms Electron.quark_charges
#print axioms Electron.hydrogen_neutral
