import HalfPlaneS0
import WeilTwinGeneral
import KaiserSplit

/-! # Joins on the half-plane side (round 279)

Round 278's `HalfPlaneS0.ne_zero_of_smoothBound` turns `SmoothBound θ` into `ζ(s) ≠ 0` and
`L(s, χ₋₃) ≠ 0` on `Re s > θ`. `SmoothBound θ` says the smoothed Möbius sums of
`ζ_{ℚ(√−3)} = ζ·L(·, χ₋₃)` satisfy `Σ_n μ_K(n)W(n/D) = O(D^{θ+ε})`. With the functional equations the
nontrivial zeros of both functions then lie in `1 − θ ≤ Re ρ ≤ θ` (`zeta_band`, `chi3_band`), and the
zeros `τ` of `Ξ` have `|Im τ| ≤ θ − ½` (`abs_im_tau_le`). The stack's sockets for a fixed zero-free
strip then give, under `SmoothBound θ` with `θ ≥ ½`:
* the twin form of `ζ` has a negative part of exponential rate at most `2θ − 1`
  (`weil_rate_of_smoothBound`, through `weil_twins_rate`);
* the same for `L(s, χ₋₃)` (`chi3_rate_of_smoothBound`, through `twins_rate`) and for the twin form
  `2Q_ζ + Q_{χ₋₃}` of `ζ·ζ_{ℚ(√−3)}` (`QK3_rate_of_smoothBound`, through `QKχ_twins_rate`);
* round 164's prefactor: `λ₁(a) ≤ K(a + 1)e^{(8 + 2θ)a − 4πe^{2a}}` (`lam_prefactor_of_smoothBound`,
  through `Kaiser.lam_le_split`). Unconditionally the exponent is `10a` (`lam_prefactor`), less a
  Korobov–Vinogradov saving `c·a^{1/3}/(log a)^{1/3}` in `external/pnt` (`lam_prefactor_KV`).

`SmoothBound θ` stays a displayed hypothesis: no instance with `θ < 1` is proved.
-/

open Complex
open Pilot1ca Pilot1bt PilotWeil PsiOmega HalfPlaneS0

namespace HalfPlaneJoins

/-- Under `SmoothBound θ`, every nontrivial zero of `ζ` has `1 − θ ≤ Re ρ ≤ θ`. -/
theorem zeta_band {θ : ℝ} (h : SmoothBound θ) {s : ℂ} (hs : IsNontrivialZero s) :
    |2 * s.re - 1| ≤ 2 * θ - 1 := by
  have h1 : s.re ≤ θ := by
    by_contra hc; exact (ne_zero_of_smoothBound h (not_le.1 hc)).1 hs.1
  have h2 : (1 - s).re ≤ θ := by
    by_contra hc
    exact (ne_zero_of_smoothBound h (not_le.1 hc)).1 (PsiOmega.IsNontrivialZero.one_sub hs).1
  rw [Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]; constructor <;> linarith

/-- Under `SmoothBound θ`, every zero of `L(s, χ₋₃)` in the critical strip has `1 − θ ≤ Re ρ ≤ θ`.
The lower bound uses the evenness of `Ξ(·, χ₋₃)` (`XiC_even`). -/
theorem chi3_band {θ : ℝ} (h : SmoothBound θ) {s : ℂ}
    (hs : DirichletCharacter.LFunction chi3 s = 0) (h0 : 0 < s.re) (_h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 2 * θ - 1 := by
  have u1 : s.re ≤ θ := by
    by_contra hc; exact (ne_zero_of_smoothBound h (not_le.1 hc)).2 hs
  have u2 : 1 - s.re ≤ θ := by
    by_contra hc
    set t := (s - 1 / 2) / I
    have hst : 1 / 2 + I * t = s := by simp only [t]; field_simp; ring
    have hXt : XiC chi3 t = 0 := by
      unfold XiC; rw [hst, LamG]; rw [completed_eq_mul h0, hs]; simp
    have hXn : XiC chi3 (-t) = 0 := by rw [XiC_even good_chi3]; exact hXt
    have hrefl : 1 / 2 + I * (-t) = 1 - s := by simp only [t]; field_simp; ring
    have hre : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hL : DirichletCharacter.LFunction chi3 (1 - s) = 0 := by
      refine LFunction_of_LamG hre ?_
      have e : XiC chi3 (-t) = LamG chi3 (1 - s) := by unfold XiC; rw [hrefl]
      rw [← e]; exact hXn
    have hgt : θ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact (ne_zero_of_smoothBound h hgt).2 hL
  rw [abs_le]; constructor <;> linarith

/-- **`ζ`'s twin form under `SmoothBound θ`**: `Q(twin (box 1) λ) ≥ −C e^{(2θ−1)λ}`. -/
theorem weil_rate_of_smoothBound {θ : ℝ} (h : SmoothBound θ) (hθ : 1 / 2 ≤ θ) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((2 * θ - 1) * l)) ≤ weilQ (l + 1) (twin (box 1) l) :=
  (weil_twins_rate (by linarith)).2 fun _ hs => zeta_band h hs

/-- **`L(s, χ₋₃)`'s twin form under `SmoothBound θ`**: rate at most `2θ − 1`. -/
theorem chi3_rate_of_smoothBound {θ : ℝ} (h : SmoothBound θ) (hθ : 1 / 2 ≤ θ) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((2 * θ - 1) * l)) ≤ QC chi3 (l + 1) (twin (box 1) l) :=
  (twins_rate good_chi3 WeilTwinGeneral.hS3 (by linarith)).2 fun _ hs h0 h1 => chi3_band h hs h0 h1

/-- **The twin form `2Q_ζ + Q_{χ₋₃}` of `ζ·ζ_{ℚ(√−3)}` under `SmoothBound θ`**: rate at most
`2θ − 1`. -/
theorem QK3_rate_of_smoothBound {θ : ℝ} (h : SmoothBound θ) (hθ : 1 / 2 ≤ θ) :
    ∃ C, ∀ l : ℝ, 0 ≤ l →
      -(C * Real.exp ((2 * θ - 1) * l)) ≤ WeilTwinGeneral.QKχ chi3 (l + 1) (twin (box 1) l) :=
  (WeilTwinGeneral.QKχ_twins_rate good_chi3 WeilTwinGeneral.hS3 (by linarith)).2
    ⟨fun _ hs => zeta_band h hs, fun _ hs h0 h1 => chi3_band h hs h0 h1⟩

/-- Under `SmoothBound θ`, every zero `τ` of `Ξ` has `|Im τ| ≤ θ − ½`. -/
theorem abs_im_tau_le {θ : ℝ} (h : SmoothBound θ) (i : ZeroIdx (sqF Xi)) :
    |(tau i).im| ≤ θ - 1 / 2 := by
  set s : ℂ := 1 / 2 + I * tau i
  have hs : IsNontrivialZero s := by
    rw [nontrivial_iff_Xi]
    have e : (s - 1 / 2) / I = tau i := by simp only [s]; field_simp; ring
    rw [e]; exact Xi_tau i
  have hb := zeta_band h hs
  have e : s.re = 1 / 2 - (tau i).im := by simp only [s]; simp; ring
  rw [e, show 2 * (1 / 2 - (tau i).im) - 1 = -(2 * (tau i).im) by ring, abs_neg, abs_mul,
    abs_two] at hb
  linarith

/-- **Round 164's prefactor under `SmoothBound θ`**: `λ₁(a) ≤ K(a + 1)e^{(8 + 2θ)a − 4πe^{2a}}` for
`a ≥ 4`. Every zero gets the weight `e^{2a|Im τ|} ≤ e^{(2θ−1)a}` in `Kaiser.lam_le_split`. -/
theorem lam_prefactor_of_smoothBound {θ : ℝ} (h : SmoothBound θ) (hθ : 1 / 2 ≤ θ) :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a →
      lam a ≤ K * (a + 1) * Real.exp ((8 + 2 * θ) * a - 4 * Real.pi * Real.exp (2 * a)) := by
  obtain ⟨K, hK, hlam⟩ := Kaiser.lam_le_split
  refine ⟨K, hK, fun a ha => ?_⟩
  have hk : 1 ≤ Real.exp ((2 * θ - 1) * a) := Real.one_le_exp (by nlinarith)
  have := hlam a ha _ hk fun i _ => by
    apply Real.exp_le_exp.2
    have := abs_im_tau_le h i
    nlinarith
  calc lam a ≤ K * (a + 1) * Real.exp ((2 * θ - 1) * a) *
        Real.exp (9 * a - 4 * Real.pi * Real.exp (2 * a)) := this
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

end HalfPlaneJoins

#print axioms HalfPlaneJoins.zeta_band
#print axioms HalfPlaneJoins.chi3_band
#print axioms HalfPlaneJoins.weil_rate_of_smoothBound
#print axioms HalfPlaneJoins.chi3_rate_of_smoothBound
#print axioms HalfPlaneJoins.QK3_rate_of_smoothBound
#print axioms HalfPlaneJoins.abs_im_tau_le
#print axioms HalfPlaneJoins.lam_prefactor_of_smoothBound
