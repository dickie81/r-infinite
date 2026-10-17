import Mathlib
import ThermalZeta
import BohrJoins
import CascadeLepton
import XiLogDeriv

/-! # Free radiation joined to the rest of the pilot (round 410)

Round 409 (ThermalZeta.lean) proved that a free massless Bose gas in `d` space dimensions has pressure
`T^{d+1} Λ(d+1)`, with `Λ = Γ_ℝ ζ`, and that the Maxwell–Boltzmann gas has `T^{d+1} Γ_ℝ(d+1)`. This file joins
those theorems to five earlier parts of the pilot. Every statement is an identity between existing definitions.

* **J1, the ball tower (round 184).** `pressureBoltz_eq_sphere`: `P_MB = T^{d+1} · 2/|S^d|`, the area of the unit
  sphere in `ℝ^{d+1}`. `pressureBoltz_six_lt`: among `d ≥ 1` the coefficient is smallest at `d = 6`, strictly
  (`D = 7`, BallTower's `sphereArea_lt_seven`). `pressureBose_eq_boltz_mul_zeta`: `P_BE = P_MB · ζ(d+1)`.
* **J2, the Bohr lift (round 398).** `pressureBose_eq_bohr`: `P_BE = T^{d+1} (2/|S^d|) exp(Σ_p p^{−(d+1)}) D₂(d+1)`,
  from BohrJoins' `completed_eq_sphereArea_bohr`.
* **J3, Binet and the cascade's lepton chain (rounds 155 and 406).** `phiB_eq_bose`: Binet's kernel
  `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2` is `bose s − 1/s + 1/2`. So round 155's Mittag-Leffler expansion is the
  Matsubara sum of the Bose occupation (`hasSum_bose_matsubara`), round 406's bounds on `φ` bound the occupation by
  its high-temperature expansion to order `s³` (`bose_highT_bounds`, with the coefficients `2ζ(2)/(2π)²` and
  `2ζ(4)/(2π)⁴` of `highT_coeffs`), and `ψ` is a Bose integral (`digamma_eq_bose_laplace`, `digamma_eq_bose`,
  `digamma_ofReal_bose`). For the definitions of CascadeLepton.lean: `psiR_eq_bose`, `psiR_eq_rpsi`,
  `pC_eq_logDeriv` (`p(d) = (log Γ_ℝ)′(d+1)`), `Nc_eq_sphereArea_ratio`, `Nc_eq_gammaR_ratio`
  (`N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)`), `Nc_eq_pressureBoltz` and `alphaC_eq` (`α(d) = N(d)²/4π`).
* **J4, Hadamard's product (rounds 8 and 9).** `hasProd_completed`: for `D ≠ 0, 1`,
  `∏_u (1 + (D − ½)²/u) = D(D − 1)Λ(D)/(2Ξ(0))`, over the zero family `u` of `Ξ(√w)` with multiplicity;
  `pressureBose_eq_tprod` writes the pressure that way.
* **J5, the explicit formula at the layers (round 156).** `hasSum_pC`: for `d ≥ 1`, with `z = d + ½`,
  `Σ_u 2z/(z² + u) = p(d) + 1/(d+1) + 1/d − Σ_n Λ(n) n^{−(d+1)}`, the paired form of Theorem 1b of
  `riemann-indistinguishability.md`; `pC_eq_tsum` is its displayed form and `hasSum_PhiC_window` its sum over a
  window of layers.
-/

open Real MeasureTheory Set ThermalZeta

noncomputable section

namespace ThermalJoins

/-! ## J1. The classical gas and the ball tower -/

section J1

variable (d : ℕ)

/-- **The Maxwell–Boltzmann pressure is twice the inverse sphere area:** `P_MB = T^{d+1} · 2/|S^d|`. -/
theorem pressureBoltz_eq_sphere (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    pressureBoltz d T = T ^ (d + 1) * (2 / BallTower.sphereArea (d + 1)) := by
  have h := pressureBoltz_eq d hd hT
  have hG := gammaR_eq_two_div_sphereArea (d + 1) (by omega)
  push_cast at hG
  rw [hG] at h
  exact_mod_cast h

/-- **The classical coefficient is least at `D = 7`:** for `d ≥ 1`, `d ≠ 6`, `P_MB(6, 1) < P_MB(d, 1)`. -/
theorem pressureBoltz_six_lt (hd : 1 ≤ d) (h6 : d ≠ 6) : pressureBoltz 6 1 < pressureBoltz d 1 := by
  rw [pressureBoltz_eq_sphere 6 (by norm_num) one_pos, pressureBoltz_eq_sphere d hd one_pos, one_pow,
    one_pow, one_mul, one_mul]
  exact div_lt_div_of_pos_left two_pos (BallTower.sphereArea_pos (by omega))
    (BallTower.sphereArea_lt_seven (d + 1) (by omega))

/-- **Bose = Boltzmann × ζ:** `P_BE = P_MB · ζ(d+1)`. -/
theorem pressureBose_eq_boltz_mul_zeta (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBose d T : ℂ) = pressureBoltz d T * riemannZeta ((d : ℂ) + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 1 < ((d : ℂ) + 1).re := by simp; linarith
  rw [pressureBose_eq d hd hT, pressureBoltz_eq d hd hT, BallTower.completed_eq_Gammaℝ_mul hs]
  ring

end J1

/-! ## J2. The Bohr lift -/

/-- **The Bose pressure through the Bohr lift:**
`P_BE = T^{d+1} · (2/|S^d|) · exp(Σ_p p^{−(d+1)}) · D₂(d+1)`. -/
theorem pressureBose_eq_bohr (d : ℕ) (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBose d T : ℂ) = (T : ℂ) ^ (d + 1) * (2 / (BallTower.sphereArea (d + 1) : ℂ) *
      (Complex.exp (∑' p : Nat.Primes, BohrSphere.bohr ((d : ℂ) + 1) p) *
        Complex.exp (∑' p : Nat.Primes, BohrSphere.regTerm ((d : ℂ) + 1) p))) := by
  have h := BohrJoins.completed_eq_sphereArea_bohr (n := d + 1) (by omega)
  push_cast at h
  rw [pressureBose_eq d hd hT, h]

/-! ## J3. Binet's kernel is the Bose occupation -/

/-- **Binet's kernel is the Bose occupation less its two leading terms:** `φ(s) = 1/(eˢ − 1) − 1/s + 1/2`. -/
theorem phiB_eq_bose {s : ℝ} (hs : 0 < s) : PilotDigamma.phiB s = bose s - 1 / s + 1 / 2 := by
  have h1 : 1 < Real.exp s := by simpa using Real.exp_lt_exp.mpr hs
  have h2 : Real.exp s - 1 ≠ 0 := (sub_pos.mpr h1).ne'
  have h0 : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have h3 : 1 - (Real.exp s)⁻¹ = (Real.exp s - 1) / Real.exp s := by field_simp
  rw [PilotDigamma.phiB, bose, Real.exp_neg, h3]
  field_simp
  ring

/-- **The Matsubara sum** (round 155's `hasSum_phiB`): `1/(eˢ − 1) − 1/s + 1/2 = Σ_{n≥1} 2s/(s² + (2πn)²)`. -/
theorem hasSum_bose_matsubara {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ => 2 * s / (s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)) (bose s - 1 / s + 1 / 2) := by
  rw [← phiB_eq_bose hs]
  exact PilotDigamma.hasSum_phiB hs

/-- **Round 406's bounds are the high-temperature expansion of the Bose occupation:**
`1/s − 1/2 + s/12 − s³/720 ≤ 1/(eˢ − 1) ≤ 1/s − 1/2 + s/12` for `s > 0`. -/
theorem bose_highT_bounds {s : ℝ} (hs : 0 < s) :
    1 / s - 1 / 2 + s / 12 - s ^ 3 / 720 ≤ bose s ∧ bose s ≤ 1 / s - 1 / 2 + s / 12 := by
  have h1 := Electron.le_phiB hs
  have h2 := Electron.phiB_le hs
  rw [phiB_eq_bose hs] at h1 h2
  constructor <;> linarith

/-- The two coefficients are values of `ζ` at even integers: `1/12 = 2ζ(2)/(2π)²` and `1/720 = 2ζ(4)/(2π)⁴`. -/
theorem highT_coeffs :
    (1 / 12 : ℂ) = 2 * riemannZeta 2 / (2 * π) ^ 2 ∧
      (1 / 720 : ℂ) = 2 * riemannZeta 4 / (2 * π) ^ 4 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [riemannZeta_two, riemannZeta_four]
  constructor <;> field_simp <;> ring

/-- **`ψ` as a Laplace transform of the Bose occupation** (round 155's `digamma_eq_lap`):
`ψ(z) = log z − 1/(2z) − ∫₀^∞ e^{−zs} (1/(eˢ − 1) − 1/s + 1/2) ds` for `Re z > 0`. -/
theorem digamma_eq_bose_laplace {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / (2 * z)
      - ∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * ((bose s - 1 / s + 1 / 2 : ℝ) : ℂ) := by
  rw [PilotDigamma.digamma_eq_lap hz, PilotDigamma.lap]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  rw [phiB_eq_bose hs]

/-- **`ψ` as a Bose integral** (Binet's second formula, round 155):
`ψ(z) = log z − 1/(2z) − 2∫₀^∞ t · bose(2πt)/(t² + z²) dt` for `Re z > 0`. -/
theorem digamma_eq_bose {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / (2 * z)
      - 2 * ∫ t in Ioi (0 : ℝ), (t : ℂ) * (bose (2 * π * t) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
  have hI : (∫ t in Ioi (0 : ℝ),
      (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ))) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) * (bose (2 * π * t) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [bose]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  rw [PilotDigamma.binet hz, hI]

/-- On the positive axis `ψ` is the real Bose integral (realness alone is DigammaGauss's `digamma_ofReal`,
round 154). -/
theorem digamma_ofReal_bose {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((Real.log x - 1 / (2 * x)
      - 2 * ∫ t in Ioi (0 : ℝ), t * bose (2 * π * t) / (t ^ 2 + x ^ 2) : ℝ) : ℂ) := by
  have hI : (∫ t in Ioi (0 : ℝ), (t : ℂ) * (bose (2 * π * t) : ℂ) / ((t : ℂ) ^ 2 + (x : ℂ) ^ 2)) =
      ((∫ t in Ioi (0 : ℝ), t * bose (2 * π * t) / (t ^ 2 + x ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    push_cast
    ring
  rw [digamma_eq_bose (by simpa using hx), hI, ← Complex.ofReal_log hx.le]
  push_cast
  ring

/-- CascadeLepton's `psiR` (round 406) is the real Bose integral. -/
theorem psiR_eq_bose {x : ℝ} (hx : 0 < x) :
    Electron.psiR x = Real.log x - 1 / (2 * x)
      - 2 * ∫ t in Ioi (0 : ℝ), t * bose (2 * π * t) / (t ^ 2 + x ^ 2) := by
  rw [Electron.psiR, digamma_ofReal_bose hx, Complex.ofReal_re]

/-- CascadeLepton's `psiR` (round 406) is DigammaGauss's real digamma `rpsi = (log Γ)′` (round 154). -/
theorem psiR_eq_rpsi {x : ℝ} (hx : 0 < x) : Electron.psiR x = PilotDigamma.rpsi x := by
  rw [Electron.psiR, PilotDigamma.digamma_ofReal hx, Complex.ofReal_re]

lemma digamma_ofReal_eq_psiR {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = (Electron.psiR x : ℂ) := by
  rw [psiR_eq_rpsi hx, PilotDigamma.digamma_ofReal hx]

/-- **The potential is the dimension derivative of the classical gas:** `p(d) = (log Γ_ℝ)′(d+1)` for
CascadeLepton's `pC` (round 406), the logarithmic derivative of `pressureBoltz_eq`'s coefficient `Γ_ℝ(D)` at
`D = d + 1`. -/
theorem pC_eq_logDeriv (d : ℕ) :
    (Electron.pC d : ℂ) = logDeriv Complex.Gammaℝ ((d : ℂ) + 1) := by
  have hx : (0 : ℝ) < ((d : ℝ) + 1) / 2 := by positivity
  have e : ((d : ℂ) + 1) / 2 = ((((d : ℝ) + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Pilot1ca.logDeriv_Gammaℝ (by simp; positivity), e, digamma_ofReal_eq_psiR hx, Electron.pC]
  push_cast
  ring

/-- `N(d) = |S^{d+1}|/|S^d|` for CascadeLepton's lapse `Nc` (round 406). -/
theorem Nc_eq_sphereArea_ratio (d : ℕ) :
    Electron.Nc d = BallTower.sphereArea (d + 2) / BallTower.sphereArea (d + 1) := by
  have h1 : Real.Gamma (((d : ℝ) + 1) / 2 + 1) = ((d : ℝ) + 1) / 2 * Real.Gamma (((d : ℝ) + 1) / 2) :=
    Real.Gamma_add_one (by positivity)
  have h2 : Real.Gamma (((d : ℝ) + 2) / 2 + 1) = ((d : ℝ) + 2) / 2 * Real.Gamma (((d : ℝ) + 2) / 2) :=
    Real.Gamma_add_one (by positivity)
  have g1 : Real.Gamma (((d : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g2 : Real.Gamma (((d : ℝ) + 2) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hs : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  simp only [Electron.Nc, Electron.Rc, BallTower.sphereArea, BallTower.ballVol]
  push_cast
  rw [h1, h2, show d + 2 = (d + 1) + 1 by ring, pow_succ (√π) (d + 1)]
  field_simp

/-- **The paper's Theorem 1 coupling:** `N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)` for CascadeLepton's `Nc`. -/
theorem Nc_eq_gammaR_ratio (d : ℕ) :
    (Electron.Nc d : ℂ) = Complex.Gammaℝ ((d : ℂ) + 1) / Complex.Gammaℝ ((d : ℂ) + 2) := by
  have h1 := gammaR_eq_two_div_sphereArea (d + 1) (by omega)
  have h2 := gammaR_eq_two_div_sphereArea (d + 2) (by omega)
  push_cast at h1 h2
  have s1 : (BallTower.sphereArea (d + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (BallTower.sphereArea_pos (by omega)).ne'
  have s2 : (BallTower.sphereArea (d + 2) : ℂ) ≠ 0 := by
    exact_mod_cast (BallTower.sphereArea_pos (by omega)).ne'
  rw [h1, h2, Nc_eq_sphereArea_ratio]
  push_cast
  field_simp

/-- **The coupling is a ratio of classical gases:** `N(d) = P_MB(d, 1)/P_MB(d + 1, 1)`. -/
theorem Nc_eq_pressureBoltz (d : ℕ) (hd : 1 ≤ d) :
    Electron.Nc d = pressureBoltz d 1 / pressureBoltz (d + 1) 1 := by
  rw [pressureBoltz_eq_sphere d hd one_pos, pressureBoltz_eq_sphere (d + 1) (by omega) one_pos,
    one_pow, one_pow, one_mul, one_mul, Nc_eq_sphereArea_ratio, show d + 1 + 1 = d + 2 from rfl]
  have s1 := (BallTower.sphereArea_pos (n := d + 1) (by omega)).ne'
  have s2 := (BallTower.sphereArea_pos (n := d + 2) (by omega)).ne'
  field_simp

/-- **The paper's Theorem 1 compliance:** `α(d) = N(d)²/4π` for CascadeLepton's `alphaC = R(d)²/4`. -/
theorem alphaC_eq (d : ℕ) : Electron.alphaC d = Electron.Nc d ^ 2 / (4 * π) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [Electron.alphaC, Electron.Nc, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  field_simp

/-! ## J4. The completed zeta function as a product over the zero pairs -/

/-- **Hadamard at a dimension:** for `D ≠ 0, 1`, `∏_u (1 + (D − ½)²/u) = D(D − 1)Λ(D)/(2Ξ(0))`, over the zero
family `u` of `Ξ(√w)` with multiplicity: round 8's `hadamardW_Xi`, with round 9's inputs, at `t = −i(D − ½)`. -/
theorem hasProd_completed {D : ℂ} (h0 : D ≠ 0) (h1 : D ≠ 1) :
    HasProd (fun i : Pilot1ca.ZeroIdx (Pilot1ca.sqF Pilot1ca.Xi) => 1 + (D - 1 / 2) ^ 2 / i.1)
      (D * (D - 1) * completedRiemannZeta D / (2 * Pilot1ca.Xi 0)) := by
  have h := (Pilot1ca.hadamardW_Xi Pilot1ca.xiGrowth Pilot1ca.Xi_zero_ne_zero).prod
    (-Complex.I * (D - 1 / 2))
  have hz : Pilot1ca.Xi (-Complex.I * (D - 1 / 2)) = Pilot1ca.xi D := by
    simp only [Pilot1ca.Xi]
    congr 1
    linear_combination (-(D - 1 / 2)) * Complex.I_sq
  have hsq : (-Complex.I * (D - 1 / 2)) ^ 2 = -(D - 1 / 2) ^ 2 := by
    linear_combination (D - 1 / 2) ^ 2 * Complex.I_sq
  rw [hz, Pilot1ca.xi_eq h0 h1, hsq] at h
  convert h using 1
  · funext i
    rw [div_eq_mul_inv]
    ring
  · ring

/-- **The Bose pressure as a product over the zero pairs:**
`P_BE = T^{d+1} · 2Ξ(0)/(d(d+1)) · ∏_u (1 + (d + ½)²/u)` for `d ≥ 1`. -/
theorem pressureBose_eq_tprod (d : ℕ) (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBose d T : ℂ) = (T : ℂ) ^ (d + 1) * (2 * Pilot1ca.Xi 0 / ((d : ℂ) * ((d : ℂ) + 1)) *
      ∏' i : Pilot1ca.ZeroIdx (Pilot1ca.sqF Pilot1ca.Xi), (1 + ((d : ℂ) + 1 / 2) ^ 2 / i.1)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero d
  have hX := Pilot1ca.Xi_zero_ne_zero
  have h := hasProd_completed (D := (d : ℂ) + 1) hd1 (by simpa using hd0)
  rw [show (d : ℂ) + 1 - 1 / 2 = (d : ℂ) + 1 / 2 by ring] at h
  rw [h.tprod_eq, pressureBose_eq d hd hT]
  field_simp
  ring

/-! ## J5. Theorem 1b at the layers -/

/-- **Theorem 1b at the layers, paired form.** For `d ≥ 1`, with `z = d + ½`,
`Σ_u 2z/(z² + u) = p(d) + 1/(d+1) + 1/d − Σ_n Λ(n) n^{−(d+1)}`, over the zero family `u` of `Ξ(√w)` with
multiplicity: round 156's `hasSum_logDeriv_Xi` and `logDeriv_Xi_eq` at `t = −iz`, with `pC_eq_logDeriv`. -/
theorem hasSum_pC (d : ℕ) (hd : 1 ≤ d) :
    HasSum (fun i : Pilot1ca.ZeroIdx (Pilot1ca.sqF Pilot1ca.Xi) =>
        2 * ((d : ℂ) + 1 / 2) / (((d : ℂ) + 1 / 2) ^ 2 + i.1))
      ((Electron.pC d : ℂ) + 1 / ((d : ℂ) + 1) + 1 / (d : ℂ)
        - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((d : ℂ) + 1)) := by
  have hs : 1 / 2 + Complex.I * (-Complex.I * ((d : ℂ) + 1 / 2)) = (d : ℂ) + 1 := by
    linear_combination (-((d : ℂ) + 1 / 2)) * Complex.I_sq
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre : 1 < (1 / 2 + Complex.I * (-Complex.I * ((d : ℂ) + 1 / 2))).re := by
    rw [hs]; simp; linarith
  have hXi : Pilot1ca.Xi (-Complex.I * ((d : ℂ) + 1 / 2)) ≠ 0 :=
    Pilot1ca.xi_ne_zero_of_one_le_re hre.le
  have h := (Pilot1ca.hasSum_logDeriv_Xi hXi).mul_left (-Complex.I)
  rw [Pilot1ca.logDeriv_Xi_eq hre, hs] at h
  have hp : (Electron.pC d : ℂ) =
      -(Real.log π : ℂ) / 2 + Complex.digamma (((d : ℂ) + 1) / 2) / 2 := by
    rw [pC_eq_logDeriv, Pilot1ca.logDeriv_Gammaℝ (by simp; positivity)]
  convert h using 1
  · funext i
    have hden : (-Complex.I * ((d : ℂ) + 1 / 2)) ^ 2 - i.1 = -(((d : ℂ) + 1 / 2) ^ 2 + i.1) := by
      linear_combination ((d : ℂ) + 1 / 2) ^ 2 * Complex.I_sq
    rw [hden, div_neg]
    linear_combination (2 * ((d : ℂ) + 1 / 2) / (((d : ℂ) + 1 / 2) ^ 2 + i.1)) * Complex.I_sq
  · rw [hp]
    linear_combination (1 / ((d : ℂ) + 1) + 1 / (d : ℂ) - (Real.log π : ℂ) / 2
      + Complex.digamma (((d : ℂ) + 1) / 2) / 2
      - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((d : ℂ) + 1)) * Complex.I_sq

/-- Theorem 1b's displayed form: `p(d) = Σ_u 2z/(z² + u) − 1/(d+1) − 1/d + Σ_n Λ(n) n^{−(d+1)}`. -/
theorem pC_eq_tsum (d : ℕ) (hd : 1 ≤ d) :
    (Electron.pC d : ℂ) = (∑' i : Pilot1ca.ZeroIdx (Pilot1ca.sqF Pilot1ca.Xi),
        2 * ((d : ℂ) + 1 / 2) / (((d : ℂ) + 1 / 2) ^ 2 + i.1))
      - 1 / ((d : ℂ) + 1) - 1 / (d : ℂ)
      + LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((d : ℂ) + 1) := by
  rw [(hasSum_pC d hd).tsum_eq]
  ring

/-- **A window of layers:** `Φ(b) − Φ(a) = Σ_u Σ_{a<d≤b} 2z_d/(z_d² + u) − Σ_{a<d≤b} (1/(d+1) + 1/d)
+ Σ_{a<d≤b} Σ_n Λ(n) n^{−(d+1)}`, with `z_d = d + ½`, for `4 ≤ a ≤ b`. -/
theorem hasSum_PhiC_window {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) :
    HasSum (fun i : Pilot1ca.ZeroIdx (Pilot1ca.sqF Pilot1ca.Xi) =>
        ∑ d ∈ Finset.Ioc a b, 2 * ((d : ℂ) + 1 / 2) / (((d : ℂ) + 1 / 2) ^ 2 + i.1))
      (((Electron.PhiC b - Electron.PhiC a : ℝ) : ℂ) + ∑ d ∈ Finset.Ioc a b,
        (1 / ((d : ℂ) + 1) + 1 / (d : ℂ)
          - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((d : ℂ) + 1))) := by
  rw [Electron.PhiC_sub ha hab]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine hasSum_sum (fun d hd => ?_)
  have hd1 : 1 ≤ d := by
    rw [Finset.mem_Ioc] at hd
    omega
  convert hasSum_pC d hd1 using 1
  ring

end ThermalJoins

#print axioms ThermalJoins.pressureBoltz_eq_sphere
#print axioms ThermalJoins.pressureBoltz_six_lt
#print axioms ThermalJoins.pressureBose_eq_boltz_mul_zeta
#print axioms ThermalJoins.pressureBose_eq_bohr
#print axioms ThermalJoins.phiB_eq_bose
#print axioms ThermalJoins.hasSum_bose_matsubara
#print axioms ThermalJoins.bose_highT_bounds
#print axioms ThermalJoins.highT_coeffs
#print axioms ThermalJoins.digamma_eq_bose_laplace
#print axioms ThermalJoins.digamma_eq_bose
#print axioms ThermalJoins.digamma_ofReal_bose
#print axioms ThermalJoins.psiR_eq_bose
#print axioms ThermalJoins.psiR_eq_rpsi
#print axioms ThermalJoins.pC_eq_logDeriv
#print axioms ThermalJoins.Nc_eq_sphereArea_ratio
#print axioms ThermalJoins.Nc_eq_gammaR_ratio
#print axioms ThermalJoins.Nc_eq_pressureBoltz
#print axioms ThermalJoins.alphaC_eq
#print axioms ThermalJoins.hasProd_completed
#print axioms ThermalJoins.pressureBose_eq_tprod
#print axioms ThermalJoins.hasSum_pC
#print axioms ThermalJoins.pC_eq_tsum
#print axioms ThermalJoins.hasSum_PhiC_window
