import Mathlib
import ThermalJoins

/-! # Part 0's distinguished dimensions (round 411)

Part 0 (`src/cascade-series-part0.tex`) defines the sphere-area decay rate
`p(d) = −½ log π + ½ψ((d+1)/2)` and selects its distinguished dimensions with it. This file proves the
computational statements, for every real `x > −1` and every integer `d`. CascadeLepton's `pC` is `p` at the
integers (`pR_natCast`).

* **`p` is the decay rate of the sphere area** (`hasDerivAt_log_OmR`): `d/dx log Ω(x) = −p(x)` for
  `Ω(x) = 2π^{(x+1)/2}/Γ((x+1)/2)`, which is BallTower's `sphereArea (d+1)` at the integers (`OmR_natCast`).
* **`p` is strictly increasing and continuous** on `x > −1` (`pR_strictMonoOn`, `pR_continuousOn`), from
  `ψ(y) − ψ(x) ≥ 1/x − 1/y` for `0 < x ≤ y` (`rpsi_sub_ge`).
* **The natural zero** (`natural_zero`, `zero_unique`): `p(d) < 0` for `d ≤ 6` and `p(d) > 0` for `d ≥ 7`, and
  `p` has exactly one zero on `x > −1`, in `(6, 7)`. `Ω_6` is the largest sphere area (`Om_lt_six`); `Ω_d` rises
  strictly up to `d = 6` and falls strictly after it (`Om_unimodal`), the fall from `d = 7` on by the
  log-convexity of `Γ` (`Nc_lt_one`).
* **The thresholds** (`threshold_one`, `threshold_two`, `threshold_labels`, `threshold_one_unique`,
  `threshold_two_unique`): `p(19) < ½ log π < p(20)` and `p(217) < √π < p(218)`, and each level is reached
  exactly once on `x > −1`, in `(19, 20)` and `(217, 218)`. `e^{½ log π} = √π` (`exp_c1`), and
  `log(½ log π) < 0` is not a value of `p` at any `d ≥ 7` (`log_c1_neg`).
* **The invariant** (`cascadeInv_eq`, `cascadeInv_closed`, `cascadeInv_max`, `cascadeInv_bounds`):
  `(Ω_5/Ω_7)² Ω_19 Ω_217 = (9/π²) Ω_19 Ω_217 = 36π^{117}/(9!·108!)`, the strict maximum of `(Ω_5/Ω_a)² Ω_b Ω_c`
  over `(a, b, c) ∈ {6,7} × {19,20} × {217,218}`, between `1.0989 × 10⁻¹²⁰` and `1.0990 × 10⁻¹²⁰`.

Inputs: round 406's closed forms of `pC` and its enclosure of Euler's constant, round 154's `rpsi` with its
monotonicity and shift formula, round 410's `psiR_eq_rpsi` and `Nc_eq_sphereArea_ratio`, BallTower (round 184),
Mathlib's bounds on `π`, `log 2` and `e`, and Mathlib's log-convexity of `Γ`. Part 0's arguments that classify
which constants and which operations count (its theorems "Uniqueness of `c₁`", "Two canonical values",
"Tower completeness" and "Cascade invariant") are not formalized here.
-/

open Real Set Finset

noncomputable section

namespace Part0

/-! ## The potential in a continuous dimension -/

/-- `p(x) = ½ψ((x+1)/2) − ½ log π` for real `x`, with DigammaGauss's real digamma `rpsi`. -/
def pR (x : ℝ) : ℝ := PilotDigamma.rpsi ((x + 1) / 2) / 2 - Real.log π / 2

theorem pR_natCast (d : ℕ) : pR d = Electron.pC d := by
  rw [pR, Electron.pC, ThermalJoins.psiR_eq_rpsi (by positivity)]

/-- `ψ(y) − ψ(x) ≥ 1/x − 1/y` for `0 < x ≤ y`, from `rpsi_mono` and `ψ(t+1) = ψ(t) + 1/t`. -/
theorem rpsi_sub_ge {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    1 / x - 1 / y ≤ PilotDigamma.rpsi y - PilotDigamma.rpsi x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h := PilotDigamma.rpsi_mono (show (0 : ℝ) < x + 1 by linarith)
    (show (0 : ℝ) < y + 1 by linarith) (by linarith : x + 1 ≤ y + 1)
  have ex := PilotDigamma.rpsi_add_nat hx 1
  have ey := PilotDigamma.rpsi_add_nat hy 1
  simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at ex ey
  linarith

/-- **`ψ` is strictly increasing on `(0, ∞)`.** -/
theorem rpsi_strictMonoOn : StrictMonoOn PilotDigamma.rpsi (Ioi 0) := by
  intro x hx y _ hxy
  have h := rpsi_sub_ge hx hxy.le
  have : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  linarith

theorem rpsi_continuousOn : ContinuousOn PilotDigamma.rpsi (Ioi 0) := by
  have h : ContinuousOn (fun x : ℝ => (Complex.digamma (x : ℂ)).re) (Ioi 0) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine PilotDigamma.differentiableOn_digamma.continuousOn.comp
      Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    show 0 < (x : ℂ).re
    simpa using hx
  refine h.congr (fun x hx => ?_)
  show PilotDigamma.rpsi x = (Complex.digamma (x : ℂ)).re
  rw [PilotDigamma.digamma_ofReal hx, Complex.ofReal_re]

/-- **`p` is strictly increasing** on `x > −1`. -/
theorem pR_strictMonoOn : StrictMonoOn pR (Ioi (-1)) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < (x + 1) / 2 := by have : (-1 : ℝ) < x := hx; linarith
  have hy' : (0 : ℝ) < (y + 1) / 2 := by have : (-1 : ℝ) < y := hy; linarith
  have := rpsi_strictMonoOn hx' hy' (by linarith)
  unfold pR
  linarith

theorem pR_continuousOn : ContinuousOn pR (Ioi (-1)) := by
  have h : ContinuousOn (fun x : ℝ => (x + 1) / 2) (Ioi (-1)) := by fun_prop
  have h2 := rpsi_continuousOn.comp h (fun x hx => by
    show (0 : ℝ) < (x + 1) / 2
    have : (-1 : ℝ) < x := hx
    linarith)
  exact (h2.div_const 2).sub continuousOn_const

/-- A crossing of a level `c` between `a < b` exists, lies strictly between them, and is the only
solution of `p(x) = c` on `x > −1`. -/
theorem exists_unique_cross {c a b : ℝ} (ha : -1 < a) (hab : a < b) (hlo : pR a < c)
    (hhi : c < pR b) : ∃ x ∈ Ioo a b, pR x = c ∧ ∀ y, -1 < y → pR y = c → y = x := by
  have hcont : ContinuousOn pR (Icc a b) :=
    pR_continuousOn.mono (fun y hy => lt_of_lt_of_le ha hy.1)
  obtain ⟨x, hx, hxc⟩ := intermediate_value_Icc hab.le hcont ⟨hlo.le, hhi.le⟩
  have hxa : x ≠ a := fun h => by rw [h] at hxc; linarith
  have hxb : x ≠ b := fun h => by rw [h] at hxc; linarith
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩, hxc, fun y hy hyc => ?_⟩
  exact pR_strictMonoOn.injOn hy (show (-1 : ℝ) < x from lt_of_lt_of_le ha hx.1)
    (hyc.trans hxc.symm)

/-! ## The decay rate of the sphere area -/

/-- `Ω(x) = 2π^{(x+1)/2}/Γ((x+1)/2)`, the area of the unit sphere `S^x`, in a continuous dimension. -/
def OmR (x : ℝ) : ℝ := 2 * π ^ ((x + 1) / 2) / Real.Gamma ((x + 1) / 2)

theorem OmR_natCast (d : ℕ) : OmR d = BallTower.sphereArea (d + 1) := by
  have ht : (0 : ℝ) < ((d : ℝ) + 1) / 2 := by positivity
  have hG := Real.Gamma_add_one ht.ne'
  have hΓ : 0 < Real.Gamma (((d : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos ht
  have hsq : √π ^ (d + 1) = π ^ (((d : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    push_cast; ring_nf
  unfold OmR BallTower.sphereArea BallTower.ballVol
  push_cast
  rw [hG, hsq]
  field_simp

/-- **`p` is the decay rate of the sphere area:** `d/dx log Ω(x) = −p(x)` for `x > −1`. -/
theorem hasDerivAt_log_OmR {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y => Real.log (OmR y)) (-pR x) x := by
  set t := (x + 1) / 2 with ht_def
  have ht : 0 < t := by rw [ht_def]; linarith
  have hdG : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) t :=
    (Real.differentiableAt_Gamma (PilotDigamma.real_ne_neg_nat ht)).log
      (Real.Gamma_pos_of_pos ht).ne'
  have h1 : HasDerivAt (fun y : ℝ => (y + 1) / 2) (1 / 2) x := by
    simpa using ((hasDerivAt_id x).add_const 1).div_const 2
  have h2 : HasDerivAt (Real.log ∘ Real.Gamma) (PilotDigamma.rpsi t) t := hdG.hasDerivAt
  have h3 := h2.comp x h1
  have h4 : HasDerivAt (fun y : ℝ => Real.log 2 + (y + 1) / 2 * Real.log π
      - (Real.log ∘ Real.Gamma) ((y + 1) / 2)) (1 / 2 * Real.log π - PilotDigamma.rpsi t * (1 / 2)) x :=
    ((h1.mul_const (Real.log π)).const_add (Real.log 2)).sub h3
  have hev : (fun y : ℝ => Real.log 2 + (y + 1) / 2 * Real.log π
      - (Real.log ∘ Real.Gamma) ((y + 1) / 2)) =ᶠ[nhds x] fun y => Real.log (OmR y) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    have hy' : 0 < (y + 1) / 2 := by linarith
    have hΓ : 0 < Real.Gamma ((y + 1) / 2) := Real.Gamma_pos_of_pos hy'
    have hpow : 0 < π ^ ((y + 1) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    simp only [OmR, Function.comp]
    rw [Real.log_div (by positivity) hΓ.ne', Real.log_mul (by norm_num) hpow.ne',
      Real.log_rpow Real.pi_pos]
  have := h4.congr_of_eventuallyEq hev.symm
  convert this using 1
  rw [pR, ← ht_def]
  ring

/-! ## `log π` -/

theorem log_pi_gt : (1.1447 : ℝ) < Real.log π := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h := Electron.exp_le_of (x := 1.1447) 1 8 (by norm_num) 0.1447 (by norm_num) (by norm_num)
    (by norm_num)
  refine lt_of_le_of_lt h (lt_trans ?_ Real.pi_gt_d6)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem log_pi_lt : Real.log π < 1.1448 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h := Electron.exp_ge_of (x := 1.1448) 1 8 0.1448 (by norm_num) (by norm_num)
  refine lt_of_lt_of_le (lt_trans Real.pi_lt_d6 ?_) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-! ## The natural zero `d₀ = 7` -/

theorem pC_six_neg : Electron.pC 6 < 0 := by
  rw [show Electron.pC 6 = _ from Electron.pC_even 3]
  have hs : ∑ j ∈ Finset.range 3, 1 / ((j : ℝ) + 1 / 2) = 46 / 15 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hs]
  have := Electron.eulerMascheroni_bounds
  have := Real.log_two_gt_d9
  have := log_pi_gt
  linarith

theorem pC_seven_pos : 0 < Electron.pC 7 := by
  rw [show Electron.pC 7 = _ from Electron.pC_odd 3]
  have h3 : (harmonic 3 : ℝ) = 11 / 6 := by
    have : harmonic 3 = 11 / 6 := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    rw [this]; push_cast; ring
  rw [h3]
  have := Electron.eulerMascheroni_bounds
  have := log_pi_lt
  linarith

theorem pC_le_of_le {a b : ℕ} (h : a ≤ b) : Electron.pC a ≤ Electron.pC b := by
  rw [← pR_natCast, ← pR_natCast]
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  exact pR_strictMonoOn.monotoneOn (show (-1 : ℝ) < a by linarith)
    (show (-1 : ℝ) < b by linarith) (by exact_mod_cast h)

/-- **The natural zero (Part 0's Definition and Theorem "Dual characterisation", (a)):** `p(d) < 0` for
every integer `d ≤ 6` and `p(d) > 0` for every integer `d ≥ 7`. -/
theorem natural_zero : (∀ d : ℕ, d ≤ 6 → Electron.pC d < 0) ∧ (∀ d : ℕ, 7 ≤ d → 0 < Electron.pC d) :=
  ⟨fun _ hd => lt_of_le_of_lt (pC_le_of_le hd) pC_six_neg,
    fun _ hd => lt_of_lt_of_le pC_seven_pos (pC_le_of_le hd)⟩

/-- **The continuous zero** of `p` lies in `(6, 7)` and is the only zero on `x > −1`. -/
theorem zero_unique : ∃ x ∈ Ioo (6 : ℝ) 7, pR x = 0 ∧ ∀ y, -1 < y → pR y = 0 → y = x :=
  exists_unique_cross (by norm_num) (by norm_num)
    (by have := pR_natCast 6; push_cast at this; rw [this]; exact pC_six_neg)
    (by have := pR_natCast 7; push_cast at this; rw [this]; exact pC_seven_pos)

/-! ## The sphere areas `Ω_d = |S^d|` -/

/-- Part 0's `Ω_d`, the area of the unit sphere `S^d ⊂ ℝ^{d+1}`: BallTower's `sphereArea (d + 1)`. -/
abbrev Om (d : ℕ) : ℝ := BallTower.sphereArea (d + 1)

theorem Om_pos (d : ℕ) : 0 < Om d := BallTower.sphereArea_pos (by omega)

theorem Om_five : Om 5 = π ^ 3 := by
  show BallTower.sphereArea 6 = _
  unfold BallTower.sphereArea; rw [BallTower.ballVol_six]; push_cast; ring

theorem Om_six : Om 6 = 16 * π ^ 3 / 15 := by
  show BallTower.sphereArea 7 = _
  unfold BallTower.sphereArea; rw [BallTower.ballVol_seven]; push_cast; ring

theorem Om_seven : Om 7 = π ^ 4 / 3 := by
  show BallTower.sphereArea 8 = _
  unfold BallTower.sphereArea; rw [BallTower.ballVol_eight]; push_cast; ring

/-- **Dual characterisation (b):** `Ω_6` is the largest sphere area, so `d_max = 6 = d₀ − 1`. -/
theorem Om_lt_six (d : ℕ) (hd : d ≠ 6) : Om d < Om 6 :=
  BallTower.sphereArea_lt_seven (d + 1) (by omega)

/-- Part 0's evaluation: `Ω_5 = π³ < Ω_7 = π⁴/3 < Ω_6 = 16π³/15`. -/
theorem Om_five_lt_seven_lt_six : Om 5 < Om 7 ∧ Om 7 < Om 6 := by
  rw [Om_five, Om_six, Om_seven]
  have hπ := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have h3 : 0 < π ^ 3 := by positivity
  constructor <;> nlinarith

/-- **The lapse is below `1` from `d = 6` on**, by the log-convexity of `Γ`:
`N(d) ≤ √π·√((d+2)/2)/((d+1)/2) < 1` for `d ≥ 7`, and `N(6) = 5π/16`. -/
theorem Nc_lt_one (d : ℕ) (hd : 6 ≤ d) : Electron.Nc d < 1 := by
  rcases Nat.eq_or_lt_of_le hd with h | h
  · subst h
    rw [ThermalJoins.Nc_eq_sphereArea_ratio]
    have e7 := Om_seven
    have e6 := Om_six
    simp only [Om] at e7 e6
    rw [show (6 : ℕ) + 2 = 7 + 1 from rfl, show (6 : ℕ) + 1 = 6 + 1 from rfl, e7, e6]
    have hπ := Real.pi_pos
    have hπ2 := Real.pi_lt_d2
    rw [div_lt_one (by positivity)]
    nlinarith [pow_pos hπ 3]
  · set x : ℝ := ((d : ℝ) + 1) / 2 with hx_def
    have h7 : (7 : ℝ) ≤ d := by exact_mod_cast h
    have hx4 : 4 ≤ x := by rw [hx_def]; linarith
    have hx0 : 0 < x := by linarith
    have hs : 0 < x + 1 / 2 := by linarith
    -- log-convexity: `Γ(x+1)² ≤ Γ(x+½) Γ(x+3/2)`
    have hlc := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + 1 / 2) (t := x + 3 / 2)
      (a := 1 / 2) (b := 1 / 2) hs (by linarith) (by norm_num) (by norm_num) (by norm_num)
    have e1 : (1 / 2 : ℝ) * (x + 1 / 2) + 1 / 2 * (x + 3 / 2) = x + 1 := by ring
    rw [e1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul
      (Real.Gamma_pos_of_pos hs).le] at hlc
    have hG1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hsq := (Real.le_sqrt hG1.le (mul_pos (Real.Gamma_pos_of_pos hs)
      (Real.Gamma_pos_of_pos (by linarith))).le).mp hlc
    have e2 : Real.Gamma (x + 3 / 2) = (x + 1 / 2) * Real.Gamma (x + 1 / 2) := by
      rw [show x + 3 / 2 = (x + 1 / 2) + 1 by ring, Real.Gamma_add_one hs.ne']
    have e3 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0.ne'
    rw [e2, e3] at hsq
    have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
    have hGh : 0 < Real.Gamma (x + 1 / 2) := Real.Gamma_pos_of_pos hs
    -- `N(d) = √π Γ(x)/Γ(x+½)`
    have hN : Electron.Nc d = √π * (Real.Gamma x / Real.Gamma (x + 1 / 2)) := by
      rw [Electron.Nc, Electron.Rc, hx_def]
      congr 2
      ring_nf
    have hNpos : 0 < Electron.Nc d := by rw [hN]; positivity
    have hN2 : Electron.Nc d ^ 2 = π * (Real.Gamma x / Real.Gamma (x + 1 / 2)) ^ 2 := by
      rw [hN, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    have hπ := Real.pi_lt_d2
    have hratio : (Real.Gamma x / Real.Gamma (x + 1 / 2)) ^ 2 ≤ (x + 1 / 2) / x ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hlt : π * ((x + 1 / 2) / x ^ 2) < 1 := by
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      nlinarith
    have hsq1 : Electron.Nc d ^ 2 < 1 := by
      rw [hN2]
      calc π * (Real.Gamma x / Real.Gamma (x + 1 / 2)) ^ 2 ≤ π * ((x + 1 / 2) / x ^ 2) :=
            mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
        _ < 1 := hlt
    nlinarith

/-- **The sphere area increases strictly up to `S^6`:** `Ω_d < Ω_{d+1}` for `d ≤ 5`. -/
theorem Om_lt_succ (d : ℕ) (hd : d ≤ 5) : Om d < Om (d + 1) := by
  have hπ := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  interval_cases d <;> simp only [Om, BallTower.sphereArea] <;> push_cast
  · rw [BallTower.ballVol_one, BallTower.ballVol_two]; nlinarith
  · rw [BallTower.ballVol_two, BallTower.ballVol_three]; nlinarith
  · rw [BallTower.ballVol_three, BallTower.ballVol_four]; nlinarith
  · rw [BallTower.ballVol_four, BallTower.ballVol_five]; nlinarith
  · rw [BallTower.ballVol_five, BallTower.ballVol_six]; nlinarith [pow_pos hπ0 2]
  · rw [BallTower.ballVol_six, BallTower.ballVol_seven]; nlinarith [pow_pos hπ0 3]

/-- **The sphere area decreases strictly from `S^6` on:** `Ω_{d+1} < Ω_d` for `d ≥ 6`. -/
theorem Om_succ_lt (d : ℕ) (hd : 6 ≤ d) : Om (d + 1) < Om d := by
  have h := Nc_lt_one d hd
  rw [ThermalJoins.Nc_eq_sphereArea_ratio, div_lt_one (BallTower.sphereArea_pos (by omega))] at h
  simpa [Om] using h

/-- **`Ω` is unimodal with its peak at `S^6`.** -/
theorem Om_unimodal : (∀ d : ℕ, d ≤ 5 → Om d < Om (d + 1)) ∧ (∀ d : ℕ, 6 ≤ d → Om (d + 1) < Om d) :=
  ⟨Om_lt_succ, Om_succ_lt⟩

/-! ## The thresholds `d₁ = 19` and `d₂ = 217` -/

/-- **Two thresholds, `c₁`:** `p(19) < ½ log π < p(20)`. -/
theorem threshold_one : Electron.pC 19 < Real.log π / 2 ∧ Real.log π / 2 < Electron.pC 20 := by
  have g := Electron.eulerMascheroni_bounds
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have p1 := log_pi_gt
  have p2 := log_pi_lt
  constructor
  · rw [show Electron.pC 19 = _ from Electron.pC_odd 9]
    have h9 : (harmonic 9 : ℝ) = 7129 / 2520 := by
      have : harmonic 9 = 7129 / 2520 := by
        simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
      rw [this]; push_cast; ring
    rw [h9]
    linarith
  · rw [show Electron.pC 20 = _ from Electron.pC_even 10]
    have hs : (4.26651 : ℝ) < ∑ j ∈ Finset.range 10, 1 / ((j : ℝ) + 1 / 2) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    linarith

/-- **Two thresholds, `c₂`:** `p(217) < √π < p(218)`. -/
theorem threshold_two : Electron.pC 217 < √π ∧ √π < Electron.pC 218 := by
  have g := Electron.eulerMascheroni_bounds
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have p1 := log_pi_gt
  have p2 := log_pi_lt
  have s1 := Electron.sqrt_pi_gt
  have s2 := Electron.sqrt_pi_lt
  constructor
  · rw [show Electron.pC 217 = _ from Electron.pC_odd 108]
    have hq : harmonic 108 < (526397 / 100000 : ℚ) := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    have h : (harmonic 108 : ℝ) < 526397 / 100000 := by
      have := (Rat.cast_lt (K := ℝ)).mpr hq
      push_cast at this
      exact this
    linarith
  · rw [show Electron.pC 218 = _ from Electron.pC_even 109]
    have hs : (6.65486 : ℝ) < ∑ j ∈ Finset.range 109, 1 / ((j : ℝ) + 1 / 2) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    linarith

/-- The integer labels: `p(d) < ½ log π` exactly for `d ≤ 19`, and `p(d) < √π` exactly for `d ≤ 217`. -/
theorem threshold_labels :
    (∀ d : ℕ, d ≤ 19 → Electron.pC d < Real.log π / 2) ∧
    (∀ d : ℕ, 20 ≤ d → Real.log π / 2 < Electron.pC d) ∧
    (∀ d : ℕ, d ≤ 217 → Electron.pC d < √π) ∧
    (∀ d : ℕ, 218 ≤ d → √π < Electron.pC d) :=
  ⟨fun _ hd => lt_of_le_of_lt (pC_le_of_le hd) threshold_one.1,
    fun _ hd => lt_of_lt_of_le threshold_one.2 (pC_le_of_le hd),
    fun _ hd => lt_of_le_of_lt (pC_le_of_le hd) threshold_two.1,
    fun _ hd => lt_of_lt_of_le threshold_two.2 (pC_le_of_le hd)⟩

/-- **The continuous crossing of `c₁`** lies in `(19, 20)` and is unique on `x > −1`. -/
theorem threshold_one_unique :
    ∃ x ∈ Ioo (19 : ℝ) 20, pR x = Real.log π / 2 ∧ ∀ y, -1 < y → pR y = Real.log π / 2 → y = x :=
  exists_unique_cross (by norm_num) (by norm_num)
    (by have := pR_natCast 19; push_cast at this; rw [this]; exact threshold_one.1)
    (by have := pR_natCast 20; push_cast at this; rw [this]; exact threshold_one.2)

/-- **The continuous crossing of `c₂`** lies in `(217, 218)` and is unique on `x > −1`. -/
theorem threshold_two_unique :
    ∃ x ∈ Ioo (217 : ℝ) 218, pR x = √π ∧ ∀ y, -1 < y → pR y = √π → y = x :=
  exists_unique_cross (by norm_num) (by norm_num)
    (by have := pR_natCast 217; push_cast at this; rw [this]; exact threshold_two.1)
    (by have := pR_natCast 218; push_cast at this; rw [this]; exact threshold_two.2)

/-- The two canonical values are one constant: `e^{c₁} = √π = c₂`. -/
theorem exp_c1 : Real.exp (Real.log π / 2) = √π := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos]
  ring_nf

/-- Part 0's orbit termination (ii): `log c₁ < 0`, so `p(d) = log c₁` has no solution with `d ≥ d₀`. -/
theorem log_c1_neg : Real.log (Real.log π / 2) < 0 ∧
    ∀ d : ℕ, 7 ≤ d → Electron.pC d ≠ Real.log (Real.log π / 2) := by
  have p1 := log_pi_gt
  have p2 := log_pi_lt
  have h : Real.log (Real.log π / 2) < 0 := Real.log_neg (by linarith) (by linarith)
  exact ⟨h, fun d hd heq => by have := natural_zero.2 d hd; linarith⟩

/-! ## The cascade invariant -/

/-- `Ω_{2m+1} = |S^{2m+1}| = 2π^{m+1}/m!`. -/
theorem Om_odd (m : ℕ) : Om (2 * m + 1) = 2 * π ^ (m + 1) / (Nat.factorial m) := by
  show BallTower.sphereArea (2 * m + 1 + 1) = _
  have hn : (2 * m + 1 + 1 : ℕ) = 2 * (m + 1) := by ring
  rw [hn]
  unfold BallTower.sphereArea BallTower.ballVol
  have hG : Real.Gamma (((2 * (m + 1) : ℕ) : ℝ) / 2 + 1) = (Nat.factorial (m + 1) : ℝ) := by
    rw [show ((2 * (m + 1) : ℕ) : ℝ) / 2 + 1 = ((m + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hsq : √π ^ (2 * (m + 1)) = π ^ (m + 1) := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hG, hsq, Nat.factorial_succ]
  push_cast
  field_simp

/-- Part 0's bilinear form `(Ω_5/Ω_a)² Ω_b Ω_c`. -/
def cascadeInv (a b c : ℕ) : ℝ := (Om 5 / Om a) ^ 2 * Om b * Om c

theorem cascadeInv_eq : cascadeInv 7 19 217 = 9 / π ^ 2 * Om 19 * Om 217 := by
  rw [cascadeInv, Om_five, Om_seven]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- `I = 36π^{117}/(9!·108!)`. -/
theorem cascadeInv_closed :
    cascadeInv 7 19 217 = 36 * π ^ 117 / (Nat.factorial 9 * Nat.factorial 108) := by
  rw [cascadeInv_eq, show (19 : ℕ) = 2 * 9 + 1 from rfl, show (217 : ℕ) = 2 * 108 + 1 from rfl, Om_odd,
    Om_odd]
  have hπ := Real.pi_pos
  field_simp
  ring

lemma prod3_lt {A A' B B' C C' : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h1 : A ≤ A') (h2 : B ≤ B') (h3 : C ≤ C') (hs : A < A' ∨ B < B' ∨ C < C') :
    A * B * C < A' * B' * C' := by
  have hA' : 0 < A' := lt_of_lt_of_le hA h1
  have hB' : 0 < B' := lt_of_lt_of_le hB h2
  rcases hs with h | h | h
  · calc A * B * C < A' * B * C := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h hB) hC
      _ ≤ A' * B' * C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA'.le) hC.le
      _ ≤ A' * B' * C' := mul_le_mul_of_nonneg_left h3 (mul_pos hA' hB').le
  · calc A * B * C ≤ A' * B * C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hB.le) hC.le
      _ < A' * B' * C := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h hA') hC
      _ ≤ A' * B' * C' := mul_le_mul_of_nonneg_left h3 (mul_pos hA' hB').le
  · calc A * B * C ≤ A' * B' * C := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 hB.le hA'.le) hC.le
      _ < A' * B' * C' := mul_lt_mul_of_pos_left h (mul_pos hA' hB')

/-- **The variational form:** among the eight labelings `(a, b, c) ∈ {6,7} × {19,20} × {217,218}`, the
form is largest at `(7, 19, 217)` only. -/
theorem cascadeInv_max (a b c : ℕ) (ha : a = 6 ∨ a = 7) (hb : b = 19 ∨ b = 20) (hc : c = 217 ∨ c = 218)
    (hne : (a, b, c) ≠ (7, 19, 217)) : cascadeInv a b c < cascadeInv 7 19 217 := by
  have h76 : Om 7 < Om 6 := Om_five_lt_seven_lt_six.2
  have h20 : Om 20 < Om 19 := Om_succ_lt 19 (by norm_num)
  have h218 : Om 218 < Om 217 := Om_succ_lt 217 (by norm_num)
  have p5 := Om_pos 5
  have p6 := Om_pos 6
  have p7 := Om_pos 7
  have hA : (Om 5 / Om 6) ^ 2 < (Om 5 / Om 7) ^ 2 :=
    pow_lt_pow_left₀ (div_lt_div_of_pos_left p5 p7 h76) (by positivity) (by norm_num)
  have hA6 : 0 < (Om 5 / Om 6) ^ 2 := by positivity
  have hA7 : 0 < (Om 5 / Om 7) ^ 2 := by positivity
  unfold cascadeInv
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · exact prod3_lt hA6 (Om_pos _) (Om_pos _) hA.le le_rfl le_rfl (Or.inl hA)
  · exact prod3_lt hA6 (Om_pos _) (Om_pos _) hA.le le_rfl h218.le (Or.inl hA)
  · exact prod3_lt hA6 (Om_pos _) (Om_pos _) hA.le h20.le le_rfl (Or.inl hA)
  · exact prod3_lt hA6 (Om_pos _) (Om_pos _) hA.le h20.le h218.le (Or.inl hA)
  · exact absurd rfl hne
  · exact prod3_lt hA7 (Om_pos _) (Om_pos _) le_rfl le_rfl h218.le (Or.inr (Or.inr h218))
  · exact prod3_lt hA7 (Om_pos _) (Om_pos _) le_rfl h20.le le_rfl (Or.inr (Or.inl h20))
  · exact prod3_lt hA7 (Om_pos _) (Om_pos _) le_rfl h20.le h218.le (Or.inr (Or.inl h20))

/-- **The value:** `1.0989 × 10⁻¹²⁰ < I < 1.0990 × 10⁻¹²⁰`. -/
theorem cascadeInv_bounds :
    (1.0989e-120 : ℝ) < cascadeInv 7 19 217 ∧ cascadeInv 7 19 217 < 1.0990e-120 := by
  rw [cascadeInv_closed]
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hl : (3.141592 : ℝ) ^ 117 < π ^ 117 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hu : π ^ 117 < (3.141593 : ℝ) ^ 117 := pow_lt_pow_left₀ h2 Real.pi_pos.le (by norm_num)
  have hF : (0 : ℝ) < Nat.factorial 9 * Nat.factorial 108 := by positivity
  constructor
  · rw [lt_div_iff₀ hF]
    have : (1.0989e-120 : ℝ) * (Nat.factorial 9 * Nat.factorial 108) < 36 * 3.141592 ^ 117 := by
      simp only [Nat.factorial]; norm_num
    linarith
  · rw [div_lt_iff₀ hF]
    have : (36 : ℝ) * 3.141593 ^ 117 < 1.0990e-120 * (Nat.factorial 9 * Nat.factorial 108) := by
      simp only [Nat.factorial]; norm_num
    linarith

end Part0

#print axioms Part0.pR_natCast
#print axioms Part0.rpsi_sub_ge
#print axioms Part0.rpsi_strictMonoOn
#print axioms Part0.rpsi_continuousOn
#print axioms Part0.pR_strictMonoOn
#print axioms Part0.pR_continuousOn
#print axioms Part0.exists_unique_cross
#print axioms Part0.OmR_natCast
#print axioms Part0.hasDerivAt_log_OmR
#print axioms Part0.log_pi_gt
#print axioms Part0.log_pi_lt
#print axioms Part0.pC_six_neg
#print axioms Part0.pC_seven_pos
#print axioms Part0.pC_le_of_le
#print axioms Part0.natural_zero
#print axioms Part0.zero_unique
#print axioms Part0.Om_pos
#print axioms Part0.Om_five
#print axioms Part0.Om_six
#print axioms Part0.Om_seven
#print axioms Part0.Om_lt_six
#print axioms Part0.Om_five_lt_seven_lt_six
#print axioms Part0.Nc_lt_one
#print axioms Part0.Om_lt_succ
#print axioms Part0.Om_succ_lt
#print axioms Part0.Om_unimodal
#print axioms Part0.threshold_one
#print axioms Part0.threshold_two
#print axioms Part0.threshold_labels
#print axioms Part0.threshold_one_unique
#print axioms Part0.threshold_two_unique
#print axioms Part0.exp_c1
#print axioms Part0.log_c1_neg
#print axioms Part0.Om_odd
#print axioms Part0.cascadeInv_eq
#print axioms Part0.cascadeInv_closed
#print axioms Part0.cascadeInv_max
#print axioms Part0.cascadeInv_bounds
