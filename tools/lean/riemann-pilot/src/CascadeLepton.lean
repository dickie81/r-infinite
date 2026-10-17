import Mathlib
import EulerGammaBinet

/-! # The cascade's charged-lepton chain in Lean (round 406)

Definitions as Part 0 and Part IVb of the cascade series state them, for a layer `d`:
* `R(d) = Γ((d+1)/2)/Γ((d+2)/2)`, the lapse `N(d) = √π·R(d)` and `α(d) = R(d)²/4`;
* `p(d) = ½ψ((d+1)/2) − ½ ln π` and the cascade potential `Φ(d) = Σ_{d'=5}^{d} p(d')`;
* the Dirac layers `d ≡ 5 (mod 8)`; `n_D(d)` counts those in `[5, d]`;
* the leading ratio of adjacent generations, `m_heavy/m_light = exp(Φ(d_light) − Φ(d_heavy))·2√π`.

What is proved here is mathematics about these definitions. That generation 1 (with the electron) sits at
`d = 21` is the series' layer assignment, and that these numbers are lepton masses is its hypothesis; neither is
a theorem here.
-/

open Real Finset

noncomputable section

namespace Electron

/-! ## Definitions -/

/-- `R(d) = Γ((d+1)/2)/Γ((d+2)/2)` (Part 0). -/
def Rc (d : ℕ) : ℝ := Real.Gamma (((d : ℝ) + 1) / 2) / Real.Gamma (((d : ℝ) + 2) / 2)

/-- The lapse `N(d) = √π·R(d)` (Part 0; Part IVb, proof of the obstruction factor). -/
def Nc (d : ℕ) : ℝ := √π * Rc d

/-- `α(d) = R(d)²/4`. -/
def alphaC (d : ℕ) : ℝ := Rc d ^ 2 / 4

/-- The digamma function on the real line. -/
def psiR (x : ℝ) : ℝ := (Complex.digamma x).re

/-- `p(d) = ½ψ((d+1)/2) − ½ ln π`. -/
def pC (d : ℕ) : ℝ := psiR (((d : ℝ) + 1) / 2) / 2 - Real.log π / 2

/-- The cascade potential `Φ(d) = Σ_{d'=5}^{d} p(d')`. -/
def PhiC (d : ℕ) : ℝ := ∑ k ∈ Icc 5 d, pC k

/-- The Dirac layers `d ≡ 5 (mod 8)` in `[5, D]`. -/
def diracLayers (D : ℕ) : Finset ℕ := (Icc 5 D).filter (fun d => d % 8 = 5)

/-- `n_D(d)`: the number of Dirac layers in `[5, d]`. -/
def nD (d : ℕ) : ℕ := (diracLayers d).card

/-- The leading ratio `exp(Φ(b) − Φ(a))·2√π` of the masses at layers `a < b` (Part IVb). -/
def leadRatio (a b : ℕ) : ℝ := Real.exp (PhiC b - PhiC a) * (2 * √π)

/-! ## Layers -/

theorem diracLayers_29 : diracLayers 29 = {5, 13, 21, 29} := by decide

theorem nD_generations : nD 5 = 1 ∧ nD 13 = 2 ∧ nD 21 = 3 ∧ nD 29 = 4 := by decide

/-- At a Dirac layer the sphere `S^{d−1}` is even-dimensional. -/
theorem dirac_sphere_even {d : ℕ} (h : d % 8 = 5) : Even (d - 1) := by
  rw [Nat.even_iff]; omega

/-! ## The lapse: `N(0) = π`, `N(1) = 2`, `N(2) = π/2` -/

theorem Rc_pos (d : ℕ) : 0 < Rc d :=
  div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))

theorem sqrt_pi_pos : 0 < √π := Real.sqrt_pos.2 Real.pi_pos

theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem Rc_zero : Rc 0 = √π := by
  have h1 : (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 := by norm_num
  have h2 : (((0 : ℕ) : ℝ) + 2) / 2 = 1 := by norm_num
  rw [Rc, h1, h2, Real.Gamma_one_half_eq, Real.Gamma_one, div_one]

theorem Rc_one : Rc 1 = 2 / √π := by
  have h1 : (((1 : ℕ) : ℝ) + 1) / 2 = 1 := by norm_num
  have h2 : (((1 : ℕ) : ℝ) + 2) / 2 = 3 / 2 := by norm_num
  rw [Rc, h1, h2, Real.Gamma_one, Gamma_three_halves]
  have := sqrt_pi_pos.ne'
  field_simp

theorem Rc_two : Rc 2 = √π / 2 := by
  have h1 : (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 := by norm_num
  have h2 : (((2 : ℕ) : ℝ) + 2) / 2 = 2 := by norm_num
  rw [Rc, h1, h2, Gamma_three_halves, Real.Gamma_two, div_one]

theorem Nc_zero : Nc 0 = π := by
  rw [Nc, Rc_zero, Real.mul_self_sqrt Real.pi_pos.le]

theorem Nc_one : Nc 1 = 2 := by
  rw [Nc, Rc_one]
  have := sqrt_pi_pos.ne'
  field_simp

theorem Nc_two : Nc 2 = π / 2 := by
  rw [Nc, Rc_two, ← mul_div_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- `N(1)` is the slicing integral with exponent `0`: the length of `[−1, 1]`. -/
theorem Nc_one_eq_integral : Nc 1 = ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (0 : ℕ) := by
  rw [Nc_one]; norm_num

/-- `N(2)` is the slicing integral with exponent `½`: the area of the half disc. -/
theorem Nc_two_eq_integral : Nc 2 = ∫ x in (-1 : ℝ)..1, √(1 - x ^ 2) := by
  rw [Nc_two, integral_sqrt_one_sub_sq]

/-- `2√π = N(1)·Γ(½)`. -/
theorem two_sqrt_pi_eq : 2 * √π = Nc 1 * Real.Gamma (1 / 2) := by
  rw [Nc_one, Real.Gamma_one_half_eq]

/-- With `N(d) = √π·R(d)`, the product `N(0)·Γ(½)` is `π√π`, not `2√π`. -/
theorem Nc_zero_mul_ne : Nc 0 * Real.Gamma (1 / 2) ≠ 2 * √π := by
  rw [Nc_zero, Real.Gamma_one_half_eq]
  intro h
  have := mul_right_cancel₀ sqrt_pi_pos.ne' h
  linarith [Real.pi_gt_three]

/-! ## The fermion obstruction factor -/

/-- `(R(d)/2)/N(d) = 1/(2√π)` at every layer. -/
theorem fermion_scalar_ratio (d : ℕ) : (Rc d / 2) / Nc d = 1 / (2 * √π) := by
  have := (Rc_pos d).ne'
  have := sqrt_pi_pos.ne'
  rw [Nc]
  field_simp

/-- `√α(d) = R(d)/2`. -/
theorem sqrt_alphaC (d : ℕ) : √(alphaC d) = Rc d / 2 := by
  rw [alphaC, show Rc d ^ 2 / 4 = (Rc d / 2) ^ 2 by ring,
    Real.sqrt_sq (by have := Rc_pos d; positivity)]

/-! ## Digamma at integers and half-integers -/

theorem psiR_nat (m : ℕ) : psiR ((m : ℝ) + 1) = harmonic m - eulerMascheroniConstant := by
  have h := Complex.digamma_nat_add_one m
  have e : (((m : ℝ) + 1 : ℝ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  rw [psiR, e, h]
  simp

theorem psiR_half (n : ℕ) :
    psiR ((n : ℝ) + 1 / 2)
      = -2 * Real.log 2 - eulerMascheroniConstant + ∑ j ∈ range n, 1 / ((j : ℝ) + 1 / 2) := by
  have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp at h'
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := Complex.digamma_apply_add_nat hs n
  rw [Complex.digamma_one_half] at h
  have e : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) = 1 / 2 + (n : ℂ) := by push_cast; ring
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have hrhs : -2 * Complex.log 2 - (eulerMascheroniConstant : ℂ)
      + ∑ k ∈ range n, ((1 / 2 : ℂ) + (k : ℂ))⁻¹
      = ((-2 * Real.log 2 - eulerMascheroniConstant + ∑ j ∈ range n, 1 / ((j : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    rw [hlog]
    push_cast
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [one_div]
    ring
  rw [psiR, e, h, hrhs, Complex.ofReal_re]

theorem pC_odd (m : ℕ) :
    pC (2 * m + 1) = ((harmonic m : ℝ) - eulerMascheroniConstant) / 2 - Real.log π / 2 := by
  have e : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [pC, e, psiR_nat]

theorem pC_even (n : ℕ) :
    pC (2 * n) = (-2 * Real.log 2 - eulerMascheroniConstant
      + ∑ j ∈ range n, 1 / ((j : ℝ) + 1 / 2)) / 2 - Real.log π / 2 := by
  have e : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  rw [pC, e, psiR_half]

/-! ## The potential over one Bott period -/

theorem PhiC_sub {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) :
    PhiC b - PhiC a = ∑ k ∈ Ioc a b, pC k := by
  have hI : ∀ n, Icc 5 n = Ioc 4 n := fun n => by ext k; simp; omega
  rw [PhiC, PhiC, hI, hI, ← Finset.sum_Ioc_consecutive _ ha hab]
  ring

/-- `Φ(21) − Φ(13)`: eight layers, four integer and four half-integer digamma arguments. -/
theorem PhiC_21_sub_13 : PhiC 21 - PhiC 13
    = 3195110257 / 232792560 - 4 * eulerMascheroniConstant - 4 * Real.log 2 - 4 * Real.log π := by
  rw [PhiC_sub (by norm_num) (by norm_num),
    show Ioc 13 21 = {14, 15, 16, 17, 18, 19, 20, 21} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h14 : pC 14 = _ := pC_even 7
  have h15 : pC 15 = _ := pC_odd 7
  have h16 : pC 16 = _ := pC_even 8
  have h17 : pC 17 = _ := pC_odd 8
  have h18 : pC 18 = _ := pC_even 9
  have h19 : pC 19 = _ := pC_odd 9
  have h20 : pC 20 = _ := pC_even 10
  have h21 : pC 21 = _ := pC_odd 10
  rw [h14, h15, h16, h17, h18, h19, h20, h21]
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- `Φ(13) − Φ(5)`. -/
theorem PhiC_13_sub_5 : PhiC 13 - PhiC 5
    = 62093 / 5544 - 4 * eulerMascheroniConstant - 4 * Real.log 2 - 4 * Real.log π := by
  rw [PhiC_sub (by norm_num) (by norm_num),
    show Ioc 5 13 = {6, 7, 8, 9, 10, 11, 12, 13} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h6 : pC 6 = _ := pC_even 3
  have h7 : pC 7 = _ := pC_odd 3
  have h8 : pC 8 = _ := pC_even 4
  have h9 : pC 9 = _ := pC_odd 4
  have h10 : pC 10 = _ := pC_even 5
  have h11 : pC 11 = _ := pC_odd 5
  have h12 : pC 12 = _ := pC_even 6
  have h13 : pC 13 = _ := pC_odd 6
  rw [h6, h7, h8, h9, h10, h11, h12, h13]
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Over a Bott period the potential difference is `q − 4γ − 4 ln 2 − 4 ln π`, so the leading ratio is
`√π e^{q − 4γ}/(8π⁴)`. -/
theorem leadRatio_closed {a b : ℕ} {q : ℝ}
    (h : PhiC b - PhiC a = q - 4 * eulerMascheroniConstant - 4 * Real.log 2 - 4 * Real.log π) :
    leadRatio a b = √π / (8 * π ^ 4) * Real.exp (q - 4 * eulerMascheroniConstant) := by
  rw [leadRatio, h]
  have e2 : Real.exp (4 * Real.log 2) = 16 := by
    rw [show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    norm_num
  have eπ : Real.exp (4 * Real.log π) = π ^ 4 := by
    rw [show (4 : ℝ) * Real.log π = Real.log (π ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [Real.exp_sub, Real.exp_sub, e2, eπ]
  have := Real.pi_pos
  field_simp
  ring

theorem leadRatio_13_21 : leadRatio 13 21
    = √π / (8 * π ^ 4) * Real.exp (3195110257 / 232792560 - 4 * eulerMascheroniConstant) :=
  leadRatio_closed PhiC_21_sub_13

theorem leadRatio_5_13 : leadRatio 5 13
    = √π / (8 * π ^ 4) * Real.exp (62093 / 5544 - 4 * eulerMascheroniConstant) :=
  leadRatio_closed PhiC_13_sub_5

/-! ## Interval arithmetic for `exp` -/

theorem exp_nat (n : ℕ) : Real.exp n = Real.exp 1 ^ n := by
  rw [← Real.exp_nat_mul, mul_one]

theorem exp_ge_of {x : ℝ} (n N : ℕ) (r : ℝ) (hx : x = n + r) (hr : 0 ≤ r) :
    (2.7182818283 : ℝ) ^ n * ∑ i ∈ range N, r ^ i / (Nat.factorial i) ≤ Real.exp x := by
  rw [hx, Real.exp_add, exp_nat]
  exact mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n)
    (Real.sum_le_exp_of_nonneg hr N) (Finset.sum_nonneg fun i _ => by positivity) (by positivity)

theorem exp_le_of {x : ℝ} (n N : ℕ) (hN : 0 < N) (r : ℝ) (hx : x = n + r) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    Real.exp x ≤ (2.7182818286 : ℝ) ^ n * ((∑ i ∈ range N, r ^ i / (Nat.factorial i))
      + r ^ N * (N + 1) / ((Nat.factorial N) * N)) := by
  rw [hx, Real.exp_add, exp_nat]
  exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n)
    (Real.exp_bound' hr0 hr1 hN) (Real.exp_pos _).le (by positivity)

theorem sqrt_pi_gt : (1.7724538509 : ℝ) < √π := by
  rw [Real.lt_sqrt (by norm_num)]
  linarith [Real.pi_gt_d20]

theorem sqrt_pi_lt : √π < 1.7724538510 := by
  rw [Real.sqrt_lt' (by norm_num)]
  linarith [Real.pi_lt_d20]

/-! ## The two leading ratios -/

/-- **`m_μ/m_e` at leading order**: `206.4957 < exp(Φ(21) − Φ(13))·2√π < 206.4959` (the series: `206.50`). -/
theorem leadRatio_13_21_bounds : (206.4957 : ℝ) < leadRatio 13 21 ∧ leadRatio 13 21 < 206.4959 := by
  rw [leadRatio_13_21]
  obtain ⟨gl, gu⟩ := eulerMascheroni_bounds
  have hEl := (exp_ge_of (x := 11.4162758) 11 10 0.4162758 (by norm_num) (by norm_num)).trans
    (Real.exp_le_exp.2 (show (11.4162758 : ℝ) ≤ 3195110257 / 232792560 - 4 * eulerMascheroniConstant
      by linarith))
  have hEu := (Real.exp_le_exp.2 (show 3195110257 / 232792560 - 4 * eulerMascheroniConstant
      ≤ (11.4162765 : ℝ) by linarith)).trans
    (exp_le_of (x := 11.4162765) 11 10 (by norm_num) 0.4162765 (by norm_num) (by norm_num)
      (by norm_num))
  set E := Real.exp (3195110257 / 232792560 - 4 * eulerMascheroniConstant)
  have hpl := Real.pi_gt_d20
  have hpu := Real.pi_lt_d20
  have hsl := sqrt_pi_gt
  have hsu := sqrt_pi_lt
  have hπ := Real.pi_pos
  rw [div_mul_eq_mul_div]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    have h1 : (206.4957 : ℝ) * (8 * π ^ 4) < 206.4957 * (8 * 3.14159265358979323847 ^ 4) := by
      gcongr
    have h2 : (206.4957 : ℝ) * (8 * 3.14159265358979323847 ^ 4) < 1.7724538509 *
        ((2.7182818283 : ℝ) ^ 11 * ∑ i ∈ range 10, (0.4162758 : ℝ) ^ i / (Nat.factorial i)) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have h3 : (1.7724538509 : ℝ) * ((2.7182818283 : ℝ) ^ 11
        * ∑ i ∈ range 10, (0.4162758 : ℝ) ^ i / (Nat.factorial i)) ≤ √π * E :=
      mul_le_mul hsl.le hEl (by positivity) sqrt_pi_pos.le
    linarith
  · rw [div_lt_iff₀ (by positivity)]
    have h1 : √π * E ≤ 1.7724538510 * ((2.7182818286 : ℝ) ^ 11 * ((∑ i ∈ range 10,
        (0.4162765 : ℝ) ^ i / (Nat.factorial i)) + 0.4162765 ^ 10 * (10 + 1)
          / ((Nat.factorial 10) * 10))) :=
      mul_le_mul hsu.le hEu (Real.exp_pos _).le (by norm_num)
    have h2 : (1.7724538510 : ℝ) * ((2.7182818286 : ℝ) ^ 11 * ((∑ i ∈ range 10,
        (0.4162765 : ℝ) ^ i / (Nat.factorial i)) + 0.4162765 ^ 10 * (10 + 1)
          / ((Nat.factorial 10) * 10))) < 206.4959 * (8 * 3.14159265358979323846 ^ 4) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have h3 : (206.4959 : ℝ) * (8 * 3.14159265358979323846 ^ 4) < 206.4959 * (8 * π ^ 4) := by
      gcongr
    linarith

/-- **`m_τ/m_μ` at leading order**: `16.52999 < exp(Φ(13) − Φ(5))·2√π < 16.53001` (the series: `16.53`). -/
theorem leadRatio_5_13_bounds : (16.52999 : ℝ) < leadRatio 5 13 ∧ leadRatio 5 13 < 16.53001 := by
  rw [leadRatio_5_13]
  obtain ⟨gl, gu⟩ := eulerMascheroni_bounds
  have hEl := (exp_ge_of (x := 8.8911728) 8 14 0.8911728 (by norm_num) (by norm_num)).trans
    (Real.exp_le_exp.2 (show (8.8911728 : ℝ) ≤ 62093 / 5544 - 4 * eulerMascheroniConstant
      by linarith))
  have hEu := (Real.exp_le_exp.2 (show 62093 / 5544 - 4 * eulerMascheroniConstant
      ≤ (8.8911735 : ℝ) by linarith)).trans
    (exp_le_of (x := 8.8911735) 8 14 (by norm_num) 0.8911735 (by norm_num) (by norm_num)
      (by norm_num))
  set E := Real.exp (62093 / 5544 - 4 * eulerMascheroniConstant)
  have hpl := Real.pi_gt_d20
  have hpu := Real.pi_lt_d20
  have hsl := sqrt_pi_gt
  have hsu := sqrt_pi_lt
  have hπ := Real.pi_pos
  rw [div_mul_eq_mul_div]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    have h1 : (16.52999 : ℝ) * (8 * π ^ 4) < 16.52999 * (8 * 3.14159265358979323847 ^ 4) := by
      gcongr
    have h2 : (16.52999 : ℝ) * (8 * 3.14159265358979323847 ^ 4) < 1.7724538509 *
        ((2.7182818283 : ℝ) ^ 8 * ∑ i ∈ range 14, (0.8911728 : ℝ) ^ i / (Nat.factorial i)) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have h3 : (1.7724538509 : ℝ) * ((2.7182818283 : ℝ) ^ 8
        * ∑ i ∈ range 14, (0.8911728 : ℝ) ^ i / (Nat.factorial i)) ≤ √π * E :=
      mul_le_mul hsl.le hEl (by positivity) sqrt_pi_pos.le
    linarith
  · rw [div_lt_iff₀ (by positivity)]
    have h1 : √π * E ≤ 1.7724538510 * ((2.7182818286 : ℝ) ^ 8 * ((∑ i ∈ range 14,
        (0.8911735 : ℝ) ^ i / (Nat.factorial i)) + 0.8911735 ^ 14 * (14 + 1)
          / ((Nat.factorial 14) * 14))) :=
      mul_le_mul hsu.le hEu (Real.exp_pos _).le (by norm_num)
    have h2 : (1.7724538510 : ℝ) * ((2.7182818286 : ℝ) ^ 8 * ((∑ i ∈ range 14,
        (0.8911735 : ℝ) ^ i / (Nat.factorial i)) + 0.8911735 ^ 14 * (14 + 1)
          / ((Nat.factorial 14) * 14))) < 16.53001 * (8 * 3.14159265358979323846 ^ 4) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have h3 : (16.53001 : ℝ) * (8 * 3.14159265358979323846 ^ 4) < 16.53001 * (8 * π ^ 4) := by
      gcongr
    linarith

/-! ## The series' closures beyond leading order (inputs displayed) -/

theorem Rc_21 : Rc 21 = 7431782400 / (13749310575 * √π) := by
  have h1 : (((21 : ℕ) : ℝ) + 1) / 2 = ((10 : ℕ) : ℝ) + 1 := by norm_num
  have h2 : (((21 : ℕ) : ℝ) + 2) / 2 = ((11 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have hf : (Nat.factorial 10 : ℝ) = 3628800 := by norm_num [Nat.factorial]
  have hd : ((2 * 11 - 1 : ℕ).doubleFactorial : ℝ) = 13749310575 := by
    rw [show (2 * 11 - 1 : ℕ).doubleFactorial = 13749310575 by decide]; norm_num
  rw [Rc, h1, h2, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_add_half, hf, hd]
  have := sqrt_pi_pos.ne'
  field_simp
  norm_num

theorem alphaC_21 : alphaC 21 = (7431782400 / 13749310575) ^ 2 / (4 * π) := by
  rw [alphaC, Rc_21, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have := Real.pi_pos.ne'
  field_simp

theorem Rc_14 : Rc 14 = 135135 * √π / 645120 := by
  have h1 : (((14 : ℕ) : ℝ) + 1) / 2 = ((7 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have h2 : (((14 : ℕ) : ℝ) + 2) / 2 = ((7 : ℕ) : ℝ) + 1 := by norm_num
  have hf : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
  have hd : ((2 * 7 - 1 : ℕ).doubleFactorial : ℝ) = 135135 := by
    rw [show (2 * 7 - 1 : ℕ).doubleFactorial = 135135 by decide]; norm_num
  rw [Rc, h1, h2, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_add_half, hf, hd]
  field_simp
  norm_num

theorem alphaC_14 : alphaC 14 = (135135 / 645120) ^ 2 * π / 4 := by
  rw [alphaC, Rc_14, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  ring

/-- Part IVb's `m_μ/m_e` closure at the `m − k = 0` slot (Remark `rem:slot-precedence-mu-e`):
`leading × (1 + α_em/(2π) + α_em·α(21))`, with `α_em` an argument. -/
def muECorrected (αem : ℝ) : ℝ := leadRatio 13 21 * (1 + αem / (2 * π) + αem * alphaC 21)

/-- With the paper's `α_em = 1/137.028`: `206.7705 < m_μ/m_e < 206.7708` (CODATA 2022: `206.7682827`). -/
theorem muECorrected_bounds :
    (206.7705 : ℝ) < muECorrected (1 / 137.028) ∧ muECorrected (1 / 137.028) < 206.7708 := by
  obtain ⟨l, u⟩ := leadRatio_13_21_bounds
  have hpl := Real.pi_gt_d20
  have hpu := Real.pi_lt_d20
  have hπ := Real.pi_pos
  have hF : 1 + (1 / 137.028) / (2 * π) + (1 / 137.028) * alphaC 21
      = 1 + ((1 / 137.028) / 2 + (1 / 137.028) * (7431782400 / 13749310575) ^ 2 / 4) / π := by
    rw [alphaC_21]; field_simp; ring
  have hFl : (1.0013311 : ℝ) < 1 + (1 / 137.028) / (2 * π) + (1 / 137.028) * alphaC 21 := by
    rw [hF, ← sub_lt_iff_lt_add', lt_div_iff₀ hπ]; norm_num; linarith
  have hFu : 1 + (1 / 137.028) / (2 * π) + (1 / 137.028) * alphaC 21 < (1.0013312 : ℝ) := by
    rw [hF, ← lt_sub_iff_add_lt', div_lt_iff₀ hπ]; norm_num; linarith
  rw [muECorrected]
  constructor
  · have := mul_lt_mul'' l hFl (by norm_num) (by norm_num)
    linarith
  · have := mul_lt_mul'' u hFu (by linarith) (by linarith)
    linarith

/-- The closure sits between `0.00107%` and `0.00123%` above CODATA 2022's `206.7682827`. -/
theorem muECorrected_vs_codata :
    (0.0000107 : ℝ) < muECorrected (1 / 137.028) / 206.7682827 - 1 ∧
      muECorrected (1 / 137.028) / 206.7682827 - 1 < 0.0000123 := by
  obtain ⟨l, u⟩ := muECorrected_bounds
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ (by norm_num)]; linarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by norm_num)]; linarith

/-- The `U(1)`-layer shift of Part IVb (Theorem `thm:alpha-s-closure`): `exp(Φ(13) − Φ(5) + α(14)/χ)·2√π`
with `χ = 2`. -/
def tauMuShifted : ℝ := Real.exp (PhiC 13 - PhiC 5 + alphaC 14 / 2) * (2 * √π)

theorem tauMuShifted_eq : tauMuShifted = leadRatio 5 13 * Real.exp (alphaC 14 / 2) := by
  rw [tauMuShifted, leadRatio, Real.exp_add]; ring

/-- `16.8172 < m_τ/m_μ < 16.8174` with the shift (the series: `16.8173`; PDG: `16.8170 ± 0.0011`). -/
theorem tauMuShifted_bounds : (16.8172 : ℝ) < tauMuShifted ∧ tauMuShifted < 16.8174 := by
  obtain ⟨l, u⟩ := leadRatio_5_13_bounds
  have hpl := Real.pi_gt_d20
  have hpu := Real.pi_lt_d20
  set y := alphaC 14 / 2 with hy
  have hy' : y = (135135 / 645120) ^ 2 / 8 * π := by rw [hy, alphaC_14]; ring
  have hyl : (0.017231161 : ℝ) ≤ y := by rw [hy']; nlinarith
  have hyu : y ≤ (0.017231163 : ℝ) := by rw [hy']; nlinarith
  have hEl : (1.0173804 : ℝ) < Real.exp y := by
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ y by linarith) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    nlinarith
  have hEu : Real.exp y < (1.0173808 : ℝ) := by
    have := Real.exp_bound' (show (0 : ℝ) ≤ y by linarith) (by linarith) (show 0 < 3 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    nlinarith
  rw [tauMuShifted_eq]
  constructor
  · have := mul_lt_mul'' l hEl (by norm_num) (by norm_num)
    linarith
  · have := mul_lt_mul'' u hEu (by linarith) (Real.exp_pos _).le
    linarith

/-- The leading `m_μ/m_e` sits between `0.1319%` and `0.1321%` below CODATA 2022's `206.7682827`. -/
theorem leadRatio_13_21_vs_codata :
    (0.001319 : ℝ) < 206.7682827 / leadRatio 13 21 - 1 ∧ 206.7682827 / leadRatio 13 21 - 1 < 0.001321 := by
  obtain ⟨l, u⟩ := leadRatio_13_21_bounds
  have hL : 0 < leadRatio 13 21 := by linarith
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hL]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hL]; nlinarith

end Electron

#print axioms Electron.leadRatio_13_21_bounds
#print axioms Electron.leadRatio_5_13_bounds
#print axioms Electron.Nc_zero_mul_ne
#print axioms Electron.nD_generations
#print axioms Electron.muECorrected_bounds
#print axioms Electron.tauMuShifted_bounds
#print axioms Electron.leadRatio_13_21_vs_codata
#print axioms Electron.muECorrected_vs_codata
#print axioms Electron.diracLayers_29
#print axioms Electron.dirac_sphere_even
#print axioms Electron.Nc_one_eq_integral
#print axioms Electron.Nc_two_eq_integral
#print axioms Electron.two_sqrt_pi_eq
#print axioms Electron.fermion_scalar_ratio
#print axioms Electron.sqrt_alphaC
