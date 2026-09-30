import ParityCont
import KaiserNine

/-! # A parity gap from a one-sector lower bound at the prefactor scale (round 246)

If the odd ground energy `λ₁ᴼ(b)` is eventually at least `c·exp((9 + δ)b − 4πe^{2b})`, the parity gap holds eventually, and along a sequence of ground states this gives RH (`rh_of_lamO_lower`); odd test functions have purely imaginary `ĝ` on `ℝ`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace ParityGapLower

open Pilot1ca Pilot1bt

/-- **The eventual parity gap from an odd lower bound at the Connes scale.** If for some `δ > 0` and
`c > 0` the odd ground energy is eventually `≥ c·e^{(9+δ)b − 4πe^{2b}}`, then `ParityGap b` holds for
all large `b`. The even side is `Kaiser.lam_nine` (`λ₁ ≤ K(b+1)e^{9b − 4πe^{2b}}`). -/
theorem parityGap_of_lamO_lower {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (h : ∀ᶠ b in atTop, c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) ≤ lamO b) :
    ∀ᶠ b in atTop, ParityGap b := by
  obtain ⟨K, hK, hnine⟩ := Kaiser.lam_nine
  have hev : ∀ᶠ b : ℝ in atTop, 4 ≤ b ∧ 4 * K / (c * δ ^ 2) < b :=
    (eventually_ge_atTop 4).and (eventually_gt_atTop _)
  filter_upwards [h, hev] with b hb ⟨hb4, hbK⟩
  have hb0 : 0 < b := by linarith
  have hcd : 0 < c * δ ^ 2 := by positivity
  -- K(b+1) < c·e^{δb}
  have hq : (δ * b) ^ 2 / 2 ≤ Real.exp (δ * b) := by
    have := Real.quadratic_le_exp_of_nonneg (x := δ * b) (by positivity)
    nlinarith [mul_pos hδ hb0]
  have hK2 : K * (b + 1) ≤ 2 * K * b := by nlinarith
  have hKb : 2 * K * b < c * ((δ * b) ^ 2 / 2) := by
    have h1 : 4 * K < c * δ ^ 2 * b := by
      have := (div_lt_iff₀ hcd).1 hbK
      linarith
    nlinarith
  have hlt : K * (b + 1) < c * Real.exp (δ * b) := by
    have : c * ((δ * b) ^ 2 / 2) ≤ c * Real.exp (δ * b) := mul_le_mul_of_nonneg_left hq hc.le
    linarith
  set E := Real.exp (9 * b - 4 * π * Real.exp (2 * b)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hsplit : c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) = c * Real.exp (δ * b) * E := by
    have ex : (9 + δ) * b - 4 * π * Real.exp (2 * b) = δ * b + (9 * b - 4 * π * Real.exp (2 * b)) := by ring
    rw [hE, ex, Real.exp_add]; ring
  have hlam : lam b < lamO b := by
    have h1 := hnine b hb4
    have h2 : K * (b + 1) * E < c * Real.exp (δ * b) * E := mul_lt_mul_of_pos_right hlt hE0
    rw [← hsplit] at h2
    linarith
  intro o hp hn
  exact hlam.trans_le (lamO_le hb0 hp hn)

/-- **RH from `HypConv` and an odd lower bound at the Connes scale.** No crossing on a compact range,
no simplicity. -/
theorem rh_of_lamO_lower {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hinf : Tendsto a atTop atTop)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (h : ∀ᶠ b in atTop, c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) ≤ lamO b)
    (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_parity_gap ha hgs (hinf.eventually (parityGap_of_lamO_lower hδ hc h)) hconv

/-- **Odd transforms are purely imaginary on `ℝ`.** -/
theorem ghatC_re_eq_zero_of_odd {o : ℝ → ℝ} {a : ℝ} (hodd : ∀ u, o (-u) = -o u)
    (hint : IntervalIntegrable o volume (-a) a) (x : ℝ) : (ghatC o a x).re = 0 := by
  have hgC : IntervalIntegrable (fun u => ((o u : ℝ) : ℂ)) volume (-a) a := ⟨hint.1.ofReal, hint.2.ofReal⟩
  have hc : IntervalIntegrable (fun u : ℝ => ((o u : ℝ) : ℂ) * Complex.exp (I * x * u)) volume (-a) a :=
    hgC.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * x * u)).continuousOn
  unfold ghatC
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hc]
  simp only [Complex.reCLM_apply]
  set f : ℝ → ℝ := fun u => (((o u : ℝ) : ℂ) * Complex.exp (I * x * u)).re with hf
  have hform : ∀ u, f u = o u * Real.cos (x * u) := by
    intro u
    have e2 : (I * (x : ℂ) * (u : ℂ)) = ((x * u : ℝ) : ℂ) * I := by push_cast; ring
    simp only [hf, e2, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hodd' : ∀ u, f (-u) = -f u := by
    intro u
    rw [hform, hform, hodd, mul_neg, Real.cos_neg, neg_mul]
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) f
  simp only [neg_neg] at h
  have : ∫ u in (-a)..a, f u = -∫ u in (-a)..a, f u := by
    conv_lhs => rw [← h]
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ => hodd' u
  linarith

/-- The odd-sector zero term `−ô(τ)²` is `≥ 0` at a real `τ` (a zero on the line). -/
theorem odd_term_nonneg_real {o : ℝ → ℝ} {a : ℝ} (hodd : ∀ u, o (-u) = -o u)
    (hint : IntervalIntegrable o volume (-a) a) (x : ℝ) : 0 ≤ (-(ghatC o a x) ^ 2).re := by
  have hre := ghatC_re_eq_zero_of_odd hodd hint x
  set z := ghatC o a x
  have e : z = (z.im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
  rw [e]
  have : (-(((z.im : ℝ) : ℂ) * I) ^ 2 : ℂ) = ((z.im ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [this, ofReal_re]; positivity

/-- The odd-sector zero term `−ô(iy)²` is `≤ 0` at a purely imaginary `τ = iy` (a real zero): real
zeros are seen, with the negative sign, by odd probes. -/
theorem odd_term_nonpos_imag (o : ℝ → ℝ) (a y : ℝ) : (-(ghatC o a (I * y)) ^ 2).re ≤ 0 := by
  have e : ghatC o a (I * y) = ((∫ u in (-a)..a, o u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
    unfold ghatC
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro u _
    have e : I * (I * (y : ℂ)) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
      push_cast
      linear_combination (y * u : ℂ) * I_mul_I
    simp only
    rw [e, ← ofReal_exp]
    push_cast
    ring
  rw [e]
  set x : ℝ := ∫ u in (-a)..a, o u * Real.exp (-(y * u))
  have : (-((x : ℝ) : ℂ) ^ 2 : ℂ) = ((-(x ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]
  nlinarith [sq_nonneg x]

end ParityGapLower

#print axioms ParityGapLower.parityGap_of_lamO_lower
#print axioms ParityGapLower.rh_of_lamO_lower
#print axioms ParityGapLower.ghatC_re_eq_zero_of_odd
#print axioms ParityGapLower.odd_term_nonneg_real
#print axioms ParityGapLower.odd_term_nonpos_imag
