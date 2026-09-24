import Mathlib
import StripConv

/-! # Riemann's kernel formula

Riemann's kernel `Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}` (`RPhi`) satisfies

  `∫_ℝ Φ(u) e^{izu} du = Ξ(z)/2`   for every `z ∈ ℂ`   (`RPhiHat_eq`),

with `Ξ(z) = ξ(½ + iz)` built from Mathlib's `completedRiemannZeta₀`. This discharges round 62's
`KernelApprox` for `φ_n = Φ` whenever `a_n → ∞` (`kernelApprox_RPhi`), so `rh_of_close_RPhi` derives
RH from the `L²` closeness hypothesis alone.

* **Half-plane (`integral_RPhi_halfplane`).** For `Im z < −½` (`Re s > 1`, `s = ½ + iz`), each term
  integrates to `(s(s−1)/4)(πn²)^{−s/2}Γ(s/2)` by the substitution `x = e^{2u}` and Euler's integral
  (`integral_exp_theta_term`, `integral_phiT`). The norm integrals are summable (`n^{−Re s}`), so the
  sum can be integrated termwise. Mathlib's `completedZeta_eq_tsum_of_one_lt_re` then gives `ξ(s)/2`.
* **Evenness (`RPhi_even`).** With `F(u) = e^{u/2}θ(e^{2u})` (`θ` = Mathlib's `evenKernel 0`), termwise
  differentiation gives `4Φ = F'' − F/4` (`RPhi_eq`), and the theta functional equation gives
  `F(−u) = F(u)` (`theta_even`). So `F''` and `Φ` are even.
* **Decay (`RPhi_decay_gen`).** `|Φ(u)| ≤ C_B e^{−B|u|}` for every `B`: the series bound for `u ≥ 0`,
  then evenness.
* **Continuation (`RPhiHat_eq`).** The truncated transforms converge uniformly on every strip
  `|Im z| ≤ M`, so `Φ̂` is entire (`differentiable_RPhiHat`). It agrees with `Ξ/2` on `Im z < −½`,
  hence on all of `ℂ` by the identity theorem.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace Pilot1ca

open Pilot1bt HurwitzZeta

theorem cpow_exp_real (v : ℝ) (w : ℂ) : ((Real.exp v : ℝ) : ℂ) ^ w = Complex.exp (v * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]

/-- `∫_ℝ e^{αu} exp(−c e^{2u}) du = ½ (1/c)^{α/2} Γ(α/2)` for `Re α > 0`, `c > 0`. -/
theorem integral_exp_theta_term {α : ℂ} (hα : 0 < α.re) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, Complex.exp (α * u) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ)
      = 1 / 2 * ((1 / c : ℂ) ^ (α / 2) * Complex.Gamma (α / 2)) := by
  set h : ℝ → ℂ := fun t => (t : ℂ) ^ (α / 2 - 1) * Complex.exp (-(c * t))
  set g : ℝ → ℂ := fun v => (Real.exp v : ℝ) • h (Real.exp v)
  have hg : ∀ v, g v = Complex.exp (α * (v / 2)) * (Real.exp (-(c * Real.exp v)) : ℂ) := by
    intro v
    simp only [g, h, Complex.real_smul, cpow_exp_real]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have e1 : (fun u : ℝ => Complex.exp (α * u) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ))
      = fun u => g (2 * u) := by
    funext u; rw [hg]; congr 3; push_cast; ring
  rw [e1, Measure.integral_comp_mul_left (fun v => g v) 2, integral_comp_exp h]
  have hα2 : 0 < (α / 2).re := by simp; linarith
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hα2 hc]
  simp [abs_of_pos]

theorem integrable_exp_theta_term {α : ℂ} (hα : 0 < α.re) {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ℝ => Complex.exp (α * u) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ) := by
  set h : ℝ → ℂ := fun t => (t : ℂ) ^ (α / 2 - 1) * Complex.exp (-(c * t))
  set g : ℝ → ℂ := fun v => (Real.exp v : ℝ) • h (Real.exp v)
  have hg : ∀ v, g v = Complex.exp (α * (v / 2)) * (Real.exp (-(c * Real.exp v)) : ℂ) := by
    intro v
    simp only [g, h, Complex.real_smul, cpow_exp_real]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hα2 : 0 < (α / 2).re := by simp; linarith
  have hh : IntegrableOn h (Ioi 0) := by
    have := Complex.GammaIntegral_convergent hα2
    rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at this
    refine (IntegrableOn.congr_fun (this.const_mul ((1 / c : ℂ) ^ (α / 2 - 1)))
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
    simp only [h]
    have key : (1 / (c : ℂ)) ^ (α / 2 - 1) * (c : ℂ) ^ (α / 2 - 1) = 1 := by
      rw [show (1 / (c : ℂ)) = ((1 / c : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) hc.le, ← Complex.ofReal_mul,
        one_div_mul_cancel hc.ne', Complex.ofReal_one, Complex.one_cpow]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le]
    push_cast
    linear_combination (↑t ^ (α / 2 - 1) * Complex.exp (-(↑c * ↑t))) * key
  have hgi : Integrable g := (integrable_comp_exp h).2 hh
  have e1 : (fun u : ℝ => Complex.exp (α * u) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ))
      = fun u => g (2 * u) := by
    funext u; rw [hg]; congr 3; push_cast; ring
  rw [e1]
  exact hgi.comp_mul_left' two_ne_zero

/-- `c_n = πn²`. -/
noncomputable def thC (n : ℕ) : ℝ := π * (n : ℝ) ^ 2

/-- The `n`-th term of Riemann's kernel,
`φ_n(u) = (2π²n⁴e^{4u} − 3πn²e^{2u}) e^{u/2 − πn²e^{2u}}`. -/
noncomputable def phiT (n : ℕ) (u : ℝ) : ℝ :=
  (2 * thC n ^ 2 * Real.exp (4 * u) - 3 * thC n * Real.exp (2 * u))
    * Real.exp (u / 2 - thC n * Real.exp (2 * u))

theorem phiT_split (n : ℕ) (z : ℂ) (u : ℝ) :
    (phiT n u : ℂ) * Complex.exp (Complex.I * z * u)
      = 2 * (thC n : ℂ) ^ 2 * (Complex.exp ((9 / 2 + Complex.I * z) * u)
          * (Real.exp (-(thC n * Real.exp (2 * u))) : ℂ))
        - 3 * (thC n : ℂ) * (Complex.exp ((5 / 2 + Complex.I * z) * u)
          * (Real.exp (-(thC n * Real.exp (2 * u))) : ℂ)) := by
  simp only [phiT]
  push_cast
  have e1 : Complex.exp (4 * u) * Complex.exp (u / 2 - thC n * Complex.exp (2 * u))
      * Complex.exp (Complex.I * z * u)
      = Complex.exp ((9 / 2 + Complex.I * z) * u) * Complex.exp (-(thC n * Complex.exp (2 * u))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (2 * u) * Complex.exp (u / 2 - thC n * Complex.exp (2 * u))
      * Complex.exp (Complex.I * z * u)
      = Complex.exp ((5 / 2 + Complex.I * z) * u) * Complex.exp (-(thC n * Complex.exp (2 * u))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (2 * (thC n : ℂ) ^ 2) * e1 - (3 * (thC n : ℂ)) * e2

theorem thC_pos {n : ℕ} (hn : 1 ≤ n) : 0 < thC n := by
  unfold thC; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

/-- **The transform of one term**: `∫ φ_n(u) e^{izu} du = (s(s−1)/4)(1/c_n)^{s/2} Γ(s/2)` with
`s = ½ + iz`, for `Im z < −½`. -/
theorem integral_phiT {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.im < -1 / 2) :
    ∫ u : ℝ, (phiT n u : ℂ) * Complex.exp (Complex.I * z * u)
      = (1 / 2 + Complex.I * z) * (1 / 2 + Complex.I * z - 1) / 4
        * ((1 / (thC n : ℂ)) ^ ((1 / 2 + Complex.I * z) / 2)
          * Complex.Gamma ((1 / 2 + Complex.I * z) / 2)) := by
  have hc := thC_pos hn
  have h1 : 0 < (9 / 2 + Complex.I * z).re := by simp; linarith
  have h2 : 0 < (5 / 2 + Complex.I * z).re := by simp; linarith
  simp_rw [phiT_split]
  rw [integral_sub ((integrable_exp_theta_term h1 hc).const_mul _)
      ((integrable_exp_theta_term h2 hc).const_mul _),
    integral_const_mul, integral_const_mul, integral_exp_theta_term h1 hc,
    integral_exp_theta_term h2 hc]
  set w := (1 / 2 + Complex.I * z) / 2 with hw
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have hw1 : w + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have ea : (9 / 2 + Complex.I * z) / 2 = w + 1 + 1 := by rw [hw]; ring
  have eb : (5 / 2 + Complex.I * z) / 2 = w + 1 := by rw [hw]; ring
  have hc0 : (1 / (thC n : ℂ)) ≠ 0 := by
    simp; exact_mod_cast hc.ne'
  rw [ea, eb, Complex.Gamma_add_one _ hw1, Complex.Gamma_add_one _ hw0,
    Complex.cpow_add _ _ hc0, Complex.cpow_add _ _ hc0, Complex.cpow_one]
  have hcC : (thC n : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp
  ring

theorem cpow_pos_real {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ((r : ℝ) : ℂ) ^ w = Complex.exp (Real.log r * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]

theorem integral_exp_theta_term_real {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, Real.exp (β * u) * Real.exp (-(c * Real.exp (2 * u)))
      = 1 / 2 * ((1 / c) ^ (β / 2) * Real.Gamma (β / 2)) := by
  have h := integral_exp_theta_term (α := (β : ℂ)) (by simpa using hβ) hc
  have e : (fun u : ℝ => Complex.exp ((β : ℂ) * u) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ))
      = fun u => ((Real.exp (β * u) * Real.exp (-(c * Real.exp (2 * u))) : ℝ) : ℂ) := by
    funext u; push_cast; ring_nf
  rw [e, integral_complex_ofReal] at h
  have e2 : ((1 / c : ℂ)) ^ ((β : ℂ) / 2) = (((1 / c) ^ (β / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  rw [e2, show ((β : ℂ) / 2) = ((β / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

theorem integrable_exp_theta_term_real {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ℝ => Real.exp (β * u) * Real.exp (-(c * Real.exp (2 * u))) := by
  have h := (integrable_exp_theta_term (α := (β : ℂ)) (by simpa using hβ) hc).norm
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.exp_pos _)]; simp

theorem phiT_zero (u : ℝ) : phiT 0 u = 0 := by simp [phiT, thC]

/-- The norm integrals of the terms are summable when `Im z < −½`. -/
theorem summable_integral_norm_phiT {z : ℂ} (hz : z.im < -1 / 2) :
    Summable fun n => ∫ u : ℝ, ‖(phiT n u : ℂ) * Complex.exp (Complex.I * z * u)‖ := by
  set y := z.im
  have hb1 : 0 < 9 / 2 - y := by linarith
  have hb2 : 0 < 5 / 2 - y := by linarith
  set K := Real.Gamma ((9 / 2 - y) / 2) + 3 / 2 * Real.Gamma ((5 / 2 - y) / 2)
  set e := (y - 1 / 2) / 2
  have hbound : ∀ n, 1 ≤ n → ∫ u : ℝ, ‖(phiT n u : ℂ) * Complex.exp (Complex.I * z * u)‖
      ≤ thC n ^ e * K := by
    intro n hn
    have hc := thC_pos hn
    set c := thC n
    have hpt : ∀ u : ℝ, ‖(phiT n u : ℂ) * Complex.exp (Complex.I * z * u)‖
        ≤ 2 * c ^ 2 * (Real.exp ((9 / 2 - y) * u) * Real.exp (-(c * Real.exp (2 * u))))
          + 3 * c * (Real.exp ((5 / 2 - y) * u) * Real.exp (-(c * Real.exp (2 * u)))) := by
      intro u
      rw [phiT_split]
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, norm_pow,
        Complex.norm_ofNat]
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos hc]
      congr 2 <;> (simp only [y, c]; simp [Complex.mul_re]; ring_nf; simp)
    have i1 := integrable_exp_theta_term_real hb1 hc
    have i2 := integrable_exp_theta_term_real hb2 hc
    have i3 : Integrable fun u : ℝ =>
        2 * c ^ 2 * (Real.exp ((9 / 2 - y) * u) * Real.exp (-(c * Real.exp (2 * u))))
          + 3 * c * (Real.exp ((5 / 2 - y) * u) * Real.exp (-(c * Real.exp (2 * u)))) :=
      (i1.const_mul (2 * c ^ 2)).add (i2.const_mul (3 * c))
    have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      i3 (Filter.Eventually.of_forall hpt)
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_theta_term_real hb1 hc, integral_exp_theta_term_real hb2 hc] at hmono
    refine hmono.trans (le_of_eq ?_)
    rw [Real.div_rpow zero_le_one hc.le, Real.div_rpow zero_le_one hc.le, Real.one_rpow,
      Real.one_rpow]
    have h1 : c ^ 2 * (1 / c ^ ((9 / 2 - y) / 2)) = c ^ e := by
      rw [← Real.rpow_natCast, mul_one_div, ← Real.rpow_sub hc]; congr 1; simp [e]; ring
    have h2 : c * (1 / c ^ ((5 / 2 - y) / 2)) = c ^ e := by
      rw [mul_one_div, ← Real.rpow_one_sub' hc.le] <;> [congr 1; skip]
      · simp [e]; ring
      · linarith
    simp only [K]
    linear_combination (Real.Gamma ((9 / 2 - y) / 2)) * h1 + (3 / 2 * Real.Gamma ((5 / 2 - y) / 2)) * h2
  have hK : 0 ≤ K := by
    simp only [K]
    have := Real.Gamma_pos_of_pos (show 0 < (9 / 2 - y) / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < (5 / 2 - y) / 2 by linarith)
    positivity
  -- the majorant `π^e n^{2e} K`
  have hs : Summable fun n : ℕ => (π ^ e * K) * ((n : ℝ) ^ (-(2 * e)))⁻¹ :=
    (Real.summable_nat_rpow_inv.2 (by simp [e]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT_zero]
    have : (0 : ℝ) ^ (-(2 * e)) = 0 := Real.zero_rpow (by simp [e]; linarith)
    simp [this]
  · refine (hbound n hn).trans (le_of_eq ?_)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [thC]
    rw [Real.mul_rpow pi_pos.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
      Real.rpow_neg hn'.le, inv_inv]
    push_cast; ring_nf

/-- **Riemann's kernel** `Φ(u) = Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}`. -/
def RPhi (u : ℝ) : ℝ := ∑' n : ℕ, phiT n u

theorem integrable_phiT_mul (n : ℕ) {z : ℂ} (hz : z.im < -1 / 2) :
    Integrable fun u : ℝ => (phiT n u : ℂ) * Complex.exp (Complex.I * z * u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT_zero]
  have hc := thC_pos hn
  have h1 : 0 < (9 / 2 + Complex.I * z).re := by simp; linarith
  have h2 : 0 < (5 / 2 + Complex.I * z).re := by simp; linarith
  simp_rw [phiT_split]
  exact ((integrable_exp_theta_term h1 hc).const_mul _).sub
    ((integrable_exp_theta_term h2 hc).const_mul _)

theorem one_div_thC_cpow {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (1 / (thC n : ℂ)) ^ (w / 2) = (π : ℂ) ^ (-w / 2) * (1 / (n : ℂ) ^ w) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := thC_pos hn
  rw [show (1 / (thC n : ℂ)) = ((1 / thC n : ℝ) : ℂ) by push_cast; rfl,
    cpow_pos_real (by positivity), cpow_pos_real pi_pos,
    show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_pos_real hn', one_div (Complex.exp _),
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  simp only [thC]
  rw [one_div, Real.log_inv, Real.log_mul pi_pos.ne' (by positivity), Real.log_pow]
  push_cast; ring

/-- **Riemann's formula on a half-plane**: `∫ Φ(u) e^{izu} du = ξ(½ + iz)/2` for `Im z < −½`. -/
theorem integral_RPhi_halfplane {z : ℂ} (hz : z.im < -1 / 2) :
    ∫ u : ℝ, (RPhi u : ℂ) * Complex.exp (Complex.I * z * u) = Xi z / 2 := by
  set s := 1 / 2 + Complex.I * z with hs
  have hsre : 1 < s.re := by simp [hs]; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; simp at hsre
  have H := hasSum_integral_of_summable_integral_norm
    (F := fun n (u : ℝ) => (phiT n u : ℂ) * Complex.exp (Complex.I * z * u))
    (fun n => integrable_phiT_mul n hz) (summable_integral_norm_phiT hz)
  have e1 : (fun u : ℝ => ∑' n : ℕ, (phiT n u : ℂ) * Complex.exp (Complex.I * z * u))
      = fun u => (RPhi u : ℂ) * Complex.exp (Complex.I * z * u) := by
    funext u; rw [tsum_mul_right, RPhi, Complex.ofReal_tsum]
  rw [e1] at H
  rw [← H.tsum_eq]
  have e2 : ∀ n : ℕ, (∫ u : ℝ, (phiT n u : ℂ) * Complex.exp (Complex.I * z * u))
      = s * (s - 1) / 4 * Complex.Gamma (s / 2) * (π : ℂ) ^ (-s / 2) * (1 / (n : ℂ) ^ s) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [phiT_zero, Complex.zero_cpow hs0]
    rw [integral_phiT hn hz, ← hs, one_div_thC_cpow hn]; ring
  simp_rw [e2]
  rw [tsum_mul_left, Xi, xi_eq hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hsre]
  ring

/-! ## The theta terms and their derivatives -/

/-- `f_n(u) = e^{u/2 − πn²e^{2u}}`. -/
def thF (n : ℕ) (u : ℝ) : ℝ := Real.exp (u / 2 - thC n * Real.exp (2 * u))
def thF1 (n : ℕ) (u : ℝ) : ℝ := (1 / 2 - 2 * thC n * Real.exp (2 * u)) * thF n u
def thF2 (n : ℕ) (u : ℝ) : ℝ :=
  ((1 / 2 - 2 * thC n * Real.exp (2 * u)) ^ 2 - 4 * thC n * Real.exp (2 * u)) * thF n u

theorem hasDerivAt_exp_two (u : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * y)) (Real.exp (2 * u) * (2 * 1)) u :=
  ((hasDerivAt_id' u).const_mul 2).exp

theorem hasDerivAt_thF (n : ℕ) (u : ℝ) : HasDerivAt (thF n) (thF1 n u) u := by
  have h3 := ((hasDerivAt_id' u).div_const 2).sub ((hasDerivAt_exp_two u).const_mul (thC n))
  have := h3.exp
  unfold thF thF1
  convert this using 1
  simp only [thF, Pi.sub_apply]; ring

theorem hasDerivAt_thF1 (n : ℕ) (u : ℝ) : HasDerivAt (thF1 n) (thF2 n u) u := by
  have hq := (hasDerivAt_const u (1 / 2 : ℝ)).sub ((hasDerivAt_exp_two u).const_mul (2 * thC n))
  have := hq.mul (hasDerivAt_thF n u)
  unfold thF1 thF2
  convert this using 1
  simp only [thF1, Pi.sub_apply]; ring

theorem phiT_eq (n : ℕ) (u : ℝ) : phiT n u = (thF2 n u - thF n u / 4) / 2 := by
  unfold phiT thF2 thF
  rw [show Real.exp (4 * u) = Real.exp (2 * u) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
  ring

/-! ## Uniform bounds on `|u| ≤ R` -/

theorem thC_nonneg (n : ℕ) : 0 ≤ thC n := by unfold thC; positivity

theorem thF_le {R u : ℝ} (hu : |u| ≤ R) (n : ℕ) :
    thF n u ≤ Real.exp (R / 2) * Real.exp (-(π * Real.exp (-2 * R)) * n) := by
  unfold thF
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hu1 : u ≤ R := (le_abs_self u).trans hu
  have hu2 : -R ≤ u := by linarith [neg_abs_le u]
  have he : Real.exp (-2 * R) ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by linarith)
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  have hp : 0 ≤ π * Real.exp (-2 * R) := by positivity
  have : π * Real.exp (-2 * R) * n ≤ thC n * Real.exp (2 * u) := by
    unfold thC
    calc π * Real.exp (-2 * R) * n ≤ π * Real.exp (-2 * R) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hn hp
      _ = π * (n : ℝ) ^ 2 * Real.exp (-2 * R) := by ring
      _ ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * u) :=
          mul_le_mul_of_nonneg_left he (by positivity)
  linarith

theorem thq_le {R u : ℝ} (hu : |u| ≤ R) (n : ℕ) :
    0 ≤ thC n * Real.exp (2 * u) ∧ thC n * Real.exp (2 * u) ≤ π * Real.exp (2 * R) * (n : ℝ) ^ 2 := by
  refine ⟨mul_nonneg (thC_nonneg n) (Real.exp_pos _).le, ?_⟩
  have hu1 : u ≤ R := (le_abs_self u).trans hu
  unfold thC
  have := Real.exp_le_exp.2 (show 2 * u ≤ 2 * R by linarith)
  calc π * (n : ℝ) ^ 2 * Real.exp (2 * u) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * R) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem one_add_sq_le {q Q : ℝ} {n : ℕ} (hq0 : 0 ≤ q) (hq : q ≤ Q * (n : ℝ) ^ 2) (hQ : 0 ≤ Q) :
    (1 + q) ^ 2 ≤ 2 * (1 + Q) ^ 2 * ((n : ℝ) ^ 4 + 1) := by
  have h1 : 1 + q ≤ (1 + Q) * (1 + (n : ℝ) ^ 2) := by nlinarith [sq_nonneg (n : ℝ)]
  have h2 : (1 + (n : ℝ) ^ 2) ^ 2 ≤ 2 * ((n : ℝ) ^ 4 + 1) := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
  have h3 : (1 + q) ^ 2 ≤ ((1 + Q) * (1 + (n : ℝ) ^ 2)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  calc (1 + q) ^ 2 ≤ ((1 + Q) * (1 + (n : ℝ) ^ 2)) ^ 2 := h3
    _ = (1 + Q) ^ 2 * (1 + (n : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (1 + Q) ^ 2 * (2 * ((n : ℝ) ^ 4 + 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The common majorant `K (n⁴ + 1) e^{−r n}`. -/
def thMaj (K r : ℝ) (n : ℕ) : ℝ := K * (((n : ℝ) ^ 4 + 1) * Real.exp (-r * n))

theorem summable_thMaj (K : ℝ) {r : ℝ} (hr : 0 < r) : Summable (thMaj K r) := by
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 hr
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  refine ((h4.add h0).mul_left K).congr fun n => ?_
  simp only [thMaj, pow_zero, one_mul]; ring

/-- One bound for `f_n`, `f_n'`, `f_n''` and `φ_n` on `|u| ≤ R`. -/
theorem th_all_le {R u : ℝ} (hu : |u| ≤ R) (n : ℕ) :
    let K := 16 * (1 + π * Real.exp (2 * R)) ^ 2 * Real.exp (R / 2)
    let r := π * Real.exp (-2 * R)
    |thF n u| ≤ thMaj K r n ∧ |thF1 n u| ≤ thMaj K r n ∧ |thF2 n u| ≤ thMaj K r n ∧
      |phiT n u| ≤ thMaj K r n := by
  intro K r
  set q := thC n * Real.exp (2 * u)
  set Q := π * Real.exp (2 * R)
  obtain ⟨hq0, hq⟩ := thq_le hu n
  have hQ : 0 ≤ Q := by positivity
  have hsq := one_add_sq_le hq0 hq hQ
  have hf := thF_le hu n
  have hf0 : 0 ≤ thF n u := (Real.exp_pos _).le
  set B := Real.exp (R / 2) * Real.exp (-(π * Real.exp (-2 * R)) * n)
  have hB : thMaj K r n = 16 * ((1 + Q) ^ 2 * ((n : ℝ) ^ 4 + 1)) * B := by
    simp only [thMaj, K, r, B, Q]; ring
  have hB0 : 0 ≤ B := by positivity
  have hW : (1 + q) ^ 2 * B ≤ 2 * ((1 + Q) ^ 2 * ((n : ℝ) ^ 4 + 1)) * B := by
    have := mul_le_mul_of_nonneg_right hsq hB0; linarith
  have hfB : (1 + q) ^ 2 * thF n u ≤ (1 + q) ^ 2 * B := mul_le_mul_of_nonneg_left hf (sq_nonneg _)
  have hone : thF n u ≤ (1 + q) ^ 2 * thF n u := by nlinarith [sq_nonneg q]
  have hW0 : 0 ≤ (1 + Q) ^ 2 * ((n : ℝ) ^ 4 + 1) * B := by positivity
  rw [hB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg hf0]; nlinarith
  · unfold thF1
    rw [abs_mul, abs_of_nonneg hf0]
    have : |1 / 2 - 2 * thC n * Real.exp (2 * u)| ≤ 2 * (1 + q) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg q]
    have := mul_le_mul_of_nonneg_right this hf0
    nlinarith
  · unfold thF2
    rw [abs_mul, abs_of_nonneg hf0]
    have : |(1 / 2 - 2 * thC n * Real.exp (2 * u)) ^ 2 - 4 * thC n * Real.exp (2 * u)|
        ≤ 8 * (1 + q) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg q]
    have := mul_le_mul_of_nonneg_right this hf0
    nlinarith
  · rw [phiT_eq]
    unfold thF2
    have : |(((1 / 2 - 2 * thC n * Real.exp (2 * u)) ^ 2 - 4 * thC n * Real.exp (2 * u)) * thF n u
        - thF n u / 4) / 2| ≤ 8 * (1 + q) ^ 2 * thF n u := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) hf0,
        mul_nonneg hq0 hf0]
    nlinarith

/-! ## Termwise differentiation, the theta kernel, and evenness -/

theorem abs_le_of_mem_Ioo {y v : ℝ} (hv : v ∈ Ioo (y - 1) (y + 1)) : |v| ≤ |y| + 1 := by
  have := abs_sub_abs_le_abs_sub v y
  have : |v - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
  linarith

theorem thMaj_summable_at (y : ℝ) :
    Summable (thMaj (16 * (1 + π * Real.exp (2 * (|y| + 1))) ^ 2 * Real.exp ((|y| + 1) / 2))
      (π * Real.exp (-2 * (|y| + 1)))) :=
  summable_thMaj _ (by positivity)

theorem summable_thF (u : ℝ) : Summable fun n => thF n u :=
  Summable.of_norm_bounded (thMaj_summable_at u) fun n => by
    rw [Real.norm_eq_abs]; exact (th_all_le (show |u| ≤ |u| + 1 by linarith) n).1

theorem summable_thF2 (u : ℝ) : Summable fun n => thF2 n u :=
  Summable.of_norm_bounded (thMaj_summable_at u) fun n => by
    rw [Real.norm_eq_abs]; exact (th_all_le (show |u| ≤ |u| + 1 by linarith) n).2.2.1

theorem summable_phiT (u : ℝ) : Summable fun n => phiT n u :=
  Summable.of_norm_bounded (thMaj_summable_at u) fun n => by
    rw [Real.norm_eq_abs]; exact (th_all_le (show |u| ≤ |u| + 1 by linarith) n).2.2.2

theorem hasDerivAt_thG (y : ℝ) :
    HasDerivAt (fun u => ∑' n, thF n u) (∑' n, thF1 n y) y :=
  hasDerivAt_tsum_of_isPreconnected (thMaj_summable_at y) isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => hasDerivAt_thF n v)
    (fun n v hv => by rw [Real.norm_eq_abs]; exact (th_all_le (abs_le_of_mem_Ioo hv) n).2.1)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith) (summable_thF y)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)

theorem hasDerivAt_thG1 (y : ℝ) :
    HasDerivAt (fun u => ∑' n, thF1 n u) (∑' n, thF2 n y) y :=
  hasDerivAt_tsum_of_isPreconnected (thMaj_summable_at y) isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => hasDerivAt_thF1 n v)
    (fun n v hv => by rw [Real.norm_eq_abs]; exact (th_all_le (abs_le_of_mem_Ioo hv) n).2.2.1)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
    (Summable.of_norm_bounded (thMaj_summable_at y) fun n => by
      rw [Real.norm_eq_abs]; exact (th_all_le (show |y| ≤ |y| + 1 by linarith) n).2.1)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)

/-- `e^{u/2} θ(e^{2u}) = 2Σ_{n≥0} f_n(u) − e^{u/2}`, with `θ` Mathlib's `evenKernel 0`. -/
theorem theta_eq_sum (u : ℝ) :
    Real.exp (u / 2) * evenKernel 0 (Real.exp (2 * u))
      = 2 * (∑' n, thF n u) - Real.exp (u / 2) := by
  have h := (hasSum_int_evenKernel (0 : ℝ) (Real.exp_pos (2 * u))).nat_add_neg
  simp only [add_zero, QuotientAddGroup.mk_zero, Int.cast_zero, zero_pow two_ne_zero, mul_zero,
    zero_mul, Real.exp_zero, Int.cast_natCast, Int.cast_neg, neg_sq] at h
  have h2 := h.mul_left (Real.exp (u / 2))
  have e : (fun n : ℕ => Real.exp (u / 2) * (Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u))
      + Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u)))) = fun n => 2 * thF n u := by
    funext n; simp only [thF, thC]
    rw [show u / 2 - π * (n : ℝ) ^ 2 * Real.exp (2 * u) = u / 2 + (-π * (n : ℝ) ^ 2 * Real.exp (2 * u))
      by ring, Real.exp_add]; ring
  rw [e] at h2
  rw [tsum_mul_left.symm, h2.tsum_eq]; ring

/-- `F(u) = e^{u/2} θ(e^{2u})` is even (the theta functional equation). -/
theorem theta_even (u : ℝ) :
    Real.exp (-u / 2) * evenKernel 0 (Real.exp (2 * -u))
      = Real.exp (u / 2) * evenKernel 0 (Real.exp (2 * u)) := by
  rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero]
  have h1 : Real.exp (2 * -u) ^ (1 / 2 : ℝ) = Real.exp (-u) := by
    rw [← Real.exp_mul]; congr 1; ring
  have h2 : 1 / Real.exp (2 * -u) = Real.exp (2 * u) := by
    rw [one_div, ← Real.exp_neg]; congr 1; ring
  rw [h1, h2, one_div, ← Real.exp_neg, ← mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- The even function `F = 2G − e^{u/2}` and its first two derivatives. -/
def thFF (u : ℝ) : ℝ := 2 * (∑' n, thF n u) - Real.exp (u / 2)
def thFF1 (u : ℝ) : ℝ := 2 * (∑' n, thF1 n u) - Real.exp (u / 2) / 2
def thFF2 (u : ℝ) : ℝ := 2 * (∑' n, thF2 n u) - Real.exp (u / 2) / 4

theorem thFF_even (u : ℝ) : thFF (-u) = thFF u := by
  unfold thFF
  rw [← theta_eq_sum, ← theta_eq_sum, ← theta_even u]

theorem hasDerivAt_thFF (u : ℝ) : HasDerivAt thFF (thFF1 u) u := by
  have := ((hasDerivAt_thG u).const_mul 2).sub (((hasDerivAt_id' u).div_const 2).exp)
  unfold thFF thFF1
  convert this using 1
  ring

theorem hasDerivAt_thFF1 (u : ℝ) : HasDerivAt thFF1 (thFF2 u) u := by
  have := ((hasDerivAt_thG1 u).const_mul 2).sub
    ((((hasDerivAt_id' u).div_const 2).exp).div_const 2)
  unfold thFF1 thFF2
  convert this using 1; ring

theorem thFF1_odd (u : ℝ) : thFF1 (-u) = -thFF1 u := by
  have h1 : HasDerivAt (fun v => thFF (-v)) (-thFF1 (-u)) u := by
    have := (hasDerivAt_thFF (-u)).comp u (hasDerivAt_neg u)
    convert this using 1
    · funext v; simp [Function.comp]
    · ring
  have e : (fun v => thFF (-v)) = thFF := funext thFF_even
  rw [e] at h1
  have := h1.unique (hasDerivAt_thFF u)
  linarith

theorem thFF2_even (u : ℝ) : thFF2 (-u) = thFF2 u := by
  have h1 : HasDerivAt (fun v => -thFF1 (-v)) (-(-thFF2 (-u))) u := by
    have := ((hasDerivAt_thFF1 (-u)).comp u (hasDerivAt_neg u)).neg
    convert this using 1
    · funext v; simp [Function.comp]
    · ring
  have e : (fun v => -thFF1 (-v)) = thFF1 := funext fun v => by rw [thFF1_odd]; ring
  rw [e] at h1
  have := h1.unique (hasDerivAt_thFF1 u)
  linarith

/-- `Φ = (F'' − F/4)/4`. -/
theorem RPhi_eq (u : ℝ) : RPhi u = (thFF2 u - thFF u / 4) / 4 := by
  unfold RPhi thFF2 thFF
  have e : (fun n => phiT n u) = fun n => (thF2 n u - thF n u / 4) / 2 := funext fun n => phiT_eq n u
  rw [e, tsum_div_const, (summable_thF2 u).tsum_sub ((summable_thF u).div_const 4), tsum_div_const]
  ring

/-- **Riemann's kernel is even.** -/
theorem RPhi_even (u : ℝ) : RPhi (-u) = RPhi u := by
  rw [RPhi_eq, RPhi_eq, thFF2_even, thFF_even]

/-! ## Decay -/

theorem integrable_exp_neg_abs {b : ℝ} (hb : 0 < b) : Integrable fun u : ℝ => Real.exp (-b * |u|) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic hb 0).congr_fun (fun u (hu : u ≤ 0) => ?_) measurableSet_Iic
    simp only; rw [abs_of_nonpos hu]; ring_nf
  · refine (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
    simp only; rw [abs_of_pos hu]

theorem phiT_le_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |phiT n u| ≤ ((2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * Real.exp (-(π / 2) * (n : ℝ) ^ 2))
      * (Real.exp (2 * u) ^ 2 * Real.exp (u / 2) * Real.exp (-(π / 2) * Real.exp (2 * u))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT_zero]
  set X := Real.exp (2 * u)
  have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have e4 : Real.exp (4 * u) = X ^ 2 := by simp only [X]; rw [← Real.exp_nat_mul]; ring_nf
  unfold phiT thC
  rw [e4, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (u / 2 - π * (n : ℝ) ^ 2 * X)
      ≤ Real.exp (u / 2) * (Real.exp (-(π / 2) * (n : ℝ) ^ 2) * Real.exp (-(π / 2) * X)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : ((n : ℝ) ^ 2 - 1 / 2) * (X - 1 / 2) ≥ 1 / 4 := by nlinarith
    nlinarith [pi_pos]
  have hpoly : |2 * (π * (n : ℝ) ^ 2) ^ 2 * X ^ 2 - 3 * (π * (n : ℝ) ^ 2) * X|
      ≤ (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2 := by
    have hX2 : X ≤ X ^ 2 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [pi_pos, sq_nonneg (n : ℝ), mul_nonneg pi_pos.le
      (sq_nonneg (n : ℝ)), mul_le_mul_of_nonneg_left hX2 (mul_nonneg pi_pos.le (sq_nonneg (n : ℝ)))]
  have hA : 0 ≤ (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2 := by positivity
  calc |2 * (π * (n : ℝ) ^ 2) ^ 2 * X ^ 2 - 3 * (π * (n : ℝ) ^ 2) * X|
        * Real.exp (u / 2 - π * (n : ℝ) ^ 2 * X)
      ≤ ((2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2)
        * (Real.exp (u / 2) * (Real.exp (-(π / 2) * (n : ℝ) ^ 2) * Real.exp (-(π / 2) * X))) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le hA
    _ = _ := by ring

theorem summable_phiT_coef :
    Summable fun n : ℕ => (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2)
      * Real.exp (-(π / 2) * (n : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_thMaj (2 * π ^ 2 + 3 * π) (show (0 : ℝ) < π / 2 by positivity))
  simp only [thMaj]
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  have he : Real.exp (-(π / 2) * (n : ℝ) ^ 2) ≤ Real.exp (-(π / 2) * n) :=
    Real.exp_le_exp.2 (by nlinarith [pi_pos])
  have hp : 2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2 ≤ (2 * π ^ 2 + 3 * π) * ((n : ℝ) ^ 4 + 1) := by
    have : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + 1 := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
    nlinarith [pi_pos, sq_nonneg (n : ℝ)]
  calc _ ≤ (2 * π ^ 2 + 3 * π) * ((n : ℝ) ^ 4 + 1) * Real.exp (-(π / 2) * n) :=
        mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **Decay of Riemann's kernel at every exponential rate**: `|Φ(u)| ≤ C e^{−B|u|}`. -/
theorem RPhi_decay_gen (B : ℝ) : ∃ C, 0 ≤ C ∧ ∀ u, |RPhi u| ≤ C * Real.exp (-B * |u|) := by
  set S := ∑' n : ℕ, (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2)
      * Real.exp (-(π / 2) * (n : ℝ) ^ 2)
  have hS : 0 ≤ S := tsum_nonneg fun n => by positivity
  set m' := ⌈B / 2⌉₊
  set m := m' + 3
  set K : ℝ := (m.factorial : ℝ) * (2 / π) ^ m
  set C := S * K
  refine ⟨C, by positivity, ?_⟩
  have hpos : ∀ u, 0 ≤ u → |RPhi u| ≤ C * Real.exp (-B * u) := by
    intro u hu
    set X := Real.exp (2 * u)
    have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
    have hX0 : 0 < X := by linarith
    set Bd := X ^ 2 * Real.exp (u / 2) * Real.exp (-(π / 2) * X)
    have h1 : |RPhi u| ≤ S * Bd := by
      unfold RPhi
      have habs := (summable_phiT u).abs
      calc |∑' n, phiT n u| ≤ ∑' n, |phiT n u| := by
            rw [← Real.norm_eq_abs]
            exact (norm_tsum_le_tsum_norm (by simpa using habs)).trans (le_of_eq (by simp))
        _ ≤ ∑' n : ℕ, (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2)
              * Real.exp (-(π / 2) * (n : ℝ) ^ 2) * Bd :=
            habs.tsum_le_tsum (fun n => phiT_le_pos hu n) (summable_phiT_coef.mul_right Bd)
        _ = S * Bd := tsum_mul_right
    have hu2 : Real.exp (u / 2) ≤ X := Real.exp_le_exp.2 (by linarith)
    have hBu : Real.exp (B * u) ≤ X ^ m' := by
      have hm : B ≤ 2 * m' := by
        have := Nat.le_ceil (B / 2); linarith
      simp only [X]; rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hE : X ^ m * Real.exp (-(π / 2) * X) ≤ K := by
      have h4 := Real.pow_div_factorial_le_exp (π / 2 * X) (by positivity) m
      have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
      rw [div_le_iff₀ hf] at h4
      have hpe : Real.exp (-(π / 2) * X) * Real.exp (π / 2 * X) = 1 := by
        rw [← Real.exp_add]; simp
      have hq : X ^ m = (π / 2 * X) ^ m * (2 / π) ^ m := by
        rw [← mul_pow]; congr 1; field_simp
      rw [hq]
      calc (π / 2 * X) ^ m * (2 / π) ^ m * Real.exp (-(π / 2) * X)
          ≤ Real.exp (π / 2 * X) * m.factorial * (2 / π) ^ m * Real.exp (-(π / 2) * X) := by
            gcongr
        _ = (m.factorial : ℝ) * (2 / π) ^ m * (Real.exp (-(π / 2) * X) * Real.exp (π / 2 * X)) := by
            ring
        _ = K := by rw [hpe, mul_one]
    have hBd : Bd * Real.exp (B * u) ≤ K := by
      have e : X ^ m = X ^ 2 * X * X ^ m' := by simp only [m]; ring
      calc Bd * Real.exp (B * u)
          = X ^ 2 * Real.exp (u / 2) * Real.exp (B * u) * Real.exp (-(π / 2) * X) := by
            simp only [Bd]; ring
        _ ≤ X ^ 2 * X * X ^ m' * Real.exp (-(π / 2) * X) := by
            gcongr
        _ = X ^ m * Real.exp (-(π / 2) * X) := by rw [e]
        _ ≤ K := hE
    have hinv : Real.exp (B * u) * Real.exp (-B * u) = 1 := by rw [← Real.exp_add]; simp
    have hBd' : Bd ≤ K * Real.exp (-B * u) := by
      calc Bd = Bd * Real.exp (B * u) * Real.exp (-B * u) := by rw [mul_assoc, hinv, mul_one]
        _ ≤ K * Real.exp (-B * u) := mul_le_mul_of_nonneg_right hBd (Real.exp_pos _).le
    calc |RPhi u| ≤ S * Bd := h1
      _ ≤ S * (K * Real.exp (-B * u)) := mul_le_mul_of_nonneg_left hBd' hS
      _ = C * Real.exp (-B * u) := by simp only [C]; ring
  intro u
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact hpos u hu
  · rw [abs_of_neg hu, ← RPhi_even]; exact hpos (-u) (by linarith)

/-- **Decay of Riemann's kernel**: `|Φ(u)| ≤ C e^{−2|u|}`. -/
theorem RPhi_decay : ∃ C, 0 ≤ C ∧ ∀ u, |RPhi u| ≤ C * Real.exp (-2 * |u|) :=
  RPhi_decay_gen 2

theorem continuous_RPhi : Continuous RPhi := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : ContinuousOn RPhi (Ioo (y - 1) (y + 1)) :=
    continuousOn_tsum (fun n => by unfold phiT; fun_prop) (thMaj_summable_at y)
      (fun n v hv => by rw [Real.norm_eq_abs]; exact (th_all_le (abs_le_of_mem_Ioo hv) n).2.2.2)
  exact hc.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-! ## Analytic continuation to all of `ℂ` -/

/-- `Φ̂(z) = ∫ Φ(u) e^{izu} du`. -/
def RPhiHat (z : ℂ) : ℂ := ∫ u : ℝ, (RPhi u : ℂ) * Complex.exp (Complex.I * z * u)

theorem norm_RPhi_exp_le {C M : ℝ} (hC : ∀ u, |RPhi u| ≤ C * Real.exp (-(M + 1) * |u|)) {z : ℂ}
    (hz : |z.im| ≤ M) (u : ℝ) :
    ‖(RPhi u : ℂ) * Complex.exp (Complex.I * z * u)‖ ≤ C * Real.exp (-1 * |u|) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have e : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [e]
  have h1 : Real.exp (-(z.im * u)) ≤ Real.exp (M * |u|) := by
    apply Real.exp_le_exp.2
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ M * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  calc |RPhi u| * Real.exp (-(z.im * u)) ≤ (C * Real.exp (-(M + 1) * |u|)) * Real.exp (M * |u|) :=
        mul_le_mul (hC u) h1 (Real.exp_pos _).le (le_trans (abs_nonneg _) (hC u))
    _ = C * Real.exp (-1 * |u|) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem integrable_RPhi_exp (z : ℂ) :
    Integrable fun u : ℝ => (RPhi u : ℂ) * Complex.exp (Complex.I * z * u) := by
  obtain ⟨C, hC0, hC⟩ := RPhi_decay_gen (|z.im| + 1)
  refine ((integrable_exp_neg_abs one_pos).const_mul C).mono'
    (show Continuous (fun u : ℝ => (RPhi u : ℂ) * Complex.exp (Complex.I * z * u)) by
      have := continuous_RPhi; fun_prop).aestronglyMeasurable
    (Eventually.of_forall fun u => norm_RPhi_exp_le hC le_rfl u)

/-- **Tail bound** on the strip `|Im z| ≤ M`: `|Φ̂(z) − ∫_{−a}^{a} Φ e^{izu}| ≤ D e^{−a/2}`. -/
theorem norm_RPhiHat_sub_le (M : ℝ) : ∃ D, ∀ {a : ℝ}, 0 ≤ a → ∀ {z : ℂ}, |z.im| ≤ M →
    ‖RPhiHat z - ghatC RPhi a z‖ ≤ D * Real.exp (-(a / 2)) := by
  obtain ⟨C, hC0, hC⟩ := RPhi_decay_gen (M + 1)
  set I0 := ∫ u : ℝ, Real.exp (-(1 / 2) * |u|)
  refine ⟨C * I0, fun {a} ha {z} hz => ?_⟩
  set f : ℝ → ℂ := fun u => (RPhi u : ℂ) * Complex.exp (Complex.I * z * u)
  have hf : Integrable f := integrable_RPhi_exp z
  have hs : MeasurableSet (Ioc (-a) a) := measurableSet_Ioc
  have e : RPhiHat z - ghatC RPhi a z = ∫ u in (Ioc (-a) a)ᶜ, f u := by
    have := integral_add_compl hs hf
    unfold RPhiHat ghatC
    rw [intervalIntegral.integral_of_le (by linarith)]
    rw [← this]; ring
  rw [e]
  have hg : Integrable fun u : ℝ => C * Real.exp (-(a / 2)) * Real.exp (-(1 / 2) * |u|) :=
    (integrable_exp_neg_abs (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  calc ‖∫ u in (Ioc (-a) a)ᶜ, f u‖ ≤ ∫ u in (Ioc (-a) a)ᶜ, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in (Ioc (-a) a)ᶜ, C * Real.exp (-(a / 2)) * Real.exp (-(1 / 2) * |u|) := by
        refine setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs.compl fun u hu => ?_
        have hua : a ≤ |u| := by
          simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hu
          rcases hu with hu | hu
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        refine (norm_RPhi_exp_le hC hz u).trans ?_
        rw [mul_assoc, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ hC0
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ ∫ u : ℝ, C * Real.exp (-(a / 2)) * Real.exp (-(1 / 2) * |u|) :=
        setIntegral_le_integral hg (Eventually.of_forall fun u => by positivity)
    _ = C * I0 * Real.exp (-(a / 2)) := by rw [integral_const_mul]; ring

/-- The closed strip `|Im z| ≤ M`. -/
def closedStrip (M : ℝ) : Set ℂ := {z | |z.im| ≤ M}

/-- Truncated transforms converge to `Φ̂` uniformly on every strip `|Im z| ≤ M`. -/
theorem tendstoUniformlyOn_ghatC_RPhi (M : ℝ) {a : ℕ → ℝ}
    (hlim : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n z => ghatC RPhi (a n) z) RPhiHat atTop (closedStrip M) := by
  obtain ⟨D, hD⟩ := norm_RPhiHat_sub_le M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun n => D * Real.exp (-(a n / 2))) atTop (𝓝 (D * 0)) := by
    refine (Real.tendsto_exp_atBot.comp ?_).const_mul D
    exact tendsto_neg_atTop_atBot.comp (hlim.atTop_div_const (by norm_num))
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (Iio_mem_nhds hε), hlim.eventually (eventually_ge_atTop 0)]
    with n hn ha z hz
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hD ha hz) hn

/-- `Φ̂` is entire. -/
theorem differentiable_RPhiHat : Differentiable ℂ RPhiHat := by
  intro z
  set M := |z.im| + 1
  set U : Set ℂ := {w | |w.im| < M}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hzU : z ∈ U := by simp [U, M]
  have hUs : U ⊆ closedStrip M := fun w hw => show |w.im| ≤ M from le_of_lt hw
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := ((tendstoUniformlyOn_ghatC_RPhi M hlim).mono hUs).tendstoLocallyUniformlyOn
  have hd := h.differentiableOn (Eventually.of_forall fun n =>
    (ghatC_differentiable (continuous_RPhi.intervalIntegrable _ _)).differentiableOn) hU
  exact hd.differentiableAt (hU.mem_nhds hzU)

/-- **Riemann's formula**: `∫ Φ(u) e^{izu} du = Ξ(z)/2` for every `z ∈ ℂ`. -/
theorem RPhiHat_eq (z : ℂ) : RPhiHat z = Xi z / 2 := by
  have hA : AnalyticOnNhd ℂ RPhiHat univ :=
    differentiable_RPhiHat.differentiableOn.analyticOnNhd isOpen_univ
  have hB : AnalyticOnNhd ℂ (fun z => Xi z / 2) univ :=
    (differentiable_Xi.div_const 2).differentiableOn.analyticOnNhd isOpen_univ
  set z₀ : ℂ := ⟨0, -3 / 4⟩
  have hV : IsOpen {z : ℂ | z.im < -1 / 2} := isOpen_lt Complex.continuous_im continuous_const
  have hz₀V : z₀ ∈ {z : ℂ | z.im < -1 / 2} := by simp [z₀]; norm_num
  have heq : RPhiHat =ᶠ[𝓝 z₀] fun z => Xi z / 2 :=
    Filter.eventually_of_mem (hV.mem_nhds hz₀V) fun z hz => integral_RPhi_halfplane hz
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ z₀) heq (mem_univ z)

theorem memLp_RPhi : MemLp RPhi 2 volume := by
  obtain ⟨C, hC0, hC⟩ := RPhi_decay
  have hg : MemLp (fun u : ℝ => C * Real.exp (-2 * |u|)) 2 volume := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    refine ((integrable_exp_neg_abs (by norm_num : (0 : ℝ) < 4)).const_mul (C ^ 2)).congr
      (Eventually.of_forall fun u => ?_)
    simp only; rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  refine hg.of_le continuous_RPhi.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ C * Real.exp (-2 * |u|) from mul_nonneg hC0 (Real.exp_pos _).le)]
  exact hC u

/-- **`KernelApprox` holds for Riemann's kernel**, for any supports `a_n → ∞`. -/
theorem kernelApprox_RPhi {a : ℕ → ℝ} (hlim : Tendsto a atTop atTop) :
    KernelApprox a fun _ => RPhi := by
  refine ⟨fun _ => memLp_RPhi, 1 / 2, by norm_num, ?_⟩
  have hsub : stripSet ⊆ closedStrip 1 := fun z hz => by
    simp only [stripSet, Set.mem_ofPred_eq] at hz
    simp only [closedStrip, Set.mem_ofPred_eq]; linarith
  have h := (tendstoUniformlyOn_ghatC_RPhi 1 hlim).mono hsub
  have h2 : TendstoUniformlyOn (fun n z => ghatC RPhi (a n) z) (fun z => 1 / 2 * Xi z) atTop stripSet :=
    h.congr_right fun z _ => by rw [RPhiHat_eq]; ring
  exact h2.tendstoLocallyUniformlyOn

/-- **RH from `L²` closeness to Riemann's kernel**, with no unproved input other than the closeness:
if `a_n → ∞` and `√(2a_n) e^{b a_n} ‖σ_n·topGS(a_n) − Φ‖ → 0` for every `b < ½` (some signs and
scalings `σ_n ≠ 0`), the Riemann hypothesis holds. -/
theorem rh_of_close_RPhi {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hlim : Tendsto a atTop atTop)
    {σ : ℕ → ℝ} (hσ : ∀ n, σ n ≠ 0)
    (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => σ n * topGS (a n) t - RPhi t)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  rh_of_close_top ha (kernelApprox_RPhi hlim) hσ hclose

end Pilot1ca

#print axioms Pilot1ca.integral_exp_theta_term
#print axioms Pilot1ca.integral_phiT
#print axioms Pilot1ca.integral_RPhi_halfplane
#print axioms Pilot1ca.theta_even
#print axioms Pilot1ca.RPhi_even
#print axioms Pilot1ca.RPhi_decay_gen
#print axioms Pilot1ca.differentiable_RPhiHat
#print axioms Pilot1ca.RPhiHat_eq
#print axioms Pilot1ca.kernelApprox_RPhi
#print axioms Pilot1ca.rh_of_close_RPhi




