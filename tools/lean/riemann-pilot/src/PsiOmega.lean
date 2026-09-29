import Mathlib
import LandauLaplace
import HurwitzCross
import ZetaInputs
import ParityCont

/-! # A floor under the drift: `ψ(x) − x = Ω±(x^θ)` (round 220)

The wander ladder bounds `ψ(x) − x` from above (rungs 1–3, `external/pnt/`). This file gives the
matching floor, Landau's oscillation theorem, from Landau's theorem for Laplace transforms
(`LandauLaplace.lean`), applied to the Mellin integral with `φ = log` on `(1, ∞)`.

**The transform.** If `ε(ψ(x) − x) ≤ c·x^θ` for all `x > 1` (`ε ≠ 0`, `0 < θ < 1`), then
`A(x) = (c·x^θ − ε(ψ(x) − x))/x ≥ 0`, and for `Re s > 1`
`∫_1^∞ A(x)x^{−s}dx = c/(s − θ) + ε(ζ′/(sζ) + 1/(s − 1))` (`lap_eq_Fψ`). Mathlib supplies
`∫_1^∞ ψ(x)x^{−s−1}dx = L(Λ, s)/s` (`LSeries_eq_mul_integral`) and `L(Λ, s) = −ζ′/ζ`. With
`Z(s) = (s − 1)ζ(s)` (entire, `differentiable_Zr`) the right side is
`F(s) = c/(s − θ) + ε(Z′/(sZ) + 1/s)`, holomorphic on `Re s > θ` off the zeros of `ζ`.

**The argument** (`zeta_ne_zero_of_psi`).
1. The zeros of `ζ` are locally finite and none is real, so near every real `σ > θ` a thin strip is
   zero-free. Landau's theorem makes the integral converge on all of `Re s > θ`.
2. A zero `ρ` with `Re ρ > θ`: take the zero on its horizontal line with the largest real part,
   `ρ*`. To its right a thin strip is zero-free, so `F` equals the transform there, which is
   continuous at `ρ*`. But `Z = (s − ρ*)ⁿg` with `n ≥ 1`, `g(ρ*) ≠ 0`, so
   `F(s) = G(s) + (εn/ρ*)/(s − ρ*)` with `G` continuous at `ρ*`. That is a contradiction.

**Results.**
* `zeta_ne_zero_of_psi`: a one-sided bound `ε(ψ(x) − x) ≤ c·x^θ` on `(1, ∞)` makes `ζ ≠ 0` on
  `Re s > θ`.
* `psi_omega`: for every zero `ρ` of `ζ` and every `0 < θ < Re ρ`, `ψ(x) − x` exceeds `c·x^θ`, and
  falls below `−c·x^θ`, for arbitrarily large `x`, whatever `c`.
* `exists_zero_re_ge_half`: `ζ` has a zero with `½ ≤ Re ρ < 1`. From Hadamard's identity
  (`hadamard_zeta`), the sum over the zeros is `2 + γ − log 4π ≠ 0`, and `ρ ↦ 1 − ρ` preserves the
  zeros.
* `psi_omega_half`: hence, unconditionally, `ψ(x) − x = Ω±(x^θ)` for every `0 < θ < ½`.

These are classical (Landau 1905). No bearing on RH: the bound runs from zeros to oscillation.
-/

open Real Complex MeasureTheory Filter Topology Set Metric

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## `Z(s) = (s − 1)ζ(s)` is entire -/

/-- `Z(s) = (s − 1)ζ(s)`, with its limit `1` at `s = 1`. -/
def Zr : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem Zr_of_ne {s : ℂ} (hs : s ≠ 1) : Zr s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem Zr_eventuallyEq {s : ℂ} (hs : s ≠ 1) : Zr =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w :=
  (eventually_ne_nhds hs).mono fun _ hw => Zr_of_ne hw

theorem differentiable_Zr : Differentiable ℂ Zr := by
  have hne : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Zr s := fun s hs =>
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
      (Zr_eventuallyEq hs)
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht using hne t ht
    · simpa only [Zr, continuousAt_update_same] using riemannZeta_residue_one
  · exact hne s hs

theorem Zr_eq_zero {s : ℂ} (h : Zr s = 0) : s ≠ 1 ∧ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [Zr] at h
  · rw [Zr_of_ne hs] at h
    exact ⟨hs, (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hs)⟩

theorem zeta_ne_zero_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- No real point `σ > 0` is a zero of `Z`. -/
theorem Zr_real_ne {σ : ℝ} (hσ : 0 < σ) : Zr σ ≠ 0 := fun h => by
  obtain ⟨h1, h0⟩ := Zr_eq_zero h
  rcases lt_or_ge σ 1 with hl | hl
  · exact zetaNoZeroInUnitInterval σ hσ hl h0
  · exact zeta_ne_zero_re_ge_one (by simpa using hl) h0

/-! ## The integrand -/

/-- `A(x) = (c·x^θ − ε(ψ(x) − x))/x`. -/
def Aψ (θ c ε : ℝ) (x : ℝ) : ℝ := (c * x ^ θ - ε * (Chebyshev.psi x - x)) / x

/-- The Mellin data: `μ = dx` on `(1, ∞)`, `φ = log`. -/
abbrev μ1 : Measure ℝ := volume.restrict (Ioi 1)

theorem measurable_Aψ (θ c ε : ℝ) : Measurable (Aψ θ c ε) := by
  unfold Aψ
  exact ((measurable_const.mul (measurable_id.pow_const θ)).sub
    (measurable_const.mul (Chebyshev.psi_mono.measurable.sub measurable_id))).div measurable_id

theorem hyp_Aψ {θ c ε : ℝ} (h : ∀ x : ℝ, 1 < x → ε * (Chebyshev.psi x - x) ≤ c * x ^ θ) :
    Hyp μ1 (Aψ θ c ε) Real.log where
  A_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) =>
    div_nonneg (by linarith [h x hx]) (by linarith))
  ph_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) =>
    Real.log_nonneg hx.le)
  A_meas := (measurable_Aψ θ c ε).aestronglyMeasurable
  ph_meas := Real.measurable_log.aestronglyMeasurable

theorem psi_div_le {x : ℝ} (hx : 1 ≤ x) : Chebyshev.psi x / x ≤ Real.log 4 + 4 := by
  rw [div_le_iff₀ (by linarith)]; exact Chebyshev.psi_le_const_mul_self (by linarith)

theorem abs_Aψ_le {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {x : ℝ} (hx : 1 ≤ x) :
    |Aψ θ c ε x| ≤ |c| + |ε| * (Real.log 4 + 4 + 1) := by
  have hx0 : 0 < x := by linarith
  have hp := psi_div_le hx
  have hp0 : 0 ≤ Chebyshev.psi x / x := div_nonneg (Chebyshev.psi_nonneg x) hx0.le
  have hxθ : x ^ θ / x ≤ 1 := by
    rw [div_le_one hx0]
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
      _ = x := Real.rpow_one x
  have hxθ0 : 0 ≤ x ^ θ / x := by positivity
  have e : Aψ θ c ε x = c * (x ^ θ / x) - ε * (Chebyshev.psi x / x) + ε := by
    unfold Aψ; field_simp; ring
  rw [e]
  have h1 : |c * (x ^ θ / x)| ≤ |c| := by
    rw [abs_mul, abs_of_nonneg hxθ0]; exact mul_le_of_le_one_right (abs_nonneg c) hxθ
  have h2 : |ε * (Chebyshev.psi x / x)| ≤ |ε| * (Real.log 4 + 4) := by
    rw [abs_mul, abs_of_nonneg hp0]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg ε)
  calc |c * (x ^ θ / x) - ε * (Chebyshev.psi x / x) + ε|
      ≤ |c * (x ^ θ / x)| + |ε * (Chebyshev.psi x / x)| + |ε| := by
        have := abs_add_le (c * (x ^ θ / x) - ε * (Chebyshev.psi x / x)) ε
        have := abs_sub (c * (x ^ θ / x)) (ε * (Chebyshev.psi x / x))
        linarith
    _ ≤ |c| + |ε| * (Real.log 4 + 4) + |ε| := by linarith
    _ = _ := by ring

theorem conv_Aψ_three {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) : Conv μ1 (Aψ θ c ε) Real.log 3 := by
  set K := |c| + |ε| * (Real.log 4 + 4 + 1)
  have hi : IntegrableOn (fun x : ℝ => K * x ^ (-3 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul K
  refine hi.mono' ((measurable_Aψ θ c ε).mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  have e : Real.exp (-3 * Real.log x) = x ^ (-3 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right (abs_Aψ_le hθ hθ1 hx.le) (by positivity)

/-! ## The transform for `Re s > 1` -/

theorem cexp_log {x : ℝ} (hx : 0 < x) (s : ℂ) : cexp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le]; ring_nf

theorem integrand_eq {θ c ε : ℝ} {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (Aψ θ c ε x : ℂ) * cexp (-s * (Real.log x : ℂ))
      = c * (x : ℂ) ^ ((θ : ℂ) - 1 - s) - ε * ((Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)))
        + ε * (x : ℂ) ^ (-s) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  rw [cexp_log hx]
  have e1 : (x : ℂ) ^ ((θ : ℂ) - 1 - s) = (x : ℂ) ^ (θ : ℂ) * (x : ℂ) ^ (-s) / x := by
    rw [show (θ : ℂ) - 1 - s = (θ : ℂ) + -s - 1 by ring, Complex.cpow_sub _ _ hx0,
      Complex.cpow_add _ _ hx0, Complex.cpow_one]
  have e2 : (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) / x := by
    rw [show -(s + 1) = -s - 1 by ring, Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  have e3 : ((x ^ θ : ℝ) : ℂ) = (x : ℂ) ^ (θ : ℂ) := Complex.ofReal_cpow hx.le θ
  rw [e1, e2]
  unfold Aψ
  push_cast
  rw [e3]
  field_simp
  ring

theorem psi_sum_eq (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) = (Chebyshev.psi t : ℂ) := by
  unfold Chebyshev.psi; rw [← Finset.Icc_succ_left_eq_Ioc]; push_cast; rfl

/-- **`∫_1^∞ ψ(x)x^{−s−1}dx = L(Λ, s)/s`** for `Re s > 1`. -/
theorem integral_psi {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℂ))
      =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    rw [show (∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℂ))
        = ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ)⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) by
      rw [Nat.floor_natCast], psi_sum_eq, Complex.norm_real, Real.norm_of_nonneg
      (Chebyshev.psi_nonneg _), Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  have H := LSeries_eq_mul_integral _ zero_le_one (by simpa using hs)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hO
  simp_rw [psi_sum_eq] at H
  rw [H]; field_simp

theorem integrableOn_psi {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => (Real.log 4 + 4) * x ^ (-s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  · refine ((Complex.continuous_ofReal.measurable.comp Chebyshev.psi_mono.measurable).mul
      ?_).aestronglyMeasurable.restrict
    exact (Complex.continuous_ofReal.measurable).pow_const _
  · have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg x),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    have hp := Chebyshev.psi_le_const_mul_self hx0.le
    have e : x ^ (-s.re - 1) = x ^ (-s.re) / x := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [e]
    calc Chebyshev.psi x * (x ^ (-s.re) / x) ≤ (Real.log 4 + 4) * x * (x ^ (-s.re) / x) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by field_simp

/-- `F(s) = c/(s − θ) + ε(Z′/(sZ) + 1/s)`. -/
def Fψ (θ c ε : ℝ) (s : ℂ) : ℂ := c / (s - θ) + ε * (deriv Zr s / (s * Zr s) + 1 / s)

theorem deriv_Zr {s : ℂ} (hs : s ≠ 1) :
    deriv Zr s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  rw [(Zr_eventuallyEq hs).deriv_eq]
  have h : HasDerivAt (fun w => (w - 1) * riemannZeta w)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]; ring

/-- **The transform equals `F` for `Re s > 1`.** -/
theorem lap_eq_Fψ {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {s : ℂ} (hs : 1 < s.re) :
    lap μ1 (Aψ θ c ε) Real.log s = Fψ θ c ε s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hsθ : s - θ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_re_ge_one hs.le
  have i1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((θ : ℂ) - 1 - s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have i2 := integrableOn_psi hs
  have i3 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  unfold lap
  rw [setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => integrand_eq (by linarith) s]
  have i12 : IntegrableOn (fun x : ℝ => (c : ℂ) * (x : ℂ) ^ ((θ : ℂ) - 1 - s)
      - ε * ((Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)))) (Ioi 1) :=
    (i1.const_mul _).sub (i2.const_mul _)
  rw [integral_add i12 (i3.const_mul _), integral_sub (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_psi hs,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  unfold Fψ
  rw [deriv_Zr hs1, Zr_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have h1 : (θ : ℂ) - 1 - s + 1 ≠ 0 := by rw [show (θ : ℂ) - 1 - s + 1 = -(s - θ) by ring]; exact neg_ne_zero.2 hsθ
  have h2 : -s + 1 ≠ 0 := by rw [show -s + 1 = -(s - 1) by ring]; exact neg_ne_zero.2 hs1'
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-! ## Local finiteness of the zeros -/

/-- **A zero-free strip around the real half-line `[a, ∞)`**, `a > 0`. -/
theorem strip_free {a : ℝ} (ha : 0 < a) : ∃ η > 0, ∀ s : ℂ, a ≤ s.re → |s.im| < η → Zr s ≠ 0 := by
  classical
  set K : Set ℂ := closedBall 0 3 ∩ {s | a ≤ s.re} ∩ {s | |s.im| ≤ 1}
  have hK : IsCompact K := ((isCompact_closedBall 0 3).inter_right
    (isClosed_le continuous_const Complex.continuous_re)).inter_right
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hfin := hK.inter_riemannZetaZeros_finite
  obtain ⟨m, hm, hmS⟩ := exists_pos_lb hfin.toFinset (fun z => if z.im = 0 then 1 else |z.im|)
    fun z => by split_ifs with h
                · exact one_pos
                · exact abs_pos.2 h
  refine ⟨min m 1, lt_min hm one_pos, fun s hs hsi hZ => ?_⟩
  obtain ⟨h1, h0⟩ := Zr_eq_zero hZ
  have hre1 : s.re < 1 := by
    by_contra h; exact zeta_ne_zero_re_ge_one (not_lt.1 h) h0
  have hsK : s ∈ K ∩ riemannZetaZeros := by
    refine ⟨⟨⟨?_, hs⟩, ?_⟩, h0⟩
    · rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im s
      have : |s.re| ≤ 1 := abs_le.2 ⟨by linarith, hre1.le⟩
      linarith [min_le_right m 1]
    · show |s.im| ≤ 1; linarith [min_le_right m 1]
  have := hmS s (hfin.mem_toFinset.2 hsK)
  by_cases hi : s.im = 0
  · -- a real zero in `[a, 1)`
    have e : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [e] at hZ
    exact Zr_real_ne (by linarith) hZ
  · simp only [hi, ↓reduceIte] at this
    linarith [min_le_left m 1]

/-- `F` is holomorphic wherever `s ≠ θ`, `s ≠ 0` and `Z(s) ≠ 0`. -/
theorem Fψ_differentiableAt {θ c ε : ℝ} {s : ℂ} (h1 : s ≠ θ) (h0 : s ≠ 0) (hZ : Zr s ≠ 0) :
    DifferentiableAt ℂ (Fψ θ c ε) s := by
  have hd : DifferentiableAt ℂ (deriv Zr) s := (differentiable_Zr.analyticAt s).deriv.differentiableAt
  have hz : DifferentiableAt ℂ Zr s := differentiable_Zr s
  have hθ : s - θ ≠ 0 := sub_ne_zero.2 h1
  have hsz : s * Zr s ≠ 0 := mul_ne_zero h0 hZ
  unfold Fψ
  fun_prop (disch := assumption)

theorem Fψ_eventuallyEq_lap {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {z0 : ℂ} (hz : 1 < z0.re) :
    Fψ θ c ε =ᶠ[𝓝 z0] lap μ1 (Aψ θ c ε) Real.log :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    fun _ hz => (lap_eq_Fψ hθ hθ1 hz).symm

/-! ## The theorem -/

/-- **Step 1: the transform converges on `Re s > θ`.** -/
theorem conv_gt {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (h : ∀ x : ℝ, 1 < x → ε * (Chebyshev.psi x - x) ≤ c * x ^ θ) :
    ∀ σ, θ < σ → Conv μ1 (Aψ θ c ε) Real.log σ := by
  have hH := hyp_Aψ h
  refine landau_abscissa hH (conv_Aψ_three hθ hθ1) fun c' hc' habove => ?_
  set a := (θ + c') / 2
  obtain ⟨η, hη, hZ⟩ := strip_free (a := a) (by simp only [a]; linarith)
  set e := min η (c' - a)
  have he : 0 < e := lt_min hη (by simp only [a]; linarith)
  have hFd : ∀ z : ℂ, a ≤ z.re → |z.im| < η → DifferentiableAt ℂ (Fψ θ c ε) z := fun z hz hzi =>
    Fψ_differentiableAt (fun e0 => by rw [e0, ofReal_re] at hz; simp only [a] at hz; linarith)
      (fun e0 => by rw [e0, zero_re] at hz; simp only [a] at hz; linarith) (hZ z hz hzi)
  set W : Set ℂ := {s | c' < s.re} ∩ ({s | s.im < η} ∩ {s | -η < s.im})
  have hWo : IsOpen W := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hWc : Convex ℝ W := (convex_halfSpace_re_gt c').inter
    ((convex_halfSpace_im_lt η).inter (convex_halfSpace_im_gt (-η)))
  have hEq : EqOn (Fψ θ c ε) (lap μ1 (Aψ θ c ε) Real.log) W := by
    refine eqOn_convex hWo hWc (fun z hz => (hFd z (by
        have : c' < z.re := hz.1; simp only [a]; linarith)
      (abs_lt.2 ⟨by linarith [show -η < z.im from hz.2.2], by linarith [show z.im < η from hz.2.1]⟩)).differentiableWithinAt)
      ((lap_differentiableOn hH habove).mono fun z hz => hz.1) (z0 := ((max c' 3 + 1 : ℝ) : ℂ)) ?_
      (Fψ_eventuallyEq_lap hθ hθ1 ?_)
    · refine ⟨?_, ?_, ?_⟩
      · show c' < ((max c' 3 + 1 : ℝ) : ℂ).re; rw [ofReal_re]; linarith [le_max_left c' 3]
      · show ((max c' 3 + 1 : ℝ) : ℂ).im < η; rw [ofReal_im]; exact hη
      · show -η < ((max c' 3 + 1 : ℝ) : ℂ).im; rw [ofReal_im]; linarith
    · show 1 < ((max c' 3 + 1 : ℝ) : ℂ).re; rw [ofReal_re]; linarith [le_max_right c' 3]
  refine ⟨e, he, Fψ θ c ε, fun z hz => ?_, fun s hs hsc => hEq ⟨hsc, ?_, ?_⟩⟩
  · rw [mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - c')
    have h2 := Complex.abs_im_le_norm (z - c')
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
    refine (hFd z ?_ ?_).differentiableWithinAt
    · have := (abs_lt.1 (h1.trans_lt (hz.trans_le (min_le_right _ _)))).1; linarith
    · exact h2.trans_lt (hz.trans_le (min_le_left _ _))
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c')
    simp only [sub_im, ofReal_im, sub_zero] at h2
    exact (abs_lt.1 (h2.trans_lt (hs.trans_le (min_le_left _ _)))).2
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c')
    simp only [sub_im, ofReal_im, sub_zero] at h2
    exact (abs_lt.1 (h2.trans_lt (hs.trans_le (min_le_left _ _)))).1

/-- **Landau's oscillation theorem, one-sided form.** If `ε(ψ(x) − x) ≤ c·x^θ` for every `x > 1`,
with `ε ≠ 0` and `0 < θ < 1`, then `ζ` has no zero with `Re s > θ`. -/
theorem zeta_ne_zero_of_psi {θ c ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * (Chebyshev.psi x - x) ≤ c * x ^ θ) {ρ : ℂ} (hρθ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  classical
  intro hρ
  have hH := hyp_Aψ h
  set L := lap μ1 (Aψ θ c ε) Real.log
  have hLd : DifferentiableOn ℂ L {s | θ < s.re} := lap_differentiableOn hH (conv_gt hθ hθ1 h)
  have hρ1 : ρ.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hρ
  -- the zeros near `ρ`, and the rightmost one on the horizontal line through `ρ`
  set K : Set ℂ := closedBall 0 (‖ρ‖ + 3) ∩ {s | ρ.re ≤ s.re} ∩ {s | |s.im - ρ.im| ≤ 1}
  have hK : IsCompact K := ((isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)).inter_right
    (isClosed_le (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const)
  have hfin := hK.inter_riemannZetaZeros_finite
  set S := hfin.toFinset
  have hmem : ∀ z : ℂ, riemannZeta z = 0 → ρ.re ≤ z.re → |z.im - ρ.im| ≤ 1 → z ∈ S := by
    intro z hz hzre hzim
    have hz1 : z.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hz
    refine hfin.mem_toFinset.2 ⟨⟨⟨?_, hzre⟩, hzim⟩, hz⟩
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im z
    have := Complex.abs_im_le_norm ρ
    have : |z.re| ≤ 1 := abs_le.2 ⟨by linarith, hz1.le⟩
    have : |z.im| ≤ |ρ.im| + 1 := by have := abs_sub_abs_le_abs_sub z.im ρ.im; linarith
    linarith
  set cand := S.filter fun z => z.im = ρ.im
  have hρc : ρ ∈ cand := Finset.mem_filter.2 ⟨hmem ρ hρ le_rfl (by simp), rfl⟩
  obtain ⟨ps, hps, hmax⟩ := cand.exists_max_image Complex.re ⟨ρ, hρc⟩
  obtain ⟨hpsS, hpsim⟩ := Finset.mem_filter.1 hps
  have hpsK := hfin.mem_toFinset.1 hpsS
  have hps0 : riemannZeta ps = 0 := hpsK.2
  have hpsre : ρ.re ≤ ps.re := hpsK.1.1.2
  have hps1 : ps.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hps0
  have hpsθ : θ < ps.re := lt_of_lt_of_le hρθ hpsre
  have hpsne1 : ps ≠ 1 := fun e => by rw [e, one_re] at hps1; exact lt_irrefl _ hps1
  have hps00 : ps ≠ 0 := fun e => by rw [e, zero_re] at hpsθ; linarith
  -- the zero-free strip to the right of `ps`
  obtain ⟨m, hm, hmS⟩ := exists_pos_lb S (fun z => if z.im = ρ.im then 1 else |z.im - ρ.im|)
    fun z => by split_ifs with h1
                · exact one_pos
                · exact abs_pos.2 (sub_ne_zero.2 h1)
  set δ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  set U : Set ℂ := {s | ps.re < s.re} ∩ ({s | s.im < ρ.im + δ} ∩ {s | ρ.im - δ < s.im})
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  have hZU : ∀ z ∈ U, Zr z ≠ 0 := by
    intro z hz hZ
    have hU1 : ps.re < z.re := hz.1
    have hU2 : z.im < ρ.im + δ := hz.2.1
    have hU3 : ρ.im - δ < z.im := hz.2.2
    obtain ⟨-, hz0⟩ := Zr_eq_zero hZ
    have hzS := hmem z hz0 (by linarith) (by
      rw [abs_le]; constructor <;> linarith [min_le_right m 1])
    by_cases hi : z.im = ρ.im
    · have := hmax z (Finset.mem_filter.2 ⟨hzS, hi⟩); linarith
    · have := hmS z hzS
      simp only [hi, ↓reduceIte] at this
      have : |z.im - ρ.im| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith [min_le_left m 1]
  have hFU : DifferentiableOn ℂ (Fψ θ c ε) U := fun z hz => by
    have hU1 : ps.re < z.re := hz.1
    refine (Fψ_differentiableAt (fun e0 => ?_) (fun e0 => ?_) (hZU z hz)).differentiableWithinAt
    · rw [e0, ofReal_re] at hU1; linarith
    · rw [e0, zero_re] at hU1; linarith
  have hLU : DifferentiableOn ℂ L U := hLd.mono fun z hz => lt_trans hpsθ (show ps.re < z.re from hz.1)
  set z0 : ℂ := (3 : ℝ) + ρ.im * I
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = ρ.im := by simp [z0]
  have hEq : EqOn (Fψ θ c ε) L U := eqOn_convex hUo hUc hFU hLU (z0 := z0)
    ⟨show ps.re < z0.re by rw [hz0re]; linarith, show z0.im < ρ.im + δ by rw [hz0im]; linarith,
      show ρ.im - δ < z0.im by rw [hz0im]; linarith⟩
    (Fψ_eventuallyEq_lap hθ hθ1 (by rw [hz0re]; norm_num))
  have hright : ∀ x : ℝ, 0 < x → ps + x ∈ U := fun x hx =>
    ⟨show ps.re < (ps + x).re by simp; linarith, show (ps + x).im < ρ.im + δ by simp [hpsim]; linarith,
      show ρ.im - δ < (ps + x).im by simp [hpsim]; linarith⟩
  -- the order of the zero at `ps`
  have hZa : AnalyticAt ℂ Zr ps := differentiable_Zr.analyticAt ps
  have hnot : ¬ ∀ᶠ z in 𝓝 ps, Zr z = 0 := by
    intro hev
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have : dist (ps + ((r / 2 : ℝ) : ℂ)) ps < r := by
      rw [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    exact hZU _ (hright _ (by positivity)) (hball this)
  obtain ⟨n, g, hg, hg0, hZg⟩ := hZa.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  have hn : n ≠ 0 := by
    rintro rfl
    have := hZg.self_of_nhds
    simp only [pow_zero, one_smul] at this
    rw [Zr_of_ne hpsne1, hps0, mul_zero] at this
    exact hg0 this.symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- `F = G + R/(s − ps)` near `ps`
  set R : ℂ := ε * ((k + 1 : ℕ) : ℂ) / ps
  set G : ℂ → ℂ := fun z => c / (z - θ) + ε * (-((k + 1 : ℕ) : ℂ) / (ps * z) + deriv g z / (z * g z) + 1 / z)
  have hev : ∀ᶠ z in 𝓝 ps, (∀ᶠ w in 𝓝 z, Zr w = (w - ps) ^ (k + 1) • g w) ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    hZg.eventually_nhds.and (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0))
  obtain ⟨r0, hr0, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hsplit : ∀ x : ℝ, 0 < x → x < r0 →
      Fψ θ c ε (ps + x) = G (ps + x) + R / ((ps + x) - ps) := by
    intro x hx hxr
    set z := ps + (x : ℂ)
    have hzb : dist z ps < r0 := by
      rw [Complex.dist_eq, show z - ps = (x : ℂ) by simp [z], Complex.norm_real, Real.norm_of_nonneg hx.le]
      exact hxr
    obtain ⟨hZz, hgz, hgz0⟩ := hball hzb
    have hu : z - ps = (x : ℂ) := by simp [z]
    have hu0 : z - ps ≠ 0 := by rw [hu]; exact_mod_cast hx.ne'
    have hz0 : z ≠ 0 := fun e => by
      have hzre : ps.re < z.re := (hright x hx).1
      rw [e, zero_re] at hzre; linarith
    have hderiv : deriv Zr z = ((k + 1 : ℕ) : ℂ) * (z - ps) ^ k * g z + (z - ps) ^ (k + 1) * deriv g z := by
      have hZz' : Zr =ᶠ[𝓝 z] fun w => (w - ps) ^ (k + 1) * g w :=
        hZz.mono fun w hw => by rw [hw, smul_eq_mul]
      rw [hZz'.deriv_eq]
      have h1 : HasDerivAt (fun w => (w - ps) ^ (k + 1) * g w)
          (((k + 1 : ℕ) : ℂ) * (z - ps) ^ k * 1 * g z + (z - ps) ^ (k + 1) * deriv g z) z :=
        (((hasDerivAt_id z).sub_const ps).pow (k + 1)).mul hgz.differentiableAt.hasDerivAt
      rw [h1.deriv]; ring
    have hZz' : Zr z = (z - ps) ^ (k + 1) * g z := by rw [hZz.self_of_nhds, smul_eq_mul]
    unfold Fψ
    simp only [G, R]
    rw [hderiv, hZz']
    have hpk : (z - ps) ^ k ≠ 0 := pow_ne_zero _ hu0
    rw [show ps + (x : ℂ) - ps = z - ps by rfl]
    field_simp
    ring
  have hGc : ContinuousAt G ps := by
    have hθps : ps - θ ≠ 0 := fun e => by
      have := congrArg Complex.re e; simp at this; linarith
    have hdg : ContinuousAt (deriv g) ps := hg.deriv.continuousAt
    have hgc : ContinuousAt g ps := hg.continuousAt
    simp only [G]
    refine (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hθps).add
      (continuousAt_const.mul ((((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero hps00 hps00))).add (hdg.div (continuousAt_id.mul hgc) (mul_ne_zero hps00 hg0))).add
        (continuousAt_const.div continuousAt_id hps00)))
  have hR : R = 0 := residue_eq_zero hr0
    ((hLd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpsθ)).continuousAt)
    hGc fun x hx hxr => by rw [← hEq (hright x hx)]; exact hsplit x hx hxr
  simp only [R] at hR
  rw [div_eq_zero_iff] at hR
  rcases hR with hR | hR
  · rw [mul_eq_zero] at hR
    rcases hR with hR | hR
    · exact hε (by exact_mod_cast hR)
    · exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)) hR
  · exact hps00 hR

/-! ## The Ω± statements -/

/-- **Landau's oscillation theorem.** For every zero `ρ` of `ζ` and every `0 < θ < Re ρ`, whatever
`c` and `X`, `ψ(x) − x` exceeds `c·x^θ` at some `x > X`, and falls below `−c·x^θ` at some `x > X`:
`ψ(x) − x = Ω±(x^θ)`. -/
theorem psi_omega {ρ : ℂ} (hρ : riemannZeta ρ = 0) {θ : ℝ} (hθ : 0 < θ) (hθρ : θ < ρ.re) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < Chebyshev.psi x - x) ∧
      (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ θ)) := by
  have hρ1 : ρ.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hρ
  have hθ1 : θ < 1 := by linarith
  set X' := max X 1
  have hpow : ∀ x : ℝ, 1 < x → 1 ≤ x ^ θ := fun x hx => Real.one_le_rpow hx.le hθ.le
  constructor
  · by_contra hno
    push Not at hno
    refine zeta_ne_zero_of_psi hθ hθ1 one_ne_zero (c := max c 0 + Chebyshev.psi X') (fun x hx => ?_)
      hθρ hρ
    have hψ0 := Chebyshev.psi_nonneg X'
    rw [one_mul]
    rcases le_or_gt x X' with hxX | hxX
    · have h1 : Chebyshev.psi x ≤ Chebyshev.psi X' := Chebyshev.psi_mono hxX
      have h2 := hpow x hx
      have h3 : Chebyshev.psi X' ≤ Chebyshev.psi X' * x ^ θ := le_mul_of_one_le_right hψ0 h2
      have h4 : 0 ≤ max c 0 * x ^ θ := mul_nonneg (le_max_right _ _) (by positivity)
      nlinarith
    · have h1 := hno x (lt_of_le_of_lt (le_max_left _ _) hxX)
      have h2 : c * x ^ θ ≤ max c 0 * x ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h3 : 0 ≤ Chebyshev.psi X' * x ^ θ := mul_nonneg hψ0 (by positivity)
      nlinarith
  · by_contra hno
    push Not at hno
    refine zeta_ne_zero_of_psi hθ hθ1 (neg_ne_zero.2 one_ne_zero) (c := max c 0 + X') (fun x hx => ?_)
      hθρ hρ
    have hX'1 : 1 ≤ X' := le_max_right _ _
    rw [neg_one_mul, neg_sub]
    rcases le_or_gt x X' with hxX | hxX
    · have h2 := hpow x hx
      have h3 : X' ≤ X' * x ^ θ := le_mul_of_one_le_right (by linarith) h2
      have h4 : 0 ≤ max c 0 * x ^ θ := mul_nonneg (le_max_right _ _) (by positivity)
      have := Chebyshev.psi_nonneg x
      nlinarith
    · have h1 := hno x (lt_of_le_of_lt (le_max_left _ _) hxX)
      have h2 : c * x ^ θ ≤ max c 0 * x ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h3 : 0 ≤ X' * x ^ θ := mul_nonneg (by linarith) (by positivity)
      nlinarith

/-- `2 + γ − log 4π > 0` (true value 0.0462). -/
theorem hadamard_const_pos : 0 < 2 + eulerMascheroniConstant - Real.log (4 * π) := by
  have hγ := gamma_gt
  have hlog4pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have hlpi : Real.log π < 1.15 := by
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have h := Real.sum_le_exp_of_nonneg (x := 1.15) (by norm_num) 8
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    have hπ := Real.pi_lt_d6
    linarith
  rw [hlog4pi]
  norm_num at hγ hl2 ⊢
  linarith

/-- **`ζ` has a zero with `½ ≤ Re ρ < 1`.** Hadamard's identity sums `1/(ρ(1 − ρ))` over the nontrivial
zeros to `2 + γ − log 4π ≠ 0`, so there is one; `ρ ↦ 1 − ρ` preserves them. -/
theorem exists_zero_re_ge_half : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re := by
  have hne : Nonempty ZIdx := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hasSum_empty.unique hadamard_zeta
    have h0 : (2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) = 0 := by exact_mod_cast this.symm
    linarith [hadamard_const_pos]
  obtain ⟨q⟩ := hne
  have hs : IsNontrivialZero (zetaZeroFamily q) := q.1.2
  set s := zetaZeroFamily q
  rcases le_or_gt (1 / 2) s.re with h | h
  · exact ⟨s, hs.1, h⟩
  · have hs' : IsNontrivialZero (1 - s) := by
      rw [nontrivial_iff_Xi]
      have e : (1 - s - 1 / 2) / I = -((s - 1 / 2) / I) := by ring
      rw [e, Xi_even, ← nontrivial_iff_Xi]; exact hs
    exact ⟨1 - s, hs'.1, by simp; linarith⟩

/-- **`ψ(x) − x = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally.** -/
theorem psi_omega_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < Chebyshev.psi x - x) ∧
      (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ θ)) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_ge_half
  exact psi_omega hρ hθ (by linarith) c X

end PsiOmega

#print axioms PsiOmega.lap_eq_Fψ
#print axioms PsiOmega.zeta_ne_zero_of_psi
#print axioms PsiOmega.psi_omega
#print axioms PsiOmega.exists_zero_re_ge_half
#print axioms PsiOmega.psi_omega_half
