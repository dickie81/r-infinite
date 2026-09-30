import ParityGap
import DirichletOmega
import RealDirichlet

/-! # Odd probes and real characters (round 246)

`ĝ` of an odd probe is odd and purely imaginary on `ℝ`; the sign of each zero term of `−ĝ²` on the real and imaginary axes; `IsReal χ ↔ χ.IsQuadratic`.
-/

open Real Complex MeasureTheory

noncomputable section

namespace OddProbe

open Pilot1ca

theorem ghatC_odd {g : ℝ → ℝ} (hg : ∀ u, g (-u) = -g u) (a : ℝ) (z : ℂ) :
    ghatC g a (-z) = -ghatC g a z := by
  unfold ghatC
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
    (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
  simp only [neg_neg] at h
  rw [← h, ← intervalIntegral.integral_neg]
  congr 1
  funext u
  simp only [hg, Complex.ofReal_neg]
  rw [show Complex.I * -z * (u : ℂ) = Complex.I * z * -(u : ℂ) by ring]
  ring

/-- For odd real `o` and real `r`, `ô(r)` is purely imaginary. -/
theorem ghatC_odd_re {g : ℝ → ℝ} (hg : ∀ u, g (-u) = -g u) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    (ghatC g a r).re = 0 := by
  have h1 := ghatC_neg_real (f := g) ha r
  rw [ghatC_odd hg] at h1
  have := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at this
  linarith

/-- For every real `g` and real `y`, `ĝ(iy)` is real. -/
theorem ghatC_mul_I_im (g : ℝ → ℝ) (a y : ℝ) : (ghatC g a ((y : ℂ) * I)).im = 0 := by
  have h : ∀ u : ℝ, ((g u : ℝ) : ℂ) * cexp (I * ((y : ℂ) * I) * u)
      = ((g u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
    intro u
    have e : I * ((y : ℂ) * I) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
      push_cast; linear_combination ((y : ℂ) * u) * Complex.I_sq
    rw [e, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  unfold ghatC
  simp_rw [h]
  rw [intervalIntegral.integral_ofReal]
  exact Complex.ofReal_im _

/-- Even sector, real zero: `ĝ(iy)² ≥ 0`. -/
theorem even_imag_term_nonneg (g : ℝ → ℝ) (a y : ℝ) : 0 ≤ (ghatC g a ((y : ℂ) * I) ^ 2).re := by
  have h0 := ghatC_mul_I_im g a y
  rw [pow_two, Complex.mul_re, h0]; nlinarith [sq_nonneg (ghatC g a ((y : ℂ) * I)).re]

/-- Odd sector, real zero: `−ô(iy)² ≤ 0`. -/
theorem odd_imag_term_nonpos (g : ℝ → ℝ) (a y : ℝ) : (-(ghatC g a ((y : ℂ) * I) ^ 2)).re ≤ 0 := by
  have := even_imag_term_nonneg g a y
  rw [Complex.neg_re]; linarith

/-- Odd sector, on-line zero: `−ô(r)² ≥ 0`. -/
theorem odd_real_term_nonneg {g : ℝ → ℝ} (hg : ∀ u, g (-u) = -g u) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    0 ≤ (-(ghatC g a r ^ 2)).re := by
  have h0 := ghatC_odd_re hg ha r
  rw [Complex.neg_re, pow_two, Complex.mul_re, h0]
  nlinarith [sq_nonneg (ghatC g a r).im]

/-- The odd twin `o_λ = g₀(· − λ) − g₀(· + λ)` has `ô_λ(z) = −2i·sin(λz)·ĝ₀(z)`; at `z = iy` the odd
form's term is `−4 sinh²(λy)ĝ₀(iy)²`, exponentially negative: stated here only as the sign. -/
theorem odd_imag_term_neg_of_ne {g : ℝ → ℝ} {a y : ℝ} (h : ghatC g a ((y : ℂ) * I) ≠ 0) :
    (-(ghatC g a ((y : ℂ) * I) ^ 2)).re < 0 := by
  have h0 := ghatC_mul_I_im g a y
  have hre : (ghatC g a ((y : ℂ) * I)).re ≠ 0 := by
    intro hr; exact h (Complex.ext hr h0)
  rw [Complex.neg_re, pow_two, Complex.mul_re, h0]
  have := sq_pos_of_ne_zero hre
  nlinarith

end OddProbe

namespace RealChar

open PsiOmega DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem isQuadratic_of_isReal (h : IsReal χ) : χ.IsQuadratic := by
  intro a
  have ha : ((a.val : ℕ) : ZMod N) = a := ZMod.natCast_zmod_val a
  have hr := h a.val
  rw [ha] at hr
  by_cases hu : IsUnit a
  · have hn : ‖χ a‖ = 1 := by
      have := χ.unit_norm_eq_one hu.unit
      rwa [IsUnit.unit_spec] at this
    right
    have h1 : ‖(((χ a).re : ℝ) : ℂ)‖ = 1 := by rw [hr]; exact hn
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    rcases (abs_eq zero_le_one).1 h1 with h2 | h2
    · left; rw [← hr, h2]; simp
    · right; rw [← hr, h2]; simp
  · left; exact χ.map_nonunit hu

theorem isReal_iff_isQuadratic : IsReal χ ↔ χ.IsQuadratic :=
  ⟨isQuadratic_of_isReal, isReal_of_isQuadratic⟩

end RealChar

#print axioms OddProbe.ghatC_odd
#print axioms OddProbe.ghatC_odd_re
#print axioms OddProbe.even_imag_term_nonneg
#print axioms OddProbe.odd_imag_term_nonpos
#print axioms OddProbe.odd_real_term_nonneg
#print axioms OddProbe.odd_imag_term_neg_of_ne
#print axioms RealChar.isQuadratic_of_isReal
#print axioms RealChar.isReal_iff_isQuadratic
