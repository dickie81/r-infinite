import Mathlib
import Roadmap

/-! # The trapezoid ratio (Pólya's lemma), used by `Concave.lean`

For `Im z > 0` and `|c| < a`, `(cos zc − cos za)/sin za = 2/(cot A + cot B)` with `A = z(a+c)/2`,
`B = z(a−c)/2`. `cot` maps the upper half-plane into the lower one, so the ratio has positive
imaginary part (`trap_ratio_im_pos`, `trap_ratio_mul_pos`). With the rectangle's transform
`2 sin(za)/z` (`integral_rect`), this is the core of Pólya's 1918 theorem.

Round 124: the Pólya-class statement itself (`polyaFn`, `integral_trap`, `ghatC_polya`,
`realRooted_polya`) is removed. `Concave.lean` proves real-rootedness for every even concave `g ≥ 0`
directly (`realRooted_of_concaveOn`, `realRooted_of_ae_concaveOn`), with no representation
hypothesis, so it supersedes that route. -/

open Real MeasureTheory Complex

noncomputable section

namespace Pilot1ca


theorem sin_ne_zero_of_im {w : ℂ} (hw : w.im ≠ 0) : Complex.sin w ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
  apply hw; rw [hk]; simp

/-- `Im cot w < 0` in the upper half-plane. -/
theorem im_cot_neg {w : ℂ} (hw : 0 < w.im) : (Complex.cos w / Complex.sin w).im < 0 := by
  have hs := sin_ne_zero_of_im hw.ne'
  have hn : 0 < Complex.normSq (Complex.sin w) := Complex.normSq_pos.2 hs
  have e : w = (w.re : ℂ) + (w.im : ℂ) * I := (re_add_im w).symm
  have hsr : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
    rw [e, sin_add_mul_I]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]
  have hsi : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    rw [e, sin_add_mul_I]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]
  have hcr : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
    rw [e, cos_add_mul_I]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]
  have hci : (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
    rw [e, cos_add_mul_I]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]
  rw [div_im, hsr, hsi, hcr, hci]
  have key : -(Real.sin w.re * Real.sinh w.im) * (Real.sin w.re * Real.cosh w.im)
      - Real.cos w.re * Real.cosh w.im * (Real.cos w.re * Real.sinh w.im)
      = -(Real.sinh w.im * Real.cosh w.im) := by
    have := Real.sin_sq_add_cos_sq w.re
    linear_combination (-(Real.sinh w.im * Real.cosh w.im)) * this
  have hsh : 0 < Real.sinh w.im := Real.sinh_pos_iff.2 hw
  have hch : 0 < Real.cosh w.im := Real.cosh_pos _
  rw [← sub_div, key]
  exact div_neg_of_neg_of_pos (by nlinarith) hn

/-- **The trapezoid ratio**: for `Im z > 0` and `−a < c < a`,
`Im[(cos zc − cos za)/sin za] > 0`. With `A = z(a+c)/2`, `B = z(a−c)/2` the ratio is
`2/(cot A + cot B)`, and `cot` maps the upper half-plane into the lower one. -/
theorem trap_ratio_im_pos {z : ℂ} (hz : 0 < z.im) {a c : ℝ} (hca : c < a) (hac : -a < c) :
    0 < ((Complex.cos (z * c) - Complex.cos (z * a)) / Complex.sin (z * a)).im := by
  set A := z * ((a + c) / 2 : ℝ)
  set B := z * ((a - c) / 2 : ℝ)
  have hA : 0 < A.im := by simp only [A, mul_im, ofReal_re, ofReal_im, mul_zero]; nlinarith
  have hB : 0 < B.im := by simp only [B, mul_im, ofReal_re, ofReal_im, mul_zero]; nlinarith
  have sA := sin_ne_zero_of_im hA.ne'
  have sB := sin_ne_zero_of_im hB.ne'
  have hc : z * c = A - B := by simp only [A, B]; push_cast; ring
  have ha : z * a = A + B := by simp only [A, B]; push_cast; ring
  have hw : (Complex.cos A / Complex.sin A + Complex.cos B / Complex.sin B).im < 0 := by
    rw [add_im]; linarith [im_cot_neg hA, im_cot_neg hB]
  have hw0 : Complex.cos A / Complex.sin A + Complex.cos B / Complex.sin B ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hsa : Complex.sin (A + B) ≠ 0 := by
    exact sin_ne_zero_of_im (by rw [add_im]; linarith)
  have e : (Complex.cos (z * c) - Complex.cos (z * a)) / Complex.sin (z * a)
      = 2 / (Complex.cos A / Complex.sin A + Complex.cos B / Complex.sin B) := by
    rw [hc, ha, Complex.cos_sub, Complex.cos_add, Complex.sin_add]
    rw [Complex.sin_add] at hsa
    field_simp
    ring
  rw [e, div_im]
  set w := Complex.cos A / Complex.sin A + Complex.cos B / Complex.sin B
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  simp
  exact div_neg_of_neg_of_pos (by linarith) hn

theorem integral_rect {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    ∫ u in (-a)..a, Complex.exp (I * z * u) = 2 * Complex.sin (z * a) / z := by
  have hk0 : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  rw [integral_exp_mul_complex hk0, two_sin (z * a)]
  have e1 : -(z * a) * I = I * z * ((-a : ℝ) : ℂ) := by push_cast; ring
  have e2 : z * a * I = I * z * a := by ring
  rw [e1, e2, div_eq_div_iff hk0 hz]
  have hI : I * I = -1 := I_mul_I
  linear_combination (z * (Complex.exp (I * z * a) - Complex.exp (I * z * ((-a : ℝ) : ℂ)))) * hI

/-! ## The real-rootedness -/

theorem trap_ratio_mul_pos {z : ℂ} (hz : z.im ≠ 0) {a c : ℝ} (hca : c < a) (hac : -a < c) :
    0 < z.im * ((Complex.cos (z * c) - Complex.cos (z * a)) / Complex.sin (z * a)).im := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hn : 0 < (-z).im := by simp; linarith
    have := trap_ratio_im_pos hn hca hac
    have e : (Complex.cos (-z * c) - Complex.cos (-z * a)) / Complex.sin (-z * a)
        = -((Complex.cos (z * c) - Complex.cos (z * a)) / Complex.sin (z * a)) := by
      rw [neg_mul, neg_mul, Complex.cos_neg, Complex.cos_neg, Complex.sin_neg, div_neg]
    rw [e, neg_im] at this
    nlinarith
  · exact mul_pos h (trap_ratio_im_pos h hca hac)

end Pilot1ca

#print axioms Pilot1ca.im_cot_neg
#print axioms Pilot1ca.trap_ratio_im_pos
#print axioms Pilot1ca.trap_ratio_mul_pos
