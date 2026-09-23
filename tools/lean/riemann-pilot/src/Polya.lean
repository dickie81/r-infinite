import Mathlib
import Roadmap

/-! # Item 1(b) at small support: Pólya's class is real-rooted

**The class.** For `a > 0`, `β ≥ 0` and a measure `μ` on `[0, a)` with `∫ (a − c) dμ(c) < ∞`, set
`g(t) = β + ∫ (a − max(|t|, c)) dμ(c)` on `[−a, a]` and `g = 0` outside. Each `a − max(|t|, c)` is
a trapezoid: flat top `a − c` on `|t| ≤ c`, linear down to `0` at `|t| = a`. So `g` is even,
concave on `(−a, a)`, and `g(±a) = β`. Conversely, every even function concave on `(−a, a)` has this
form: `μ` is `−g''` on `(0, a)` together with an atom `−g'(0+)` at `0`, and `β = g(a−)`. That
converse is not needed: `Concave.lean` proves the theorem directly for every even concave `g ≥ 0`
(`realRooted_of_concaveOn`), with no representation hypothesis.

**The theorem (`realRooted_polya`).** For `β > 0` or `μ([0, a)) ≠ 0`, `ĝ` has only real zeros. This
is Pólya's 1918 theorem on `∫ f(t) cos zt dt`, stated for even concave `f`. The proof here is
direct and short:
* `integral_trap`: the trapezoid's transform is `2(cos zc − cos za)/z²`, and the rectangle's is
  `2 sin(za)/z`. So `z²ĝ(z)/2 = βz sin(za) + ∫ (cos zc − cos za) dμ(c)` (`ghatC_polya`, by Fubini).
* `im_cot_neg`, `trap_ratio_im_pos`: for `Im z > 0` and `|c| < a`,
  `(cos zc − cos za)/sin za = 2/(cot A + cot B)` with `A = z(a+c)/2` and `B = z(a−c)/2`. `cot` maps
  the upper half-plane into the lower one, so this ratio has positive imaginary part.
* Dividing by `sin za` (nonzero off the real axis): `Im[βz + ∫ ratio dμ]` has the sign of `Im z`
  and cannot vanish.

No zero of `ζ` and no prime enter. This is a statement about shapes, not about the Weil form. -/

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



theorem hasDerivAt_cexp_mul (k : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (k * u)) (k * Complex.exp (k * u)) u := by
  have h := ((hasDerivAt_id (u : ℂ)).const_mul k).comp_ofReal (z := u)
  simpa [mul_comm] using h.cexp

theorem cos_eq_exp (z : ℂ) (x : ℝ) :
    Complex.cos (z * x) = (Complex.exp (I * z * x) + Complex.exp (I * z * (-x : ℝ))) / 2 := by
  have := two_cos (z * x)
  rw [eq_div_iff two_ne_zero, mul_comm, this]
  push_cast; congr 1 <;> congr 1 <;> ring

/-- **The trapezoid transform**: `∫_{−a}^{a} (a − max(|u|, c)) e^{izu} du = 2(cos zc − cos za)/z²`. -/
theorem integral_trap {z : ℂ} (hz : z ≠ 0) {a c : ℝ} (hc0 : 0 ≤ c) (hca : c ≤ a) :
    ∫ u in (-a)..a, ((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u)
      = 2 * (Complex.cos (z * c) - Complex.cos (z * a)) / z ^ 2 := by
  set k := I * z with hk
  have hk0 : k ≠ 0 := mul_ne_zero I_ne_zero hz
  have hcont : Continuous fun u : ℝ => ((a - max |u| c : ℝ) : ℂ) * Complex.exp (k * u) := by
    fun_prop
  have hii : ∀ x y : ℝ, IntervalIntegrable
      (fun u : ℝ => ((a - max |u| c : ℝ) : ℂ) * Complex.exp (k * u)) MeasureTheory.volume x y :=
    fun x y => hcont.intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-a) (-c)) (hii (-c) a),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-c) c) (hii c a)]
  -- piece `[−a, −c]`
  have h1 : ∫ u in (-a)..(-c), ((a - max |u| c : ℝ) : ℂ) * Complex.exp (k * u)
      = (((a + -c : ℝ) : ℂ) * Complex.exp (k * (-c : ℝ)) / k - Complex.exp (k * (-c : ℝ)) / k ^ 2)
        - (((a + -a : ℝ) : ℂ) * Complex.exp (k * (-a : ℝ)) / k - Complex.exp (k * (-a : ℝ)) / k ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => ((a + u : ℝ) : ℂ) * Complex.exp (k * u))]
    · apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ =>
        ((a + u : ℝ) : ℂ) * Complex.exp (k * u) / k - Complex.exp (k * u) / k ^ 2)
      · intro u _
        have hd := hasDerivAt_cexp_mul k u
        have hl : HasDerivAt (fun u : ℝ => ((a + u : ℝ) : ℂ)) 1 u := by
          simpa using ((hasDerivAt_id u).const_add a).ofReal_comp
        have := ((hl.mul hd).div_const k).sub (hd.div_const (k ^ 2))
        convert this using 1
        field_simp; ring
      · exact (by fun_prop : Continuous fun u : ℝ => ((a + u : ℝ) : ℂ) * Complex.exp (k * u)).intervalIntegrable _ _
    · intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      simp only
      rw [abs_of_nonpos (by linarith [hu.2]), max_eq_left (by linarith [hu.2])]
      congr 2; ring
  -- piece `[−c, c]`
  have h2 : ∫ u in (-c)..c, ((a - max |u| c : ℝ) : ℂ) * Complex.exp (k * u)
      = ((a - c : ℝ) : ℂ) * ((Complex.exp (k * c) - Complex.exp (k * (-c : ℝ))) / k) := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => ((a - c : ℝ) : ℂ) * Complex.exp (k * u))]
    · rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hk0]
    · intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      simp only
      rw [max_eq_right (abs_le.2 ⟨hu.1, hu.2⟩)]
  -- piece `[c, a]`
  have h3 : ∫ u in c..a, ((a - max |u| c : ℝ) : ℂ) * Complex.exp (k * u)
      = (((a - a : ℝ) : ℂ) * Complex.exp (k * a) / k + Complex.exp (k * a) / k ^ 2)
        - (((a - c : ℝ) : ℂ) * Complex.exp (k * c) / k + Complex.exp (k * c) / k ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => ((a - u : ℝ) : ℂ) * Complex.exp (k * u))]
    · apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ =>
        ((a - u : ℝ) : ℂ) * Complex.exp (k * u) / k + Complex.exp (k * u) / k ^ 2)
      · intro u _
        have hd := hasDerivAt_cexp_mul k u
        have hl : HasDerivAt (fun u : ℝ => ((a - u : ℝ) : ℂ)) (-1) u := by
          simpa using ((hasDerivAt_id u).const_sub a).ofReal_comp
        have := ((hl.mul hd).div_const k).add (hd.div_const (k ^ 2))
        convert this using 1
        field_simp; ring
      · exact (by fun_prop : Continuous fun u : ℝ => ((a - u : ℝ) : ℂ) * Complex.exp (k * u)).intervalIntegrable _ _
    · intro u hu
      rw [Set.uIcc_of_le hca] at hu
      simp only
      rw [abs_of_nonneg (by linarith [hu.1]), max_eq_left hu.1]
  rw [h1, h2, h3, cos_eq_exp, cos_eq_exp]
  have hk2 : k ^ 2 = -z ^ 2 := by rw [hk, mul_pow, I_sq]; ring
  rw [hk2]
  push_cast
  field_simp
  rw [hk]
  ring_nf


theorem integral_rect {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    ∫ u in (-a)..a, Complex.exp (I * z * u) = 2 * Complex.sin (z * a) / z := by
  have hk0 : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  rw [integral_exp_mul_complex hk0, two_sin (z * a)]
  have e1 : -(z * a) * I = I * z * ((-a : ℝ) : ℂ) := by push_cast; ring
  have e2 : z * a * I = I * z * a := by ring
  rw [e1, e2, div_eq_div_iff hk0 hz]
  have hI : I * I = -1 := I_mul_I
  linear_combination (z * (Complex.exp (I * z * a) - Complex.exp (I * z * ((-a : ℝ) : ℂ)))) * hI

/-! ## Pólya's class and its transform -/

/-- **Pólya's class**: `β` plus a `μ`-mixture of trapezoids `a − max(|t|, c)`, `c ∈ [0, a)`. -/
def polyaFn (a β : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  if |t| ≤ a then β + ∫ c in Set.Ico 0 a, (a - max |t| c) ∂μ else 0

theorem trap_norm_le {z : ℂ} {a c u : ℝ} (hu : |u| ≤ a) (hc : c ∈ Set.Ico 0 a) :
    ‖((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u)‖ ≤ Real.exp (‖z‖ * a) * (a - c) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have h1 : |a - max |u| c| ≤ a - c := by
    rw [abs_of_nonneg (by have := hc.2.le; exact sub_nonneg.2 (max_le hu this))]
    linarith [le_max_right |u| c]
  have h2 : (I * z * (u : ℂ)).re ≤ ‖z‖ * a := by
    have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [mul_re]
    rw [e]
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ ‖z‖ * a := mul_le_mul (abs_im_le_norm z) hu (abs_nonneg _) (norm_nonneg _)
  have h3 : 0 ≤ a - c := by linarith [hc.2]
  calc |a - max |u| c| * Real.exp (I * z * u).re ≤ (a - c) * Real.exp (‖z‖ * a) :=
        mul_le_mul h1 (Real.exp_le_exp.2 h2) (Real.exp_pos _).le h3
    _ = Real.exp (‖z‖ * a) * (a - c) := mul_comm _ _

theorem trap_prod_integrable {z : ℂ} {a : ℝ} (ha : 0 ≤ a) {μ : Measure ℝ} [SFinite μ]
    (hμ : IntegrableOn (fun c => a - c) (Set.Ico 0 a) μ) :
    Integrable (Function.uncurry fun (u c : ℝ) => ((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u))
      ((volume.restrict (Set.uIoc (-a) a)).prod (μ.restrict (Set.Ico 0 a))) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (-a) a)) := by
    rw [Set.uIoc_of_le (by linarith)]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hb : Integrable (fun p : ℝ × ℝ => Real.exp (‖z‖ * a) * (a - p.2))
      ((volume.restrict (Set.uIoc (-a) a)).prod (μ.restrict (Set.Ico 0 a))) :=
    (integrable_const (Real.exp (‖z‖ * a))).mul_prod hμ
  refine hb.mono' ?_ ?_
  · exact (by fun_prop : Continuous (Function.uncurry fun (u c : ℝ) =>
      ((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u))).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_Ico) ?_
    rintro ⟨u, c⟩ ⟨hu, hc⟩
    have hu' : |u| ≤ a := by
      rw [Set.uIoc_of_le (by linarith)] at hu
      exact abs_le.2 ⟨hu.1.le, hu.2⟩
    exact trap_norm_le hu' hc

/-- **The transform of Pólya's class** (`z ≠ 0`):
`ĝ(z) = 2β sin(za)/z + ∫ 2(cos zc − cos za)/z² dμ(c)`. -/
theorem ghatC_polya {z : ℂ} (hz : z ≠ 0) {a β : ℝ} (ha : 0 ≤ a) {μ : Measure ℝ} [SFinite μ]
    (hμ : IntegrableOn (fun c => a - c) (Set.Ico 0 a) μ) :
    ghatC (polyaFn a β μ) a z = β * (2 * Complex.sin (z * a) / z)
      + ∫ c in Set.Ico 0 a, 2 * (Complex.cos (z * c) - Complex.cos (z * a)) / z ^ 2 ∂μ := by
  set F : ℝ → ℝ → ℂ := fun u c => ((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u) with hF
  have hprod := trap_prod_integrable (z := z) ha hμ
  have hswap := intervalIntegral_integral_swap hprod
  -- the inner `u`-integrals, `c ∈ [0, a)`
  have hinner : ∀ c ∈ Set.Ico 0 a, ∫ u in (-a)..a, F u c
      = 2 * (Complex.cos (z * c) - Complex.cos (z * a)) / z ^ 2 :=
    fun c hc => integral_trap hz hc.1 hc.2.le
  -- `u ↦ ∫_c F u c` is interval integrable
  have hleft : IntervalIntegrable (fun u => ∫ c, F u c ∂(μ.restrict (Set.Ico 0 a)))
      volume (-a) a := by
    have := hprod.integral_prod_left
    rw [Set.uIoc_of_le (by linarith)] at this
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 this
  have hrect : IntervalIntegrable (fun u : ℝ => (β : ℂ) * Complex.exp (I * z * u)) volume (-a) a :=
    (by fun_prop : Continuous fun u : ℝ => (β : ℂ) * Complex.exp (I * z * u)).intervalIntegrable _ _
  unfold ghatC
  rw [intervalIntegral.integral_congr (g := fun u => (β : ℂ) * Complex.exp (I * z * u)
      + ∫ c, F u c ∂(μ.restrict (Set.Ico 0 a)))]
  · rw [intervalIntegral.integral_add hrect hleft, intervalIntegral.integral_const_mul,
      integral_rect hz, hswap]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ico hinner
  · intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu' : |u| ≤ a := abs_le.2 ⟨hu.1, hu.2⟩
    simp only [polyaFn, hu', ite_true, hF]
    rw [integral_mul_const, ofReal_add, ← integral_complex_ofReal]
    ring

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

/-- **Pólya's theorem for even concave probes.** Every function in Pólya's class that is not
identically zero (`β > 0` or `μ([0, a)) ≠ 0`) has a real-rooted transform. -/
theorem realRooted_polya {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) {μ : Measure ℝ} [SFinite μ]
    (hμ : IntegrableOn (fun c => a - c) (Set.Ico 0 a) μ) (hnd : 0 < β ∨ μ (Set.Ico 0 a) ≠ 0) :
    RealRooted a (polyaFn a β μ) := by
  intro z hz0
  by_contra hy
  have hz : z ≠ 0 := by rintro rfl; exact hy (by simp)
  have hs : Complex.sin (z * a) ≠ 0 := sin_ne_zero_of_im (by simp; exact ⟨hy, ha.ne'⟩)
  set R : ℝ → ℂ := fun c => (Complex.cos (z * c) - Complex.cos (z * a)) / Complex.sin (z * a)
    with hR
  set ν := μ.restrict (Set.Ico 0 a)
  -- `R` is `ν`-integrable (from Fubini's integrability)
  have hprod := trap_prod_integrable (z := z) ha.le hμ
  have hright := hprod.integral_prod_right
  have hRint : Integrable R ν := by
    have hc : Integrable (fun c => (z ^ 2 / (2 * Complex.sin (z * a))) *
        ∫ u, ((a - max |u| c : ℝ) : ℂ) * Complex.exp (I * z * u)
          ∂(volume.restrict (Set.uIoc (-a) a))) ν := hright.const_mul _
    refine hc.congr (ae_restrict_of_forall_mem measurableSet_Ico fun c hc => ?_)
    beta_reduce
    rw [Set.uIoc_of_le (by linarith), ← intervalIntegral.integral_of_le (by linarith),
      integral_trap hz hc.1 hc.2.le, hR]
    field_simp
  -- the transform, divided by `2 sin(za)/z²`
  have hform := ghatC_polya hz ha.le (β := β) hμ
  rw [hz0] at hform
  have hsplit : (∫ c in Set.Ico 0 a, 2 * (Complex.cos (z * c) - Complex.cos (z * a)) / z ^ 2 ∂μ)
      = (2 * Complex.sin (z * a) / z ^ 2) * ∫ c, R c ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hR]
    field_simp
  rw [hsplit] at hform
  have hkey : (β : ℂ) * z + ∫ c, R c ∂ν = 0 := by
    have h2 : (2 * Complex.sin (z * a) / z ^ 2) ≠ 0 := by
      apply div_ne_zero (mul_ne_zero two_ne_zero hs) (pow_ne_zero 2 hz)
    have e : (2 * Complex.sin (z * a) / z ^ 2) * ((β : ℂ) * z + ∫ c, R c ∂ν)
        = β * (2 * Complex.sin (z * a) / z) + (2 * Complex.sin (z * a) / z ^ 2) * ∫ c, R c ∂ν := by
      field_simp
    have : (2 * Complex.sin (z * a) / z ^ 2) * ((β : ℂ) * z + ∫ c, R c ∂ν) = 0 := by
      rw [e]; exact hform.symm
    exact (mul_eq_zero.1 this).resolve_left h2
  -- take `Im z · Im(·)`
  have him := congrArg (fun w => z.im * w.im) hkey
  simp only [add_im, zero_im, mul_zero] at him
  have hIm : (∫ c, R c ∂ν).im = ∫ c, (R c).im ∂ν := (integral_im hRint).symm
  rw [hIm, mul_add, ← integral_const_mul] at him
  have hβz : ((β : ℂ) * z).im = β * z.im := by simp
  rw [hβz] at him
  have hpos_pt : ∀ c ∈ Set.Ico 0 a, 0 < z.im * (R c).im := fun c hc =>
    trap_ratio_mul_pos hy hc.2 (by linarith [hc.1])
  have hI_nonneg : 0 ≤ ∫ c, z.im * (R c).im ∂ν :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ico fun c hc => (hpos_pt c hc).le)
  have hβ2 : 0 ≤ β * z.im * z.im := by
    have := mul_self_nonneg z.im; nlinarith
  rcases hnd with hb | hm
  · have : 0 < β * z.im * z.im := by
      have := mul_self_pos.2 hy; nlinarith
    nlinarith
  · have hpos : 0 < ∫ c, z.im * (R c).im ∂ν := by
      rw [integral_pos_iff_support_of_nonneg_ae
        (ae_restrict_of_forall_mem measurableSet_Ico fun c hc => (hpos_pt c hc).le)
        ((hRint.im).const_mul _)]
      rw [Measure.restrict_apply' measurableSet_Ico]
      have hsub : Set.Ico 0 a ⊆ Function.support fun c => z.im * (R c).im :=
        fun c hc => (hpos_pt c hc).ne'
      rw [Set.inter_eq_right.2 hsub]
      exact pos_iff_ne_zero.2 hm
    nlinarith

end Pilot1ca

#print axioms Pilot1ca.im_cot_neg
#print axioms Pilot1ca.trap_ratio_im_pos
#print axioms Pilot1ca.integral_trap
#print axioms Pilot1ca.ghatC_polya
#print axioms Pilot1ca.realRooted_polya
