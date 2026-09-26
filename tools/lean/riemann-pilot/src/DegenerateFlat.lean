import Mathlib
import Commute

/-! # Degenerate ⇒ edge-flat (round 48, the converse direction, formal)

If the ground state at support `2a` is not simple, the ground space contains a pole-free element `w`
(`ŵ(±i/2) = 0`) together with its compactly supported Green solution `h = G w`, where

  `G w (x) = ∫_{−a}^{x} 2 sinh((x − y)/2) w(y) dy`,  i.e. `h'' − h/4 = w`, `ĥ(z) = −ŵ(z)/(z² + ¼)`.

So `h` is `H²`-flat at `±a` and both `h` and `h'' = w + h/4` lie in the ground space: this is the
structure of round 48's Theorem D, obtained here without complex swaps or finite-dimensionality.

Proof outline.
1. `G` is `hSw` at `w = i/2` (SwapRealize.lean), so `G w` is even, continuous, supported in `[−a, a]`
   when `ŵ(i/2) = poleR w = 0`, with the transform above.
2. `G w` is Lipschitz, hence its autocorrelation defect is `O(u)`, hence it is a probe.
3. `xcorr(G v, m) = xcorr(v, G m)` for pole-free `m` (a triangle Fubini swap), so for `v` in the
   ground space and pole-free `v`, `Q − λ₁` pairs `G v` with every pole-free probe to zero.
4. A rank-one argument (`Q_λ ≥ 0`) puts `G v`, or a pole-free combination, in the ground space.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The Green operator of the pole -/

/-- `G f (x) = ∫_{−a}^{x} 2 sinh((x − y)/2) f(y) dy`. -/
def Gpole (f : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-a)..x, 2 * Real.sinh ((x - y) / 2) * f y

theorem ii_mul_rexp {f : ℝ → ℝ} (hf : MemLp f 2 volume) (c : ℝ) (α β : ℝ) :
    IntervalIntegrable (fun y => f y * Real.exp (c * y)) volume α β :=
  (memLp_intervalIntegrable hf α β).mul_continuousOn (by fun_prop)

/-- The exponential form: `G f (x) = e^{x/2}∫f e^{−y/2} − e^{−x/2}∫f e^{y/2}`. -/
theorem Gpole_eq_exp {f : ℝ → ℝ} (hf : MemLp f 2 volume) (a x : ℝ) :
    Gpole f a x = Real.exp (x / 2) * (∫ y in (-a)..x, f y * Real.exp ((-1 / 2) * y))
      - Real.exp (-(x / 2)) * (∫ y in (-a)..x, f y * Real.exp ((1 / 2) * y)) := by
  unfold Gpole
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((ii_mul_rexp hf _ _ _).const_mul _)
      ((ii_mul_rexp hf _ _ _).const_mul _)]
  congr 1; funext y
  have e1 : Real.exp (x / 2) * Real.exp ((-1 / 2) * y) = Real.exp ((x - y) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(x / 2)) * Real.exp ((1 / 2) * y) = Real.exp (-((x - y) / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.sinh_eq, ← e1, ← e2]; ring

/-- `G` is `hSw` at `w = i/2`. -/
theorem hSw_half_eq {f : ℝ → ℝ} (hf : MemLp f 2 volume) (a x : ℝ) :
    hSw f a (Complex.I / 2) x = ((Gpole f a x : ℝ) : ℂ) := by
  have hP : ∀ (c : ℝ) (z : ℂ), Complex.I * z = (c : ℂ) →
      Pc f a z x = ((∫ y in (-a)..x, f y * Real.exp (c * y) : ℝ) : ℂ) := by
    intro c z hz
    unfold Pc
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext y
    rw [hz]; push_cast; rfl
  have h1 : Complex.I * (Complex.I / 2) = ((-1 / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
  have h2 : Complex.I * (-(Complex.I / 2)) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (-(1 / 2) : ℂ) * Complex.I_mul_I
  unfold hSw
  rw [hP (1 / 2) _ h2, hP (-1 / 2) _ h1, Gpole_eq_exp hf]
  have ex1 : Complex.exp (Complex.I * (Complex.I / 2) * x) = ((Real.exp (-(x / 2)) : ℝ) : ℂ) := by
    rw [h1, Complex.ofReal_exp]; push_cast; ring_nf
  have ex2 : Complex.exp (-(Complex.I * (Complex.I / 2) * x)) = ((Real.exp (x / 2) : ℝ) : ℂ) := by
    rw [h1, Complex.ofReal_exp]; push_cast; ring_nf
  have hd : (2 * Complex.I * (Complex.I / 2)) = -1 := by
    linear_combination Complex.I_mul_I
  rw [ex1, ex2, hd]
  push_cast; ring

section Gprops

variable {f : ℝ → ℝ} {a : ℝ}

theorem Gpole_continuous (hf : MemLp f 2 volume) : Continuous (Gpole f a) := by
  have h := hSw_continuous hf a (Complex.I / 2)
  have : Gpole f a = fun x => (hSw f a (Complex.I / 2) x).re := by
    funext x; rw [hSw_half_eq hf, Complex.ofReal_re]
  rw [this]; exact Complex.continuous_re.comp h

theorem Gpole_supp (hp : Probe a f) (hpole : poleR f a = 0) (x : ℝ) (hx : a < |x|) :
    Gpole f a x = 0 := by
  have hw : ghatC f a (Complex.I / 2) = 0 := by rw [ghatC_I_div_two, hpole, Complex.ofReal_zero]
  have := hSw_supp hp.memL2 hp.even hp.supp hw x hx
  rw [hSw_half_eq hp.memL2] at this
  exact_mod_cast this

theorem Gpole_even (hp : Probe a f) (hpole : poleR f a = 0) (x : ℝ) :
    Gpole f a (-x) = Gpole f a x := by
  have hw : ghatC f a (Complex.I / 2) = 0 := by rw [ghatC_I_div_two, hpole, Complex.ofReal_zero]
  have := hSw_even hp.memL2 hp.even hw x
  rw [hSw_half_eq hp.memL2, hSw_half_eq hp.memL2] at this
  exact_mod_cast this

/-- The transform: `Ĝf(z) = −f̂(z)/(z² + ¼)`. -/
theorem Gpole_hat (hp : Probe a f) (ha : 0 ≤ a) (hpole : poleR f a = 0) {z : ℂ}
    (hz : z ^ 2 ≠ (Complex.I / 2) ^ 2) :
    (∫ x in (-a)..a, ((Gpole f a x : ℝ) : ℂ) * Complex.exp (Complex.I * z * x))
      = -(ghatC f a z / (z ^ 2 - (Complex.I / 2) ^ 2)) := by
  have hw : ghatC f a (Complex.I / 2) = 0 := by rw [ghatC_I_div_two, hpole, Complex.ofReal_zero]
  have hw0 : Complex.I / 2 ≠ 0 := by simp
  rw [← hSw_hat hp.memL2 hp.even ha hw hw0 hz]
  congr 1; funext x; rw [hSw_half_eq hp.memL2]

end Gprops

/-! ## `G f` is Lipschitz, hence a probe -/

theorem sinhk_lip {R p q : ℝ} (hp : p ∈ Icc 0 (2 * R)) (hq : q ∈ Icc 0 (2 * R)) :
    |2 * Real.sinh (p / 2) - 2 * Real.sinh (q / 2)| ≤ Real.cosh R * |p - q| := by
  have hd : ∀ u ∈ Icc 0 (2 * R), HasDerivWithinAt (fun u => 2 * Real.sinh (u / 2))
      (Real.cosh (u / 2)) (Icc 0 (2 * R)) u := by
    intro u _
    have := (((hasDerivAt_id u).div_const 2).sinh).const_mul 2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id]; ring
  have hb : ∀ u ∈ Icc 0 (2 * R), ‖Real.cosh (u / 2)‖ ≤ Real.cosh R := by
    intro u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh]
    rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonneg (by linarith [hu.1, hu.2])]
    linarith [hu.2]
  have := (convex_Icc 0 (2 * R)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hq hp
  simpa [Real.norm_eq_abs] using this

section Lip

variable {f : ℝ → ℝ} {a : ℝ}

theorem ii_kernel (hf : MemLp f 2 volume) (x α β : ℝ) :
    IntervalIntegrable (fun y => 2 * Real.sinh ((x - y) / 2) * f y) volume α β :=
  (memLp_intervalIntegrable hf α β).continuousOn_mul (by fun_prop)

theorem ae_ne_pt (c : ℝ) : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ c := by
  rw [ae_iff]; simp

/-- The lower limit can be moved from `−a` to any `−R ≤ −a`. -/
theorem Gpole_from (hf : MemLp f 2 volume) (hsupp : ∀ u, a < |u| → f u = 0) {R : ℝ} (hR : a ≤ R)
    (x : ℝ) : Gpole f a x = ∫ y in (-R)..x, 2 * Real.sinh ((x - y) / 2) * f y := by
  unfold Gpole
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_kernel hf x (-R) (-a))
    (ii_kernel hf x (-a) x)]
  have : (∫ y in (-R)..(-a), 2 * Real.sinh ((x - y) / 2) * f y) = 0 := by
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [ae_ne_pt (-a)] with y hy hyI
    rw [uIoc_of_le (by linarith)] at hyI
    have : a < |y| := by
      have := lt_of_le_of_ne hyI.2 hy; linarith [neg_le_abs y]
    rw [hsupp y this, mul_zero]
  rw [this, zero_add]

/-- **Lipschitz on `[−R, R]`**, with constant `cosh R · ∫_{−R}^{R}|f|`. -/
theorem Gpole_lip (hf : MemLp f 2 volume) (hsupp : ∀ u, a < |u| → f u = 0) {R : ℝ} (hR : a ≤ R)
    {x x' : ℝ} (hx : x ∈ Icc (-R) R) (hx' : x' ∈ Icc (-R) R) :
    |Gpole f a x' - Gpole f a x|
      ≤ Real.cosh R * (∫ y in (-R)..R, |f y|) * |x' - x| := by
  have hN : IntervalIntegrable (fun y => |f y|) volume (-R) R :=
    (memLp_intervalIntegrable hf _ _).abs
  have key : ∀ x x' : ℝ, x ∈ Icc (-R) R → x' ∈ Icc (-R) R → x ≤ x' →
      |Gpole f a x' - Gpole f a x| ≤ Real.cosh R * (∫ y in (-R)..R, |f y|) * |x' - x| := by
    intro x x' hx hx' hle
    set C := Real.cosh R
    rw [Gpole_from hf hsupp hR x', Gpole_from hf hsupp hR x,
      ← intervalIntegral.integral_add_adjacent_intervals (ii_kernel hf x' (-R) x)
        (ii_kernel hf x' x x')]
    have hsplit : (∫ y in (-R)..x, 2 * Real.sinh ((x' - y) / 2) * f y)
        + (∫ y in x..x', 2 * Real.sinh ((x' - y) / 2) * f y)
        - (∫ y in (-R)..x, 2 * Real.sinh ((x - y) / 2) * f y)
        = (∫ y in (-R)..x, (2 * Real.sinh ((x' - y) / 2) - 2 * Real.sinh ((x - y) / 2)) * f y)
          + ∫ y in x..x', 2 * Real.sinh ((x' - y) / 2) * f y := by
      rw [add_sub_right_comm, ← intervalIntegral.integral_sub (ii_kernel hf x' _ _)
        (ii_kernel hf x _ _)]
      congr 1; congr 1; funext y; ring
    rw [hsplit]
    have hI1 : |∫ y in (-R)..x, (2 * Real.sinh ((x' - y) / 2) - 2 * Real.sinh ((x - y) / 2)) * f y|
        ≤ ∫ y in (-R)..x, C * |x' - x| * |f y| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le hx.1 (Eventually.of_forall fun y hy => ?_)
        ((memLp_intervalIntegrable hf _ _).abs.const_mul _)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := sinhk_lip (R := R) (p := x' - y) (q := x - y)
        ⟨by linarith [hy.2], by linarith [hy.1, hx'.2]⟩ ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
      rw [show x' - y - (x - y) = x' - x by ring] at this
      exact this
    have hI2 : |∫ y in x..x', 2 * Real.sinh ((x' - y) / 2) * f y|
        ≤ ∫ y in x..x', C * |x' - x| * |f y| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le hle (Eventually.of_forall fun y hy => ?_)
        ((memLp_intervalIntegrable hf _ _).abs.const_mul _)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := sinhk_lip (R := R) (p := x' - y) (q := 0)
        ⟨by linarith [hy.2], by linarith [hy.1, hx'.2, hx.1]⟩ ⟨le_rfl, by linarith [hx.1, hx.2]⟩
      simp only [zero_div, Real.sinh_zero, mul_zero, sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (Real.cosh_pos _).le)
      rw [abs_of_nonneg (by linarith [hy.2]), abs_of_nonneg (by linarith)]
      linarith [hy.1]
    have hmono : (∫ y in (-R)..x', |f y|) ≤ ∫ y in (-R)..R, |f y| :=
      intervalIntegral.integral_mono_interval le_rfl (hx.1.trans hle) hx'.2
        (Eventually.of_forall fun _ => abs_nonneg _) hN
    have hsum : (∫ y in (-R)..x, C * |x' - x| * |f y|) + (∫ y in x..x', C * |x' - x| * |f y|)
        = C * |x' - x| * ∫ y in (-R)..x', |f y| := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        ((memLp_intervalIntegrable hf _ _).abs.const_mul _)
        ((memLp_intervalIntegrable hf _ _).abs.const_mul _), intervalIntegral.integral_const_mul]
    have hC : 0 ≤ C * |x' - x| := mul_nonneg (Real.cosh_pos _).le (abs_nonneg _)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hI1 hI2
      _ = _ := hsum
      _ ≤ C * |x' - x| * ∫ y in (-R)..R, |f y| := mul_le_mul_of_nonneg_left hmono hC
      _ = _ := by ring
  rcases le_total x x' with h | h
  · exact key x x' hx hx' h
  · have := key x' x hx' hx h
    rwa [abs_sub_comm, abs_sub_comm x x'] at this

end Lip

section ProbeG

variable {f : ℝ → ℝ} {a : ℝ}

/-- `(G t − G(t+u))² ≤ L²u²` for `|u| ≤ 1`, with `L = cosh(a+1)·∫_{−a−1}^{a+1}|f|`. -/
theorem Gpole_sq_diff (hp : Probe a f) (hpole : poleR f a = 0) {t u : ℝ}
    (hu : |u| ≤ 1) :
    (Gpole f a t - Gpole f a (t + u)) ^ 2
      ≤ (Real.cosh (a + 1) * (∫ y in (-(a + 1))..(a + 1), |f y|)) ^ 2 * u ^ 2 := by
  set L := Real.cosh (a + 1) * (∫ y in (-(a + 1))..(a + 1), |f y|)
  have hsp := Gpole_supp hp hpole
  by_cases ht : t ∈ Icc (-(a + 1)) (a + 1)
  · by_cases htu : t + u ∈ Icc (-(a + 1)) (a + 1)
    · have h := Gpole_lip hp.memL2 hp.supp (R := a + 1) (by linarith) ht htu
      rw [show t + u - t = u by ring] at h
      calc (Gpole f a t - Gpole f a (t + u)) ^ 2 = |Gpole f a (t + u) - Gpole f a t| ^ 2 := by
            rw [sq_abs]; ring
        _ ≤ (L * |u|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = L ^ 2 * u ^ 2 := by rw [mul_pow, sq_abs]
    · have h1 : a + 1 < |t + u| := by
        by_contra hc; push Not at hc; exact htu (abs_le.1 hc)
      have h2 : a < |t| := by
        have := abs_add_le t u; linarith
      rw [hsp t h2, hsp (t + u) (by linarith)]; simp; positivity
  · have h1 : a + 1 < |t| := by
      by_contra hc; push Not at hc; exact ht (abs_le.1 hc)
    have h2 : a < |t + u| := by
      have := abs_add_le (t + u) (-u)
      rw [add_neg_cancel_right, abs_neg] at this; linarith
    rw [hsp t (by linarith), hsp (t + u) h2]; simp; positivity

theorem Gpole_memLp (hp : Probe a f) (hpole : poleR f a = 0) : MemLp (Gpole f a) 2 volume :=
  Continuous.memLp_of_hasCompactSupport (Gpole_continuous hp.memL2)
    (hasCompactSupport_of_supp (a := a) (Gpole_supp hp hpole))

/-- **The autocorrelation defect of `G f` is `O(u)`.** -/
theorem Gpole_autocorr_le (hp : Probe a f) (ha : 0 ≤ a) (hpole : poleR f a = 0) :
    ∃ K, 0 ≤ K ∧ ∀ u, 0 < u → autocorr (Gpole f a) 0 - autocorr (Gpole f a) u ≤ K * u := by
  set G := Gpole f a
  set L := Real.cosh (a + 1) * (∫ y in (-(a + 1))..(a + 1), |f y|)
  have hG := Gpole_memLp hp hpole
  have hsp : ∀ x, a < |x| → G x = 0 := Gpole_supp hp hpole
  refine ⟨(a + 2) * L ^ 2 + 2 * normSq G,
    add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith [normSq_nonneg G]),
    fun u hu => ?_⟩
  have hN0 : 0 ≤ normSq G := normSq_nonneg G
  rcases le_or_gt u 1 with hu1 | hu1
  · -- small shifts: Lipschitz
    set S := Icc (-(a + 2)) (a + 2)
    have hpt : ∀ t, (G t - G (t + u)) ^ 2 ≤ S.indicator (fun _ => L ^ 2 * u ^ 2) t := by
      intro t
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
        exact Gpole_sq_diff hp hpole (by rw [abs_of_pos hu]; exact hu1)
      · rw [Set.indicator_of_notMem ht]
        have h1 : a + 2 < |t| := by
          by_contra hc; push Not at hc; exact ht (abs_le.1 hc)
        have h2 : a < |t + u| := by
          have := abs_add_le (t + u) (-u)
          rw [add_neg_cancel_right, abs_neg, abs_of_pos hu] at this; linarith
        rw [hsp t (by linarith), hsp _ h2]; simp
    have hint : Integrable (fun t => (G t - G (t + u)) ^ 2) :=
      (hG.sub (hG.comp_measurePreserving (measurePreserving_add_right volume u))).integrable_sq
    have hbd : Integrable (S.indicator fun _ : ℝ => L ^ 2 * u ^ 2) :=
      (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    have hle := integral_mono hint hbd hpt
    rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hle
    have hns := normSq_sub_shift hG u
    unfold normSq at hns
    have e : (∫ x, (G x - G (x + u)) ^ 2) = 2 * (autocorr G 0 - autocorr G u) := hns
    have : autocorr G 0 - autocorr G u ≤ (a + 2) * L ^ 2 * u ^ 2 := by nlinarith
    have hu2 : u ^ 2 ≤ u := by nlinarith
    have hc : 0 ≤ (a + 2) * L ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hu2 hc, mul_nonneg hN0 hu.le]
  · -- large shifts: trivial bound
    have h1 : |autocorr G u| ≤ normSq G := abs_autocorr_le hG u
    have h0 : autocorr G 0 = normSq G := autocorr_zero G
    have : autocorr G 0 - autocorr G u ≤ 2 * normSq G := by
      rw [h0]; linarith [neg_abs_le (autocorr G u)]
    have hc : 0 ≤ (a + 2) * L ^ 2 * u := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ a + 2) (sq_nonneg L); nlinarith
    nlinarith

/-- **`G f` is a probe** for every pole-free probe `f`. -/
theorem Gpole_probe (hp : Probe a f) (ha : 0 ≤ a) (hpole : poleR f a = 0) :
    Probe a (Gpole f a) := by
  obtain ⟨K, hK, hle⟩ := Gpole_autocorr_le hp ha hpole
  have hG := Gpole_memLp hp hpole
  refine ⟨Gpole_even hp hpole, Gpole_supp hp hpole, hG, ?_⟩
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (K * 16)) (measurable_archIntegrand hG).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have hu0 : 0 < u := hu
  have hk : 0 < Real.exp (u / 2) / Real.sinh u :=
    div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hG hu0)]
  unfold archIntegrand
  calc (autocorr (Gpole f a) 0 - autocorr (Gpole f a) u) * (Real.exp (u / 2) / Real.sinh u)
      ≤ (K * u) * (Real.exp (u / 2) / Real.sinh u) := mul_le_mul_of_nonneg_right (hle u hu0) hk.le
    _ = K * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ K * (16 * Real.exp (-(1 / 4) * u)) := mul_le_mul_of_nonneg_left (u_archK_le hu0) hK
    _ = K * 16 * Real.exp (-(1 / 4) * u) := by ring

end ProbeG

/-! ## The symmetry `xcorr(G v, m) = xcorr(v, G m)` for pole-free `m` -/

/-- Moving the lower limit of a primitive from `−a` to `−R` for a function vanishing on `|y| > a`. -/
theorem integral_from_eq {a R : ℝ} (hR : a ≤ R) {φ : ℝ → ℝ} (hφ : ∀ y, a < |y| → φ y = 0)
    (hi : ∀ α β, IntervalIntegrable φ volume α β) (x : ℝ) :
    (∫ y in (-a)..x, φ y) = ∫ y in (-R)..x, φ y := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-R) (-a)) (hi (-a) x)]
  have : (∫ y in (-R)..(-a), φ y) = 0 := by
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [ae_ne_pt (-a)] with y hy hyI
    rw [uIoc_of_le (by linarith)] at hyI
    have := lt_of_le_of_ne hyI.2 hy
    exact hφ y (by linarith [neg_le_abs y])
  rw [this, zero_add]

theorem interval_eq_line {a α β : ℝ} (hα : α < -a) (hβ : a < β) {φ : ℝ → ℝ}
    (hφ : ∀ y, a < |y| → φ y = 0) : (∫ y in α..β, φ y) = ∫ y, φ y := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro y hy
  rw [Function.mem_support] at hy
  have : |y| ≤ a := by
    by_contra h'; exact hy (hφ y (lt_of_not_ge h'))
  exact ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

/-- A pole-free even probe annihilates `e^{±s/2}`. -/
theorem pole_free_line {a : ℝ} (ha : 0 ≤ a) {m : ℝ → ℝ} (hm : Probe a m) (hpole : poleR m a = 0) :
    (∫ s, m s * Real.exp ((-1 / 2) * s)) = 0 ∧ (∫ s, m s * Real.exp ((1 / 2) * s)) = 0 := by
  have h1 : (∫ s, m s * Real.exp ((-1 / 2) * s)) = 0 := by
    rw [← hpole, poleR_eq_integral ha hm.supp]
    congr 1; funext s; congr 2; ring
  refine ⟨h1, ?_⟩
  rw [← h1, ← integral_neg_eq_self]
  congr 1; funext s; rw [hm.even]; congr 2; ring

/-- `∫_α^β 2 sinh((s − c)/2) m(s) ds = 0` for a pole-free even probe, `[−a, a] ⊂ (α, β)`. -/
theorem kernel_zero {a : ℝ} (ha : 0 ≤ a) {m : ℝ → ℝ} (hm : Probe a m) (hpole : poleR m a = 0)
    {α β : ℝ} (hα : α < -a) (hβ : a < β) (c : ℝ) :
    (∫ s in α..β, 2 * Real.sinh ((s - c) / 2) * m s) = 0 := by
  have hpt : (fun s => 2 * Real.sinh ((s - c) / 2) * m s) = fun s =>
      Real.exp (-(c / 2)) * (m s * Real.exp ((1 / 2) * s))
        - Real.exp (c / 2) * (m s * Real.exp ((-1 / 2) * s)) := by
    funext s
    rw [Real.sinh_eq]
    have e1 : Real.exp (-(c / 2)) * Real.exp ((1 / 2) * s) = Real.exp ((s - c) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (c / 2) * Real.exp ((-1 / 2) * s) = Real.exp (-((s - c) / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← e1, ← e2]; ring
  obtain ⟨z1, z2⟩ := pole_free_line ha hm hpole
  have s1 : (∫ s in α..β, m s * Real.exp ((1 / 2) * s)) = 0 := by
    rw [interval_eq_line hα hβ (fun y hy => by rw [hm.supp y hy, zero_mul]), z2]
  have s2 : (∫ s in α..β, m s * Real.exp ((-1 / 2) * s)) = 0 := by
    rw [interval_eq_line hα hβ (fun y hy => by rw [hm.supp y hy, zero_mul]), z1]
  rw [hpt, intervalIntegral.integral_sub ((ii_mul_rexp hm.memL2 _ _ _).const_mul _)
    ((ii_mul_rexp hm.memL2 _ _ _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, s1, s2]
  ring


/-- The inner Green integral: `∫_y^R 2 sinh((t − y)/2) m(t + u) dt = G m (y + u)` for pole-free `m`,
once `R + u > a`. -/
theorem inner_green {a : ℝ} (ha : 0 ≤ a) {m : ℝ → ℝ} (hm : Probe a m) (hpole : poleR m a = 0)
    {R u : ℝ} (hRu : a < R + u) (y : ℝ) :
    (∫ t in y..R, 2 * Real.sinh ((t - y) / 2) * m (t + u)) = Gpole m a (y + u) := by
  set c := y + u
  have hshift : (∫ t in y..R, 2 * Real.sinh ((t - y) / 2) * m (t + u))
      = ∫ s in c..(R + u), 2 * Real.sinh ((s - c) / 2) * m s := by
    have := intervalIntegral.integral_comp_add_right
      (fun s => 2 * Real.sinh ((s - c) / 2) * m s) u (a := y) (b := R)
    rw [← this]
    congr 1; funext t; congr 3; simp only [c]; ring
  have hii : ∀ α β, IntervalIntegrable (fun s => 2 * Real.sinh ((s - c) / 2) * m s) volume α β :=
    fun α β => (memLp_intervalIntegrable hm.memL2 α β).continuousOn_mul (by fun_prop)
  rw [hshift, ← intervalIntegral.integral_interval_sub_left (hii (-(a + 1)) (R + u))
    (hii (-(a + 1)) c), kernel_zero ha hm hpole (by linarith) hRu c, zero_sub,
    ← integral_from_eq (a := a) (R := a + 1) (by linarith)
      (fun y hy => by rw [hm.supp y hy, mul_zero]) hii c]
  unfold Gpole
  rw [← intervalIntegral.integral_neg]
  congr 1; funext s
  rw [show (s - c) / 2 = -((c - s) / 2) by ring, Real.sinh_neg]; ring

/-- **`∫ G v(t) m(t + u) dt = ∫ v(y) G m(y + u) dy`** for pole-free `m`. -/
theorem shift_swap {a : ℝ} (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : Probe a v) (hm : Probe a m)
    (hmpole : poleR m a = 0) (u : ℝ) :
    (∫ t, Gpole v a t * m (t + u)) = ∫ y, v y * Gpole m a (y + u) := by
  set R := a + |u| + 1
  have hRa : a ≤ R := by simp only [R]; linarith [abs_nonneg u]
  -- restrict both sides to `[−R, R]`
  have hL : (∫ t, Gpole v a t * m (t + u)) = ∫ t in (-R)..R, Gpole v a t * m (t + u) := by
    refine (interval_eq_line (a := a + |u|) (by simp only [R]; linarith) (by simp only [R]; linarith)
      fun t ht => ?_).symm
    have : a < |t + u| := by
      have := abs_add_le (t + u) (-u); rw [add_neg_cancel_right, abs_neg] at this; linarith
    rw [hm.supp _ this, mul_zero]
  have hRside : (∫ y, v y * Gpole m a (y + u)) = ∫ y in (-R)..R, v y * Gpole m a (y + u) :=
    (interval_eq_line (a := a) (by simp only [R]; linarith [abs_nonneg u])
      (by simp only [R]; linarith [abs_nonneg u]) fun y hy => by rw [hv.supp y hy, zero_mul]).symm
  rw [hL, hRside]
  -- the exponential form of `G v` with lower limit `−R`
  set A : ℝ → ℝ := fun x => ∫ y in (-R)..x, v y * Real.exp ((-1 / 2) * y)
  set B : ℝ → ℝ := fun x => ∫ y in (-R)..x, v y * Real.exp ((1 / 2) * y)
  have hvi : ∀ (σ : ℝ) α β, IntervalIntegrable (fun y => v y * Real.exp (σ * y)) volume α β :=
    fun σ α β => ii_mul_rexp hv.memL2 σ α β
  have hvz : ∀ σ : ℝ, ∀ y, a < |y| → v y * Real.exp (σ * y) = 0 :=
    fun σ y hy => by rw [hv.supp y hy, zero_mul]
  have hG : ∀ t, Gpole v a t = Real.exp (t / 2) * A t - Real.exp (-(t / 2)) * B t := by
    intro t
    rw [Gpole_eq_exp hv.memL2, integral_from_eq hRa (hvz _) (hvi _) t,
      integral_from_eq hRa (hvz _) (hvi _) t]
  have hmu : MemLp (fun t => m (t + u)) 2 volume :=
    hm.memL2.comp_measurePreserving (measurePreserving_add_right volume u)
  set e₁ : ℝ → ℝ := fun t => m (t + u) * Real.exp ((1 / 2) * t)
  set e₂ : ℝ → ℝ := fun t => m (t + u) * Real.exp ((-1 / 2) * t)
  have he₁ : IntervalIntegrable e₁ volume (-R) R := ii_mul_rexp hmu _ _ _
  have he₂ : IntervalIntegrable e₂ volume (-R) R := ii_mul_rexp hmu _ _ _
  have hAc : Continuous A := intervalIntegral.continuous_primitive (hvi _) (-R)
  have hBc : Continuous B := intervalIntegral.continuous_primitive (hvi _) (-R)
  have hsplit : (fun t => Gpole v a t * m (t + u)) = fun t => e₁ t * A t - e₂ t * B t := by
    funext t
    have x1 : Real.exp ((1 / 2) * t) = Real.exp (t / 2) := by ring_nf
    have x2 : Real.exp ((-1 / 2) * t) = Real.exp (-(t / 2)) := by ring_nf
    simp only [e₁, e₂, hG t, x1, x2]
    ring
  have hR0 : -R ≤ R := by linarith
  have hE : ∀ e : ℝ → ℝ, (∀ α β, IntervalIntegrable e volume α β) →
      Continuous fun y => ∫ x in y..R, e x := fun e he => by
    have := (intervalIntegral.continuous_primitive he R).neg
    convert this using 1; funext y; rw [intervalIntegral.integral_symm]; rfl
  have hRu : a < R + u := by simp only [R]; linarith [neg_abs_le u]
  rw [hsplit, intervalIntegral.integral_sub (he₁.mul_continuousOn hAc.continuousOn)
      (he₂.mul_continuousOn hBc.continuousOn),
    triangle_swap hR0 he₁.1 (hvi _ _ _).1, triangle_swap hR0 he₂.1 (hvi _ _ _).1,
    ← intervalIntegral.integral_sub ((hvi _ _ _).mul_continuousOn
      (hE e₁ fun α β => ii_mul_rexp hmu _ α β).continuousOn)
      ((hvi _ _ _).mul_continuousOn (hE e₂ fun α β => ii_mul_rexp hmu _ α β).continuousOn)]
  apply intervalIntegral.integral_congr
  intro y _
  simp only
  rw [← inner_green ha hm hmpole hRu y]
  have hlin : Real.exp ((-1 / 2) * y) * (∫ x in y..R, e₁ x)
      - Real.exp ((1 / 2) * y) * (∫ x in y..R, e₂ x)
      = ∫ t in y..R, 2 * Real.sinh ((t - y) / 2) * m (t + u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((ii_mul_rexp hmu _ _ _).const_mul _)
        ((ii_mul_rexp hmu _ _ _).const_mul _)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    have e1 : Real.exp ((-1 / 2) * y) * Real.exp ((1 / 2) * t) = Real.exp ((t - y) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp ((1 / 2) * y) * Real.exp ((-1 / 2) * t) = Real.exp (-((t - y) / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.sinh_eq, ← e1, ← e2]; ring
  rw [← hlin]; ring

/-- **`xcorr(G v, m) = xcorr(v, G m)`** at every shift, for pole-free `m`. -/
theorem xcorr_G_swap {a : ℝ} (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : Probe a v) (hm : Probe a m)
    (hmpole : poleR m a = 0) (u : ℝ) : xcorr (Gpole v a) m u = xcorr v (Gpole m a) u := by
  unfold xcorr
  have h1 := shift_swap ha hv hm hmpole u
  have h2 : (∫ t, m t * Gpole v a (t + u)) = ∫ t, Gpole m a t * v (t + u) := by
    have e1 : (∫ t, m t * Gpole v a (t + u)) = ∫ s, Gpole v a s * m (s + -u) := by
      rw [← integral_add_right_eq_self (fun s => Gpole v a s * m (s + -u)) u]
      congr 1; funext t; simp only [add_neg_cancel_right]; ring
    have e2 : (∫ y, v y * Gpole m a (y + -u)) = ∫ t, Gpole m a t * v (t + u) := by
      rw [← integral_add_right_eq_self (fun y => v y * Gpole m a (y + -u)) u]
      congr 1; funext t; simp only [add_neg_cancel_right]; ring
    rw [e1, shift_swap ha hv hm hmpole (-u), e2]
  rw [h1, h2]

theorem bil0_G_swap {a : ℝ} (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : Probe a v) (hm : Probe a m)
    (hmpole : poleR m a = 0) : bil0 a (Gpole v a) m = bil0 a v (Gpole m a) := by
  unfold bil0 archX primeX
  simp only [xcorr_G_swap ha hv hm hmpole]

/-- **`Q − λ₁` pairs `G v` with every pole-free probe to zero**, for pole-free `v` in the ground
space. -/
theorem Gpole_annihilates {a : ℝ} (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : v ∈ groundSpace a)
    (hvpole : poleR v a = 0) (hm : Probe a m) (hmpole : poleR m a = 0) :
    bil0 a (Gpole v a) m - lam a * xcorr (Gpole v a) m 0 = 0 := by
  have el := euler_lagrange_mem hv (Gpole_probe hm ha hmpole)
  rw [hvpole, mul_zero, zero_mul, add_zero] at el
  rw [bil0_G_swap ha hv.1 hm hmpole, xcorr_G_swap ha hv.1 hm hmpole, el, sub_self]

/-- `Q_λ(φ + rψ) = Q_λ(φ) + 2r B_λ(φ, ψ) + r² Q_λ(ψ)`. -/
theorem Qlam_add_smul {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (r : ℝ) :
    weilQ a (fun t => φ t + r * ψ t) - lam a * normSq (fun t => φ t + r * ψ t)
      = (weilQ a φ - lam a * normSq φ)
        + 2 * r * (bil0 a φ ψ + 2 * poleR φ a * poleR ψ a - lam a * xcorr φ ψ 0)
        + r ^ 2 * (weilQ a ψ - lam a * normSq ψ) := by
  have hQ : ∀ f, weilQ a f = weilQ0 a f + 2 * poleR f a ^ 2 := fun f => by unfold weilQ0; ring
  rw [hQ, hQ φ, hQ ψ, weilQ0_add_smul hφ hψ, poleR_add hφ.memL2 (hψ.memL2.const_mul r) a,
    poleR_smul, normSq_add_smul hφ.memL2 hψ.memL2]
  ring

theorem Qlam_nonneg {a : ℝ} {f : ℝ → ℝ} (hf : Probe a f) : 0 ≤ weilQ a f - lam a * normSq f := by
  have := lam_mul_le hf; linarith


/-! ## The ground space contains `G w` -/

theorem Gpole_lin {a : ℝ} {f₁ f₂ : ℝ → ℝ} (h₁ : MemLp f₁ 2 volume) (h₂ : MemLp f₂ 2 volume)
    (α β x : ℝ) :
    Gpole (fun t => α * f₁ t + β * f₂ t) a x = α * Gpole f₁ a x + β * Gpole f₂ a x := by
  unfold Gpole
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((ii_kernel h₁ x _ _).const_mul _)
      ((ii_kernel h₂ x _ _).const_mul _)]
  congr 1; funext y; ring

/-- If `w` and `G w` are both pole-free, `G w` is in the ground space. -/
theorem G_mem_pole_free {a : ℝ} (ha : 0 ≤ a) {w : ℝ → ℝ} (hw : w ∈ groundSpace a)
    (hwp : poleR w a = 0) (hGp : poleR (Gpole w a) a = 0) : Gpole w a ∈ groundSpace a := by
  have hP := Gpole_probe hw.1 ha hwp
  refine ⟨hP, ?_⟩
  have key := Gpole_annihilates ha hw hwp hP hGp
  have hQ : weilQ a (Gpole w a) = bil0 a (Gpole w a) (Gpole w a) := by
    have : weilQ a (Gpole w a) = weilQ0 a (Gpole w a) + 2 * poleR (Gpole w a) a ^ 2 := by
      unfold weilQ0; ring
    rw [this, hGp, weilQ0_eq_bil0 hP]; ring
  rw [hQ, normSq_eq_xcorr hP.memL2]
  linarith

/-- **Rank-one step.** If `w` is pole-free in the ground space and some ground-space element `k` has
`k̂(i/2) ≠ 0`, then `G w` is in the ground space. -/
theorem G_mem_partner {a : ℝ} (ha : 0 ≤ a) {w k : ℝ → ℝ} (hw : w ∈ groundSpace a)
    (hwp : poleR w a = 0) (hk : k ∈ groundSpace a) (hkp : poleR k a ≠ 0) :
    Gpole w a ∈ groundSpace a := by
  set H := Gpole w a
  have hP : Probe a H := Gpole_probe hw.1 ha hwp
  set s := -(poleR H a / poleR k a)
  set f : ℝ → ℝ := fun t => H t + s * k t
  have hf : Probe a f := probe_add_smul hP hk.1 s
  have hfp : poleR f a = 0 := by
    simp only [f]
    rw [poleR_add hP.memL2 (hk.1.memL2.const_mul s) a, poleR_smul]
    simp only [s]; field_simp; ring
  have hB : bil0 a H f + 2 * poleR H a * poleR f a - lam a * xcorr H f 0 = 0 := by
    rw [hfp, mul_zero, add_zero]; exact Gpole_annihilates ha hw hwp hf hfp
  have hexp := Qlam_add_smul hP hf (-1)
  have hfun : (fun t => H t + (-1) * f t) = fun t => (-s) * k t := by
    funext t; simp only [f]; ring
  rw [hfun, weilQ_smul, normSq_smul, hB] at hexp
  have hk0 : weilQ a k - lam a * normSq k = 0 := by rw [hk.2]; ring
  have e0 : (-s) ^ 2 * weilQ a k - lam a * ((-s) ^ 2 * normSq k) = 0 := by
    linear_combination (-s) ^ 2 * hk0
  have n1 := Qlam_nonneg hP
  have n2 := Qlam_nonneg hf
  refine ⟨hP, ?_⟩
  nlinarith

/-- **Degenerate ⇒ edge-flat (round 48, Theorem D, formal).** If a ground state `g` at support `2a`
is not simple, the ground space contains a nonzero pole-free `w` together with its compactly
supported Green solution `G w` (`(G w)'' − (G w)/4 = w`). -/
theorem degenerate_flat {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) :
    ∃ w, w ∈ groundSpace a ∧ poleR w a = 0 ∧ 0 < normSq w ∧ Gpole w a ∈ groundSpace a := by
  have hgV : g ∈ groundSpace a := ((isGroundState_iff ha).1 hg).1
  obtain ⟨h, hhV, hnot⟩ : ∃ h ∈ groundSpace a, ∀ c : ℝ, ¬ h =ᵐ[volume] fun t => c * g t := by
    by_contra H
    push Not at H
    exact hns ⟨hg, H⟩
  have hsub : ∀ c : ℝ, (fun t => h t + (-c) * g t) ∈ groundSpace a := fun c => by
    have := (groundSpace a).add_mem hhV ((groundSpace a).smul_mem (-c) hgV)
    convert this using 1
  have pos_of : ∀ c : ℝ, 0 < normSq (fun t => h t + (-c) * g t) := by
    intro c
    rcases (normSq_nonneg _).lt_or_eq with hlt | h0
    · exact hlt
    · exfalso
      apply hnot c
      filter_upwards [ae_zero_of_normSq (hsub c).1.memL2 h0.symm] with t ht
      have : h t + (-c) * g t = 0 := ht
      linarith
  have hgn : 0 < normSq g := by rw [hg.2.1]; norm_num
  by_cases hgp : poleR g a = 0
  · by_cases hhp : poleR h a = 0
    · -- both pole-free
      set βg := poleR (Gpole g a) a
      set βh := poleR (Gpole h a) a
      by_cases hβ : βg = 0
      · exact ⟨g, hgV, hgp, hgn, G_mem_pole_free ha.le hgV hgp hβ⟩
      · set c := βh / βg
        set w : ℝ → ℝ := fun t => h t + (-c) * g t
        have hwV := hsub c
        have hwp : poleR w a = 0 := by
          simp only [w]; rw [poleR_add hhV.1.memL2 (hgV.1.memL2.const_mul _) a, poleR_smul, hgp, hhp]
          ring
        have hGw : Gpole w a = fun x => Gpole h a x + (-c) * Gpole g a x := by
          funext x
          have := Gpole_lin (a := a) hhV.1.memL2 hgV.1.memL2 1 (-c) x
          simp only [one_mul] at this
          exact this
        have hGp : poleR (Gpole w a) a = 0 := by
          rw [hGw, poleR_add (Gpole_memLp hhV.1 hhp) ((Gpole_memLp hgV.1 hgp).const_mul _) a,
            poleR_smul]
          simp only [c]; field_simp; ring
        exact ⟨w, hwV, hwp, pos_of c, G_mem_pole_free ha.le hwV hwp hGp⟩
    · exact ⟨g, hgV, hgp, hgn, G_mem_partner ha.le hgV hgp hhV hhp⟩
  · set c := poleR h a / poleR g a
    have hwp : poleR (fun t => h t + (-c) * g t) a = 0 := by
      rw [poleR_add hhV.1.memL2 (hgV.1.memL2.const_mul _) a, poleR_smul]
      simp only [c]; field_simp; ring
    exact ⟨_, hsub c, hwp, pos_of c, G_mem_partner ha.le (hsub c) hwp hgV hgp⟩

/-- **The edge-flat structure, in Fourier form.** Non-simplicity puts in the ground space a nonzero
pole-free `w` and `h = G w`, compactly supported in `[−a, a]`, with `ĥ(z) = −ŵ(z)/(z² + ¼)`, i.e.
`h'' − h/4 = w`: both `h` and `h'' = w + h/4` lie in the ground space. -/
theorem degenerate_flat_fourier {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) :
    ∃ w, w ∈ groundSpace a ∧ poleR w a = 0 ∧ 0 < normSq w ∧ Gpole w a ∈ groundSpace a ∧
      (∀ x, a < |x| → Gpole w a x = 0) ∧
      ∀ z : ℂ, z ^ 2 ≠ (Complex.I / 2) ^ 2 →
        (∫ x in (-a)..a, ((Gpole w a x : ℝ) : ℂ) * Complex.exp (Complex.I * z * x))
          = -(ghatC w a z / (z ^ 2 - (Complex.I / 2) ^ 2)) := by
  obtain ⟨w, hw, hwp, hpos, hG⟩ := degenerate_flat ha hg hns
  exact ⟨w, hw, hwp, hpos, hG, Gpole_supp hw.1 hwp, fun z hz => Gpole_hat hw.1 ha.le hwp hz⟩


/-- **Conversely**, a ground space containing a nonzero pole-free `w` and `G w` is not simple: `G w`
cannot be an a.e. multiple of `w`, because `Ĝw = −ŵ/(z² + ¼)`. -/
theorem not_simple_of_green_pair {a : ℝ} (ha : 0 < a) {g w : ℝ → ℝ} (hs : SimpleGround a g)
    (hw : w ∈ groundSpace a) (hwp : poleR w a = 0) (hpos : 0 < normSq w)
    (hG : Gpole w a ∈ groundSpace a) : False := by
  obtain ⟨hgs, hsimp⟩ := hs
  obtain ⟨c₁, h₁⟩ := hsimp w hw
  obtain ⟨c₂, h₂⟩ := hsimp _ hG
  -- on the real line: `ĝ(t)·(c₂(t² + ¼) + c₁) = 0`
  have key : ∀ t : ℝ, ghatC g a t ≠ 0 → c₂ * (t ^ 2 + 1 / 4) + c₁ = 0 := by
    intro t ht
    set r := (ghatC g a t).re
    have hr : ghatC g a t = (r : ℂ) :=
      Complex.ext (by simp [r]) (by simp [ghatC_im_zero hgs.1.even ha.le t])
    have hr0 : r ≠ 0 := fun h => ht (by rw [hr, h, Complex.ofReal_zero])
    have hden : ((t : ℂ)) ^ 2 - (Complex.I / 2) ^ 2 = (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) := by
      rw [div_pow, Complex.I_sq]; push_cast; ring
    have hq : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
    have hz : ((t : ℂ)) ^ 2 ≠ (Complex.I / 2) ^ 2 := by
      intro e
      have h0 : (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) = 0 := by rw [← hden, e, sub_self]
      rw [Complex.ofReal_eq_zero] at h0; linarith
    have hh := Gpole_hat hw.1 ha.le hwp hz
    have e1 : (∫ x in (-a)..a, ((Gpole w a x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x))
        = c₂ * ghatC g a t := by
      rw [show (∫ x in (-a)..a, ((Gpole w a x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x))
        = ghatC (Gpole w a) a t from rfl, ghatC_congr_ae h₂, ghatC_smul]
    rw [e1, ghatC_congr_ae h₁, ghatC_smul, hr, hden] at hh
    have hh' : c₂ * r = -(c₁ * r / (t ^ 2 + 1 / 4)) := by exact_mod_cast hh
    have hm := congrArg (· * (t ^ 2 + 1 / 4)) hh'
    rw [neg_mul, div_mul_cancel₀ _ hq.ne'] at hm
    have : r * (c₂ * (t ^ 2 + 1 / 4) + c₁) = 0 := by linear_combination hm
    exact (mul_eq_zero.1 this).resolve_left hr0
  obtain ⟨t₁, t₂, ht₁, ht₂, hsq⟩ := exists_two_real_ghatC_ne ha hgs.1 hgs.2.1
  have k1 := key t₁ ht₁
  have k2 := key t₂ ht₂
  have hc₂ : c₂ = 0 := by
    have : c₂ * (t₂ ^ 2 - t₁ ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exfalso; linarith
  have hc₁ : c₁ = 0 := by rw [hc₂] at k1; linarith
  have : normSq w = 0 := by
    rw [normSq_congr_ae h₁, hc₁]; simp [normSq]
  linarith

/-- **Formal equivalence (round 48, both directions).** A ground state `g` is simple iff the ground
space contains no nonzero pole-free `w` together with its Green solution `G w`. -/
theorem simple_iff_no_green_pair {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g ↔
      ¬ ∃ w, w ∈ groundSpace a ∧ poleR w a = 0 ∧ 0 < normSq w ∧ Gpole w a ∈ groundSpace a := by
  constructor
  · rintro hs ⟨w, hw, hwp, hpos, hG⟩
    exact not_simple_of_green_pair ha hs hw hwp hpos hG
  · intro H
    by_contra hns
    exact H (degenerate_flat ha hg hns)

end Pilot1ca

#print axioms Pilot1ca.hSw_half_eq
#print axioms Pilot1ca.Gpole_hat
#print axioms Pilot1ca.Gpole_lip
#print axioms Pilot1ca.Gpole_probe
#print axioms Pilot1ca.kernel_zero
#print axioms Pilot1ca.shift_swap
#print axioms Pilot1ca.xcorr_G_swap
#print axioms Pilot1ca.Gpole_annihilates
#print axioms Pilot1ca.G_mem_partner
#print axioms Pilot1ca.degenerate_flat
#print axioms Pilot1ca.degenerate_flat_fourier
#print axioms Pilot1ca.not_simple_of_green_pair
#print axioms Pilot1ca.simple_iff_no_green_pair
