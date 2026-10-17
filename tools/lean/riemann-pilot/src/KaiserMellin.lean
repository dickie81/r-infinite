import Mathlib
import KaiserPoisson

/-! # Mellin–Dirichlet identity for Connes' map (round 163, part 4)

For continuous `f` with `‖f x‖ ≤ C/(1 + x²)` on `x > 0`:

* `mellin_Sf`: `𝓜(Σ_{n≥1} f(n·))(w) = ζ(w) 𝓜f(w)` for `1 < Re w < 2` (Fubini over the sum);
* `mellin_E`: `𝓜(E f)(s) = ζ(s + ½) 𝓜f(s + ½)` for `½ < Re s < 3/2`, where `E f x = √x Σ f(nx)`.
-/

open Complex Filter Topology MeasureTheory Real Set Asymptotics

noncomputable section

namespace Kaiser

/-- `Sf f x = Σ_{n≥1} f(nx)`. -/
def Sf (f : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n : ℕ, f ((n + 1) * x)

theorem isBigO_top_of_bound {f : ℝ → ℂ} {C : ℝ} (hC : ∀ x, 0 < x → ‖f x‖ ≤ C / (1 + x ^ 2)) :
    f =O[atTop] (· ^ (-(2 : ℝ))) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hr : ‖(x : ℝ) ^ (-(2 : ℝ))‖ = (x ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le _), Real.rpow_neg hx.le, Real.rpow_two]
  rw [hr]
  calc ‖f x‖ ≤ C / (1 + x ^ 2) := hC x hx
    _ ≤ |C| / (1 + x ^ 2) := by gcongr; exact le_abs_self C
    _ ≤ |C| / x ^ 2 := by gcongr; linarith
    _ = |C| * (x ^ 2)⁻¹ := div_eq_mul_inv _ _

theorem isBigO_bot_of_bound {f : ℝ → ℂ} {C : ℝ} (hC : ∀ x, 0 < x → ‖f x‖ ≤ C / (1 + x ^ 2)) :
    f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  refine (hC x hx).trans ?_
  have : 0 < 1 + x ^ 2 := by positivity
  rcases le_or_gt 0 C with h | h
  · rw [abs_of_nonneg h, div_le_iff₀ this]; nlinarith [sq_nonneg x]
  · exact (div_neg_of_neg_of_pos h this).le.trans (abs_nonneg C)

theorem mellinConvergent_of_bound {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {C : ℝ}
    (hC : ∀ x, 0 < x → ‖f x‖ ≤ C / (1 + x ^ 2)) {w : ℂ} (h0 : 0 < w.re) (h2 : w.re < 2) :
    MellinConvergent f w :=
  mellinConvergent_of_isBigO_rpow (hf.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_top_of_bound hC) h2 (isBigO_bot_of_bound hC) (by simpa using h0)

/-- The `L¹` norm of the `n`-th term scales like `(n+1)^{−σ}`. -/
theorem integral_norm_term (f : ℝ → ℂ) (w : ℂ) (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (w - 1) • f ((n + 1) * x)‖
      = ((n : ℝ) + 1) ^ (-w.re) * ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (w - 1) • f x‖ := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  set g : ℝ → ℝ := fun y => ‖(y : ℂ) ^ (w - 1) • f y‖
  have e : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ (w - 1) • f ((n + 1) * x)‖
      = ((n : ℝ) + 1) ^ (1 - w.re) * g ((n + 1) * x) := by
    intro x hx
    have hx : (0 : ℝ) < x := hx
    simp only [g, norm_smul, norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos
      (mul_pos hn hx), sub_re, one_re]
    rw [Real.mul_rpow hn.le hx.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hn,
      show 1 - w.re + (w.re - 1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 hn, mul_zero, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_neg hn.le]
  field_simp

/-- **Mellin–Dirichlet.** -/
theorem mellin_Sf {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {C : ℝ}
    (hC : ∀ x, 0 < x → ‖f x‖ ≤ C / (1 + x ^ 2)) {w : ℂ} (h1 : 1 < w.re) (h2 : w.re < 2) :
    mellin (Sf f) w = riemannZeta w * mellin f w := by
  have hconv := mellinConvergent_of_bound hf hC (by linarith) h2
  set F : ℕ → ℝ → ℂ := fun n x => (x : ℂ) ^ (w - 1) • f ((n + 1) * x)
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((MellinConvergent.comp_mul_left (a := (n : ℝ) + 1) (by positivity)).2 hconv)
  have hsum : Summable fun n => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp only [F, integral_norm_term]
    refine Summable.mul_right _ ?_
    have := (Real.summable_nat_rpow_inv.2 h1)
    exact ((summable_nat_add_iff 1).2 this).congr fun n => by
      push_cast; rw [Real.rpow_neg (by positivity)]
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hterm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x = ((n : ℂ) + 1) ^ (-w) * mellin f w := by
    intro n
    have := mellin_comp_mul_left f w (a := (n : ℝ) + 1) (by positivity)
    simp only [mellin, smul_eq_mul] at this
    simp only [F, smul_eq_mul]
    rw [this]; simp only [mellin, smul_eq_mul]; push_cast; rfl
  unfold mellin Sf
  simp_rw [smul_eq_mul, ← tsum_mul_left]
  have hswap' : ∫ x in Ioi (0 : ℝ), ∑' n : ℕ, (x : ℂ) ^ (w - 1) * f ((n + 1) * x)
      = ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), F n x := by
    rw [hswap]; simp only [F, smul_eq_mul]
  rw [hswap']
  simp_rw [hterm]
  rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  congr 1
  refine tsum_congr fun n => ?_
  rw [cpow_neg, one_div]

/-- **Mellin transform of Connes' map.** -/
theorem mellin_E {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {C : ℝ}
    (hC : ∀ x, 0 < x → ‖f x‖ ≤ C / (1 + x ^ 2)) {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 3 / 2) :
    mellin (E f) s = riemannZeta (s + 1 / 2) * mellin f (s + 1 / 2) := by
  have e : mellin (E f) s = mellin (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) • Sf f t) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0 : ℝ) < t := ht
    simp only [E, Sf, smul_eq_mul]
    congr 2
    rw [Real.sqrt_eq_rpow, ofReal_cpow ht.le]; norm_num
  rw [e, mellin_cpow_smul]
  exact mellin_Sf hf hC (by simp; linarith) (by simp; linarith)

end Kaiser

#print axioms Kaiser.mellin_Sf
#print axioms Kaiser.mellin_E
