/-
# Round 518, part 1: a zero detector with the line moved to `Re s = 1/2`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `ρ = β + iγ` be a zero of `ζ` with `1/2 < β < 1`, let `X ≥ 0` and `Y ≥ 1`, and let
`a_n = Σ_{d | n, d ≤ X} μ(d)` be the coefficients of `M_X(s)ζ(s)`, `M_X(s) = Σ_{m ≤ X} μ(m)m^{−s}` (`aX`,
`LSeries_aX`). Then (`detect_identity`)
`Σ_n a_n n^{−ρ}(n/Y + ρ − 1)e^{−n/Y} = (1/2π) ∫ G(1/2 − β + iv) dv`,
with `G(w) = M_X(ρ + w)·(Z(ρ + w)/w)·Γ(w + 1)·Y^w` and `Z(s) = (s − 1)ζ(s)` (`Gfun`); on that line
`ρ + w = 1/2 + i(γ + v)`. For `U ≤ |γ| ≤ 2U`, `8 ≤ Y`, `2 ≤ U ≤ Y`, `1 ≤ X`, `1 ≤ N` and `22 Y log Y ≤ XN`, one of
`|P₁(ρ)| ≥ 1/4`, `|P₂(ρ)| ≥ 1/4` and `|I(ρ)| ≥ U/4` holds (`trichotomy`), where `P₁` and `P₂` are the Dirichlet
polynomials `Σ_{X < j ≤ XN} a_j e^{−j/Y} j^{−ρ}` and `Σ_{X < j ≤ XN} a_j (j/Y)e^{−j/Y} j^{−ρ}` (`Pv`, `b1`, `b2`)
and `I` is the right side of the identity (`Iv`).

* `norm_Gamma_poly_le`, `norm_Gamma_strip_le`: `|Γ(x + it)| ≤ 81e^{12}(1 + |t|)³e^{−π|t|/2}` and
  `|Γ(x + it)|(1 + |t|)⁵ ≤ KG` on `1/2 ≤ x ≤ 3`, from round 517's `Subconvexity.norm_Gamma_le_half` and
  `|Γ(1/2 + it)| ≤ 3e^{−π|t|/2}` (`norm_Gamma_half_le`). Round 520 adds `|Γ(x + it)| ≤ KE e^{−|t|}`
  (`norm_Gamma_exp_le`), the kernel bound of the Linnik contour (`Linnik.norm_pf_le`).
* `integral_kernel_line`: `(1/2π) ∫ x^{−(c+iy)}(Γ(c + iy + 1) + aΓ(c + iy)) dy = (x + a)e^{−x}` for
  `1/2 ≤ c ≤ 2` and `x > 0` (Mathlib's `mellinInv_mellin_eq`, with `Γ` the Mellin transform of `e^{−x}`).
* `LSeries_aX`: `Σ_n a_n n^{−s} = M_X(s)ζ(s)` on `Re s > 1` (Mathlib's `LSeries_convolution'`).
* `sum_side`: the integral on `Re w = 2` integrated termwise (`integral_tsum_of_summable_integral_norm`).
* `Gfun_eq_LSeries`: on `Re(ρ + w) > 1`, `G(w) = L(a, ρ + w)(Γ(w + 1) + (ρ − 1)Γ(w))Y^w`. The kernel
  `Γ(w + 1) + (ρ − 1)Γ(w) = (w + ρ − 1)Γ(w)` turns `M_X ζ` into `M_X Z`; since `Z(ρ) = 0`, the quotient `Z(ρ + w)/w`
  (Mathlib's `dslope`) is entire, and `G` is holomorphic on `Re w > −1` (`differentiableAt_Gfun`).
* `Gfun_strip_bound`: `|G(w)|(1 + |Im w|)³` is bounded on `1/2 − β ≤ Re w ≤ 2`, from `|Z(s)| ≤ C(1 + |Im s|)²` on
  `1/2 ≤ Re s ≤ 3` (`Zr_strip_bound`, with `HalfPlanePNT.riemannZeta_linear_growth`). The line moves from
  `Re w = 2` to `Re w = 1/2 − β` by `SmoothPerron.verticalIntegral_shift`, with no residue.
* `tail_le`: the terms past `M ≥ 22 Y log Y` sum to at most `1/16` in norm, for `Y ≥ 8` and `2 ≤ U ≤ Y`.
-/
import Subconvexity
import HalfPlanePNT
import SmoothPerron
import MollId
import PsiOmega

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace InghamDensity

open ShortWeil PsiOmega

/-! ### Γ on vertical lines -/

/-- `e^{|x|} ≤ 2 cosh x`. -/
theorem exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos x]

/-- `|Γ(½ + it)| ≤ 3 e^{−π|t|/2}`. -/
theorem norm_Gamma_half_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ≤ 3 * Real.exp (-(π * |t|) / 2) := by
  have h1 := Subconvexity.norm_Gamma_half_sq t
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have h2 : Real.exp (π * |t|) ≤ 2 * Real.cosh (π * t) := by
    have := exp_abs_le_two_cosh (π * t)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have he : Real.exp (-(π * |t|) / 2) ^ 2 = Real.exp (-(π * |t|)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hprod : Real.exp (-(π * |t|)) * Real.exp (π * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 ≤ (3 * Real.exp (-(π * |t|) / 2)) ^ 2 := by
    rw [h1, mul_pow, he, div_le_iff₀ hc]
    have h4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(π * |t|))).le
    have := Real.pi_lt_four
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- `yⁿ e^{−y} ≤ n!` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : y ^ n * Real.exp (-y) ≤ n.factorial := by
  have h := Real.pow_div_factorial_le_exp _ hy n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  calc y ^ n * Real.exp (-y) ≤ Real.exp y * n.factorial * Real.exp (-y) := by gcongr
    _ = n.factorial * (Real.exp y * Real.exp (-y)) := by ring
    _ = n.factorial := by rw [← Real.exp_add]; simp

/-- `|Γ(x + it)| ≤ 81 e^{12} (1 + |t|)³ e^{−π|t|/2}` on `½ ≤ x ≤ 3`: Stirling's
`|Γ(x + it)| ≤ |Γ(½ + it)|(e⁴|x + it|)^{x−½}` (round 517's `norm_Gamma_le_half`) and `|Γ(½ + it)| ≤ 3e^{−π|t|/2}`. -/
theorem norm_Gamma_poly_le {x : ℝ} (hx : 1 / 2 ≤ x) (hx3 : x ≤ 3) (t : ℝ) :
    ‖Complex.Gamma (x + t * I)‖ ≤ 81 * Real.exp 12 * ((1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2)) := by
  have h1 := Subconvexity.norm_Gamma_le_half hx t
  have hn1 : ‖(x : ℂ) + t * I‖ ≤ 3 + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    linarith
  have hn2 : 1 / 2 ≤ ‖(x : ℂ) + t * I‖ := by
    have := Complex.re_le_norm ((x : ℂ) + t * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self,
      add_zero] at this
    linarith
  have he4 : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  set b := Real.exp 4 * ‖(x : ℂ) + t * I‖ with hb
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith
  have hb2 : b ^ (x - 1 / 2) ≤ b ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by push_cast; linarith)
  have hb3 : b ^ (3 : ℕ) ≤ Real.exp 12 * (3 * (1 + |t|)) ^ 3 := by
    have : b ≤ Real.exp 4 * (3 * (1 + |t|)) := by
      rw [hb]; gcongr; linarith [abs_nonneg t]
    calc b ^ 3 ≤ (Real.exp 4 * (3 * (1 + |t|))) ^ 3 := by gcongr
      _ = Real.exp 12 * (3 * (1 + |t|)) ^ 3 := by
          rw [mul_pow, ← Real.exp_nat_mul]; norm_num
  have hG := norm_Gamma_half_le t
  calc ‖Complex.Gamma (x + t * I)‖ ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * b ^ (x - 1 / 2) := h1
    _ ≤ 3 * Real.exp (-(π * |t|) / 2) * (Real.exp 12 * (3 * (1 + |t|)) ^ 3) := by
        gcongr
        exact hb2.trans hb3
    _ = 81 * Real.exp 12 * ((1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2)) := by ring

/-- The constant of `norm_Gamma_strip_le`. -/
def KG : ℝ := 81 * Real.exp 12 * (2 ^ 8 * 40320 * Real.exp (1 / 2))

theorem KG_pos : 0 < KG := by unfold KG; positivity

/-- **`|Γ(x + it)|(1 + |t|)⁵ ≤ KG` on `½ ≤ x ≤ 3`**, from `norm_Gamma_poly_le` and `y⁸e^{−y} ≤ 8!` at
`y = (1 + |t|)/2`. -/
theorem norm_Gamma_strip_le {x : ℝ} (hx : 1 / 2 ≤ x) (hx3 : x ≤ 3) (t : ℝ) :
    ‖Complex.Gamma (x + t * I)‖ * (1 + |t|) ^ 5 ≤ KG := by
  have hpow : (1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2) ≤ 2 ^ 8 * 40320 * Real.exp (1 / 2) := by
    have hy : 0 ≤ (1 + |t|) / 2 := by positivity
    have h8 := pow_mul_exp_neg_le 8 hy
    have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [hf] at h8
    have hexp : Real.exp (-(π * |t|) / 2) ≤ Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := Real.pi_gt_three
      nlinarith [abs_nonneg t]
    calc (1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2)
        ≤ (1 + |t|) ^ 8 * (Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2)) := by gcongr
      _ = 2 ^ 8 * (((1 + |t|) / 2) ^ 8 * Real.exp (-((1 + |t|) / 2))) * Real.exp (1 / 2) := by ring
      _ ≤ 2 ^ 8 * 40320 * Real.exp (1 / 2) := by gcongr
  calc ‖Complex.Gamma (x + t * I)‖ * (1 + |t|) ^ 5
      ≤ 81 * Real.exp 12 * ((1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2)) * (1 + |t|) ^ 5 := by
        gcongr; exact norm_Gamma_poly_le hx hx3 t
    _ = 81 * Real.exp 12 * ((1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2)) := by ring
    _ ≤ 81 * Real.exp 12 * (2 ^ 8 * 40320 * Real.exp (1 / 2)) := by gcongr
    _ = KG := rfl

/-- The constant of `norm_Gamma_exp_le`. -/
def KE : ℝ := 81 * Real.exp 12 * (48 * Real.exp (1 / 2))

theorem KE_pos : 0 < KE := by unfold KE; positivity

/-- **`|Γ(x + it)| ≤ KE e^{−|t|}` on `½ ≤ x ≤ 3`**, from `norm_Gamma_poly_le` and `y³e^{−y} ≤ 3!` at
`y = (1 + |t|)/2`, as `π/2 > 3/2`. -/
theorem norm_Gamma_exp_le {x : ℝ} (hx : 1 / 2 ≤ x) (hx3 : x ≤ 3) (t : ℝ) :
    ‖Complex.Gamma (x + t * I)‖ ≤ KE * Real.exp (-|t|) := by
  have h := norm_Gamma_poly_le hx hx3 t
  have hy : 0 ≤ (1 + |t|) / 2 := by positivity
  have h3 := pow_mul_exp_neg_le 3 hy
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h3
  have hexp : Real.exp (-(π * |t|) / 2) ≤
      Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2) * Real.exp (-|t|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := Real.pi_gt_three
    nlinarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2) ≤ 48 * Real.exp (1 / 2) * Real.exp (-|t|) := by
    calc (1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2)
        ≤ (1 + |t|) ^ 3 * (Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2) * Real.exp (-|t|)) := by gcongr
      _ = 8 * (((1 + |t|) / 2) ^ 3 * Real.exp (-((1 + |t|) / 2))) * Real.exp (1 / 2) * Real.exp (-|t|) := by
          ring
      _ ≤ 8 * 6 * Real.exp (1 / 2) * Real.exp (-|t|) := by gcongr
      _ = 48 * Real.exp (1 / 2) * Real.exp (-|t|) := by ring
  calc ‖Complex.Gamma (x + t * I)‖ ≤ 81 * Real.exp 12 * ((1 + |t|) ^ 3 * Real.exp (-(π * |t|) / 2)) := h
    _ ≤ 81 * Real.exp 12 * (48 * Real.exp (1 / 2) * Real.exp (-|t|)) := by gcongr
    _ = KE * Real.exp (-|t|) := by unfold KE; ring

/-- `Γ` is continuous along a vertical line `Re s = x > 0`. -/
theorem continuous_Gamma_line {x : ℝ} (hx : 0 < x) : Continuous fun t : ℝ => Complex.Gamma (x + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : ∀ m : ℕ, ((x : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self, add_zero,
      neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact ContinuousAt.comp (g := Complex.Gamma) (f := fun t : ℝ => (x : ℂ) + t * I)
    (Complex.differentiableAt_Gamma _ hne).continuousAt (by fun_prop)

/-- A continuous `f` with `|f(t)|(1 + |t|)² ≤ K` is integrable. -/
theorem integrable_of_le_sq {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, ‖f t‖ * (1 + |t|) ^ 2 ≤ K) : Integrable f := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hf.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hle : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖f t‖ * (1 + t ^ 2) ≤ ‖f t‖ * (1 + |t|) ^ 2 := by gcongr
    _ ≤ K := hK t

theorem Gamma_line_integrable {x : ℝ} (hx : 1 / 2 ≤ x) (hx3 : x ≤ 3) :
    Integrable fun t : ℝ => Complex.Gamma (x + t * I) := by
  refine integrable_of_le_sq (continuous_Gamma_line (by linarith)) (K := KG) fun t => ?_
  have h := norm_Gamma_strip_le hx hx3 t
  have h1 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 5 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
  calc ‖Complex.Gamma (x + t * I)‖ * (1 + |t|) ^ 2 ≤ ‖Complex.Gamma (x + t * I)‖ * (1 + |t|) ^ 5 := by gcongr
    _ ≤ KG := h

/-! ### The Mellin kernel -/

theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral hs]

theorem mellinConvergent_exp_neg {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s := by
  refine (Complex.GammaIntegral_convergent hs).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

/-- **Mellin inversion for `e^{−x}`**: `(1/2π) ∫ x^{−(c+iy)} Γ(c + iy) dy = e^{−x}` for `½ ≤ c ≤ 3`, `x > 0`. -/
theorem integral_Gamma_line {c x : ℝ} (hc : 1 / 2 ≤ c) (hc3 : c ≤ 3) (hx : 0 < x) :
    (1 / (2 * π) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) * Complex.Gamma (c + y * I)
      = (Real.exp (-x) : ℂ) := by
  have hre : ∀ y : ℝ, 0 < ((c : ℂ) + y * I).re := fun y => by simp; linarith
  have hM : ∀ y : ℝ, mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (c + y * I) = Complex.Gamma (c + y * I) :=
    fun y => mellin_exp_neg (hre y)
  have hV : Complex.VerticalIntegrable (mellin fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) c := by
    unfold Complex.VerticalIntegrable
    simp_rw [hM]
    exact Gamma_line_integrable hc hc3
  have hcont : ContinuousAt (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) x := by fun_prop
  have h := mellinInv_mellin_eq c (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) hx
    (mellinConvergent_exp_neg (by simp; linarith)) hV hcont
  rw [mellinInv] at h
  simp_rw [hM, smul_eq_mul] at h
  rw [← h, Complex.real_smul]
  push_cast
  ring

/-- **The kernel**: `(1/2π) ∫ x^{−(c+iy)} (Γ(c + iy + 1) + aΓ(c + iy)) dy = (x + a)e^{−x}` for `½ ≤ c ≤ 2`. -/
theorem integral_kernel_line {c x : ℝ} (hc : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hx : 0 < x) (a : ℂ) :
    (1 / (2 * π) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) *
        (Complex.Gamma (c + y * I + 1) + a * Complex.Gamma (c + y * I))
      = ((x : ℂ) + a) * (Real.exp (-x) : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hshift : ∀ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) * Complex.Gamma (c + y * I + 1)
      = (x : ℂ) * ((x : ℂ) ^ (-(((c + 1 : ℝ) : ℂ) + y * I)) * Complex.Gamma ((c + 1 : ℝ) + y * I)) := by
    intro y
    have e1 : -((c : ℂ) + y * I) = 1 + -(((c + 1 : ℝ) : ℂ) + y * I) := by push_cast; ring
    have e2 : (c : ℂ) + y * I + 1 = ((c + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    rw [e1, Complex.cpow_add _ _ hx', Complex.cpow_one, e2]
    ring
  have hint1 : Integrable fun y : ℝ => (x : ℂ) ^ (-(((c + 1 : ℝ) : ℂ) + y * I)) * Complex.Gamma ((c + 1 : ℝ) + y * I) := by
    refine Integrable.mono' ((Gamma_line_integrable (x := c + 1) (by linarith) (by linarith)).norm.const_mul
      (x ^ (-(c + 1)))) ?_ (Eventually.of_forall fun y => ?_)
    · exact (Continuous.mul (Continuous.const_cpow (by fun_prop) (Or.inl hx'))
        (continuous_Gamma_line (by linarith))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
  have hint2 : Integrable fun y : ℝ => (x : ℂ) ^ (-((c : ℂ) + y * I)) * Complex.Gamma (c + y * I) := by
    refine Integrable.mono' ((Gamma_line_integrable hc (by linarith)).norm.const_mul (x ^ (-c))) ?_
      (Eventually.of_forall fun y => ?_)
    · exact (Continuous.mul (Continuous.const_cpow (by fun_prop) (Or.inl hx'))
        (continuous_Gamma_line (by linarith))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
  have e : ∀ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) *
        (Complex.Gamma (c + y * I + 1) + a * Complex.Gamma (c + y * I))
      = (x : ℂ) * ((x : ℂ) ^ (-(((c + 1 : ℝ) : ℂ) + y * I)) * Complex.Gamma ((c + 1 : ℝ) + y * I))
        + a * ((x : ℂ) ^ (-((c : ℂ) + y * I)) * Complex.Gamma (c + y * I)) := by
    intro y; rw [mul_add, hshift]; ring
  simp_rw [e]
  rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul]
  have h1 := integral_Gamma_line (c := c + 1) (by linarith) (by linarith) hx
  have h2 := integral_Gamma_line hc (by linarith) hx
  set J1 := ∫ y : ℝ, (x : ℂ) ^ (-(((c + 1 : ℝ) : ℂ) + y * I)) * Complex.Gamma ((c + 1 : ℝ) + y * I) with hJ1
  set J2 := ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) * Complex.Gamma (c + y * I) with hJ2
  rw [show (1 / (2 * π) : ℂ) * ((x : ℂ) * J1 + a * J2)
      = (x : ℂ) * ((1 / (2 * π) : ℂ) * J1) + a * ((1 / (2 * π) : ℂ) * J2) by ring, h1, h2]
  ring

/-! ### The coefficients of `M_X(s)ζ(s)` -/

/-- `a_n = Σ_{d | n, d ≤ X} μ(d)`. -/
def aX (X n : ℕ) : ℂ := ∑ d ∈ n.divisors, if d ≤ X then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0

/-- `μ` cut at `X`. -/
def muX (X n : ℕ) : ℂ := if n ≤ X then ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0

theorem aX_eq_conv (X : ℕ) : aX X = LSeries.convolution (muX X) 1 := by
  funext n
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a _ => muX X a)]
  rfl

theorem aX_zero (X : ℕ) : aX X 0 = 0 := by simp [aX]

theorem aX_one {X : ℕ} (hX : 1 ≤ X) : aX X 1 = 1 := by simp [aX, hX]

theorem aX_eq_zero {X n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ X) : aX X n = 0 := by
  unfold aX
  rw [Finset.sum_congr rfl (g := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ)) fun d hd => by
    rw [ite_eq_left ((Nat.divisor_le hd).trans hn)], sum_divisors_moebius, ite_eq_right (by omega)]

theorem norm_aX_le (X n : ℕ) : ‖aX X n‖ ≤ (n.divisors.card : ℝ) := by
  unfold aX
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  split_ifs
  · rw [Complex.norm_intCast]; push_cast
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

theorem norm_aX_le_self (X n : ℕ) : ‖aX X n‖ ≤ n :=
  (norm_aX_le X n).trans (by exact_mod_cast Nat.card_divisors_le_self n)

theorem muX_summable (X : ℕ) (s : ℂ) : LSeriesSummable (muX X) s := by
  refine summable_of_ne_finset_zero (s := Finset.Ioc 0 X) fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hpos.ne', muX, ite_eq_right fun h => hn (Finset.mem_Ioc.2 ⟨hpos, h⟩), zero_div]

theorem LSeries_muX (X : ℕ) (s : ℂ) : LSeries (muX X) s = moll X s := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc 0 X) fun n hn => ?_]
  · unfold moll
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h0, hX⟩ := Finset.mem_Ioc.1 hn
    rw [LSeries.term_of_ne_zero (by omega), muX, ite_eq_left hX, Complex.cpow_neg, div_eq_mul_inv]
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hpos.ne', muX, ite_eq_right fun h => hn (Finset.mem_Ioc.2 ⟨hpos, h⟩), zero_div]

/-- `Σ a_n n^{−s} = M_X(s)ζ(s)` on `Re s > 1`. -/
theorem LSeries_aX (X : ℕ) {s : ℂ} (hs : 1 < s.re) : LSeries (aX X) s = moll X s * riemannZeta s := by
  rw [aX_eq_conv, LSeries_convolution' (muX_summable X s) (LSeriesSummable_one_iff.2 hs), LSeries_muX,
    LSeries_one_eq_riemannZeta hs]

theorem LSeriesSummable_aX (X : ℕ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (aX X) s := by
  rw [aX_eq_conv]; exact (muX_summable X s).convolution (LSeriesSummable_one_iff.2 hs)

/-! ### The integrand -/

/-- **The integrand** `M_X(ρ + w)·(Z(ρ + w)/w)·Γ(w + 1)·Y^w`, with `Z(s) = (s − 1)ζ(s)`: at a zero `ρ` of `ζ`, the
quotient `Z(ρ + w)/w` (Mathlib's `dslope` at `0`) is entire, and `Γ(w + 1)` is holomorphic on `Re w > −1`. -/
def Gfun (X : ℕ) (Y : ℝ) (ρ w : ℂ) : ℂ :=
  moll X (ρ + w) * dslope (fun z => Zr (ρ + z)) 0 w * Complex.Gamma (w + 1) * (Y : ℂ) ^ w

theorem differentiable_moll (X : ℕ) : Differentiable ℂ (moll X) := by
  have e : moll X = fun s => ∑ m ∈ Finset.Ioc 0 X, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * (m : ℂ) ^ (-s) :=
    rfl
  rw [e]
  refine Differentiable.fun_sum fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Ioc.1 hm).1; omega)
  exact (differentiable_id.neg.const_cpow (Or.inl hm0)).const_mul _

theorem differentiable_dslope (ρ : ℂ) : Differentiable ℂ (dslope (fun z => Zr (ρ + z)) 0) := by
  have hd : Differentiable ℂ (fun z => Zr (ρ + z)) := differentiable_Zr.comp (by fun_prop)
  have h := (Complex.differentiableOn_dslope (s := univ) (c := 0) Filter.univ_mem).2 hd.differentiableOn
  exact fun w => h.differentiableAt Filter.univ_mem

theorem differentiableAt_Gfun (X : ℕ) {Y : ℝ} (hY : 0 < Y) (ρ : ℂ) {w : ℂ} (hw : -1 < w.re) :
    DifferentiableAt ℂ (Gfun X Y ρ) w := by
  have h1 : DifferentiableAt ℂ (fun w => moll X (ρ + w)) w :=
    (differentiable_moll X).differentiableAt.comp w (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun w => Complex.Gamma (w + 1)) w := by
    refine DifferentiableAt.comp (g := Complex.Gamma) w (Complex.differentiableAt_Gamma _ fun m h => ?_) (by fun_prop)
    have := congrArg Complex.re h
    simp only [add_re, one_re, neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h4 : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hY.ne'))
  exact ((h1.mul (differentiable_dslope ρ w)).mul h3).mul h4

/-- `Z(ρ + w)/w` for `w ≠ 0`, at a zero `ρ ≠ 1` of `ζ`. -/
theorem dslope_eq {ρ : ℂ} (hρ : Zr ρ = 0) {w : ℂ} (hw : w ≠ 0) :
    dslope (fun z => Zr (ρ + z)) 0 w = Zr (ρ + w) / w := by
  rw [dslope_of_ne _ hw, slope_def_field]
  simp [hρ]

theorem Zr_zero_of_zeta {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) : Zr ρ = 0 := by
  rw [Zr_of_ne hρ1, hρ, mul_zero]

/-- **On `Re(ρ + w) > 1`** the integrand is `L(a, ρ + w)·(Γ(w + 1) + (ρ − 1)Γ(w))·Y^w`. -/
theorem Gfun_eq_LSeries (X : ℕ) (Y : ℝ) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) {w : ℂ} (hw : w ≠ 0)
    (hre : 1 < (ρ + w).re) :
    Gfun X Y ρ w =
      LSeries (aX X) (ρ + w) * (Complex.Gamma (w + 1) + (ρ - 1) * Complex.Gamma w) * (Y : ℂ) ^ w := by
  have hρw : ρ + w ≠ 1 := fun h => by rw [h] at hre; simp at hre
  rw [Gfun, dslope_eq (Zr_zero_of_zeta hρ hρ1) hw, Zr_of_ne hρw, LSeries_aX X hre,
    Complex.Gamma_add_one w hw]
  field_simp
  ring

/-- **On the line `Re w = ½ − Re ρ`**: `G(w) = M_X(ρ + w) Z(ρ + w) Γ(w + 1)/w · Y^w`. -/
theorem Gfun_eq_left (X : ℕ) (Y : ℝ) {ρ : ℂ} (hρ : Zr ρ = 0) {w : ℂ} (hw : w ≠ 0) :
    Gfun X Y ρ w = moll X (ρ + w) * Zr (ρ + w) * (Complex.Gamma (w + 1) / w) * (Y : ℂ) ^ w := by
  rw [Gfun, dslope_eq hρ hw]
  ring

/-! ### Bounds on the strip -/

/-- `|M_X(s)| ≤ X` for `Re s ≥ 0`. -/
theorem norm_moll_le_X (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) : ‖moll X s‖ ≤ X := by
  unfold moll
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Finset.Ioc 0 X, ‖((ArithmeticFunction.moebius m : ℤ) : ℂ) * (m : ℂ) ^ (-s)‖ ≤ 1 := by
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hm0]
    have hμ : (|((ArithmeticFunction.moebius m : ℤ) : ℝ)|) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 : (m : ℝ) ^ (-s).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm0) (by simp; linarith)
    calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * (m : ℝ) ^ (-s).re ≤ 1 * 1 :=
          mul_le_mul hμ h1 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  refine (Finset.sum_le_sum hterm).trans ?_
  simp

/-- `|Z(s)| ≤ C(1 + |Im s|)²` on `½ ≤ Re s ≤ 3`. -/
theorem Zr_strip_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖Zr s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    differentiable_Zr.continuous.continuousOn
  refine ⟨max C₀ 9, le_max_of_le_right (by norm_num), fun s hs1 hs3 => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases lt_or_ge |s.im| 1 with ht | ht
  · have hball : s ∈ Metric.closedBall (0 : ℂ) 4 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 4 := by rw [abs_of_nonneg (by linarith)]; linarith
    calc ‖Zr s‖ ≤ C₀ := hC₀ s hball
      _ ≤ max C₀ 9 * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max C₀ 9 * (1 + |s.im|) ^ 2 := by gcongr
  · have hs1' : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
    rw [Zr_of_ne hs1', norm_mul]
    have hz := HalfPlanePNT.riemannZeta_linear_growth (δ := 1 / 2) (by norm_num) hs1 ht
    have hsub : ‖s - 1‖ ≤ 2 + |s.im| := by
      have hre : |s.re - 1| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
      calc ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re - 1| + |s.im| := by simp
        _ ≤ 2 + |s.im| := by linarith
    have hinv : (5 / 2 + (1 / 2 : ℝ)⁻¹) = 9 / 2 := by norm_num
    rw [hinv] at hz
    calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (2 + |s.im|) * (9 / 2 * |s.im|) :=
          mul_le_mul hsub hz (norm_nonneg _) (by positivity)
      _ ≤ 9 * (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
      _ ≤ max C₀ 9 * (1 + |s.im|) ^ 2 := by gcongr; exact le_max_right _ _

/-- `Γ` on `½ ≤ Re z ≤ 3`, in the variable `z`. -/
theorem norm_Gamma_le' {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h3 : z.re ≤ 3) :
    ‖Complex.Gamma z‖ * (1 + |z.im|) ^ 5 ≤ KG := by
  have := norm_Gamma_strip_le h1 h3 z.im
  rwa [Complex.re_add_im] at this

/-- **`|G(w)|(1 + |Im w|)³` is bounded on the strip `½ − Re ρ ≤ Re w ≤ 2`.** -/
theorem Gfun_strip_bound (X : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ} (hρ : Zr ρ = 0) (hρ1 : 1 / 2 < ρ.re)
    (hρ2 : ρ.re < 1) :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gfun X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zr_strip_bound
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_dslope ρ).continuous.continuousOn
  set D := max C₁ (CZ * (1 + |ρ.im|) ^ 2) with hD
  have hD0 : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨X * D * KG * Y ^ (2 : ℝ), fun w hw1 hw2 => ?_⟩
  have h1 : 1 ≤ (1 + |w.im|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg w.im])
  have hDw : ‖dslope (fun z => Zr (ρ + z)) 0 w‖ ≤ D * (1 + |w.im|) ^ 2 := by
    rcases le_or_gt ‖w‖ 1 with hw | hw
    · calc ‖dslope (fun z => Zr (ρ + z)) 0 w‖ ≤ C₁ :=
            hC₁ w (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
        _ ≤ D := le_max_left _ _
        _ ≤ D * (1 + |w.im|) ^ 2 := le_mul_of_one_le_right hD0 h1
    · have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
      rw [dslope_eq hρ hw0, norm_div]
      have hz := hCZ (ρ + w) (by simp; linarith) (by simp; linarith)
      have him : |(ρ + w).im| ≤ |ρ.im| + |w.im| := by simp only [add_im]; exact abs_add_le _ _
      calc ‖Zr (ρ + w)‖ / ‖w‖ ≤ ‖Zr (ρ + w)‖ := div_le_self (norm_nonneg _) hw.le
        _ ≤ CZ * (1 + |(ρ + w).im|) ^ 2 := hz
        _ ≤ CZ * ((1 + |ρ.im|) * (1 + |w.im|)) ^ 2 := by
            gcongr
            nlinarith [abs_nonneg ρ.im, abs_nonneg w.im]
        _ = CZ * (1 + |ρ.im|) ^ 2 * (1 + |w.im|) ^ 2 := by ring
        _ ≤ D * (1 + |w.im|) ^ 2 := by gcongr; exact le_max_right _ _
  have hm := norm_moll_le_X X (s := ρ + w) (by simp; linarith)
  have hG := norm_Gamma_le' (z := w + 1) (by simp; linarith) (by simp; linarith)
  have hGim : (w + 1).im = w.im := by simp
  rw [hGim] at hG
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY hw2
  unfold Gfun
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖moll X (ρ + w)‖ * ‖dslope (fun z => Zr (ρ + z)) 0 w‖ * ‖Complex.Gamma (w + 1)‖ * ‖(Y : ℂ) ^ w‖
        * (1 + |w.im|) ^ 3
      ≤ X * (D * (1 + |w.im|) ^ 2) * ‖Complex.Gamma (w + 1)‖ * Y ^ (2 : ℝ) * (1 + |w.im|) ^ 3 := by
        gcongr
    _ = X * D * Y ^ (2 : ℝ) * (‖Complex.Gamma (w + 1)‖ * (1 + |w.im|) ^ 5) := by ring
    _ ≤ X * D * Y ^ (2 : ℝ) * KG := by gcongr
    _ = X * D * KG * Y ^ (2 : ℝ) := by ring

theorem continuous_Gfun_line (X : ℕ) {Y : ℝ} (hY : 0 < Y) (ρ : ℂ) {σ : ℝ} (hσ : -1 < σ) :
    Continuous fun t : ℝ => Gfun X Y ρ (σ + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ContinuousAt.comp (g := Gfun X Y ρ) (f := fun t : ℝ => (σ : ℂ) + t * I)
    (differentiableAt_Gfun X hY ρ (by simpa using hσ)).continuousAt (by fun_prop)

theorem Gfun_line_integrable (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} {C : ℝ}
    (hC : ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gfun X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C)
    (hρ2 : ρ.re < 1) {σ : ℝ} (hσ1 : 1 / 2 - ρ.re ≤ σ) (hσ2 : σ ≤ 2) :
    Integrable fun t : ℝ => Gfun X Y ρ (σ + t * I) := by
  refine integrable_of_le_sq (continuous_Gfun_line X hY ρ (by linarith)) (K := C) fun t => ?_
  have h := hC (σ + t * I) (by simpa using hσ1) (by simpa using hσ2)
  have him : ((σ : ℂ) + t * I).im = t := by simp
  rw [him] at h
  have h23 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
  calc ‖Gfun X Y ρ (σ + t * I)‖ * (1 + |t|) ^ 2 ≤ ‖Gfun X Y ρ (σ + t * I)‖ * (1 + |t|) ^ 3 := by gcongr
    _ ≤ C := h

theorem Gfun_decay (X : ℕ) {Y : ℝ} {ρ : ℂ} {C : ℝ}
    (hC : ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gfun X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc (1 / 2 - ρ.re) 2, ∀ y : ℝ, T₀ ≤ |y| → ‖Gfun X Y ρ (x + y * I)‖ ≤ η := by
  intro η hη
  refine ⟨C / η, fun x hx y hy => ?_⟩
  have hb := hC (x + y * I) (by simpa using hx.1) (by simpa using hx.2)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at hb
  have hpos : 0 < 1 + |y| := by positivity
  have h3 : 1 + |y| ≤ (1 + |y|) ^ 3 := le_self_pow₀ (by linarith [abs_nonneg y]) (by norm_num)
  have hCη : C ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hy
  have hG0 := norm_nonneg (Gfun X Y ρ (x + y * I))
  have : ‖Gfun X Y ρ (x + y * I)‖ * (1 + |y|) ≤ η * (1 + |y|) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hG0]
  exact le_of_mul_le_mul_right this hpos

/-! ### The sum side -/

theorem kernel_integrable {c x : ℝ} (hc : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hx : 0 < x) (a : ℂ) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-((c : ℂ) + y * I)) *
        (Complex.Gamma (c + y * I + 1) + a * Complex.Gamma (c + y * I)) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have e1 : ∀ y : ℝ, (c : ℂ) + y * I + 1 = ((c + 1 : ℝ) : ℂ) + y * I := fun y => by push_cast; ring
  have hG1 : Integrable fun y : ℝ => Complex.Gamma ((c : ℂ) + y * I + 1) := by
    simp_rw [e1]; exact Gamma_line_integrable (by linarith) (by linarith)
  have hG0 : Integrable fun y : ℝ => Complex.Gamma ((c : ℂ) + y * I) :=
    Gamma_line_integrable hc (by linarith)
  have hcont1 : Continuous fun y : ℝ => Complex.Gamma ((c : ℂ) + y * I + 1) := by
    simp_rw [e1]; exact continuous_Gamma_line (by linarith)
  refine Integrable.mono' ((hG1.norm.add (hG0.norm.const_mul ‖a‖)).const_mul (x ^ (-c))) ?_
    (Eventually.of_forall fun y => ?_)
  · exact (Continuous.mul (Continuous.const_cpow (by fun_prop) (Or.inl hx'))
      (hcont1.add (continuous_const.mul (continuous_Gamma_line (by linarith))))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((c : ℂ) + y * I)).re = -c := by simp
    rw [hre]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    exact le_rfl

/-- **The sum side**: `(1/2π) ∫ L(a, ρ + w)(Γ(w + 1) + (ρ − 1)Γ(w))Y^w dt` over `w = 2 + it` is
`Σ_n a_n n^{−ρ}(n/Y + ρ − 1)e^{−n/Y}`. -/
theorem sum_side (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρre : 0 < ρ.re) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries (aX X) (ρ + (((2 : ℝ) : ℂ) + t * I)) *
        (Complex.Gamma (((2 : ℝ) : ℂ) + t * I + 1) + (ρ - 1) * Complex.Gamma (((2 : ℝ) : ℂ) + t * I)) *
        (Y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I)
      = ∑' n : ℕ, aX X n * (n : ℂ) ^ (-ρ) * ((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1)) *
          (Real.exp (-((n : ℝ) / Y)) : ℂ) := by
  set w : ℝ → ℂ := fun t => ((2 : ℝ) : ℂ) + t * I with hw
  set K : ℝ → ℂ := fun t => Complex.Gamma (w t + 1) + (ρ - 1) * Complex.Gamma (w t) with hK
  have hre2 : 1 < (ρ + 2).re := by simp; linarith
  have hsumm := LSeriesSummable_aX X hre2
  let F : ℕ → ℝ → ℂ := fun n t => LSeries.term (aX X) (ρ + w t) n * K t * (Y : ℂ) ^ (w t)
  have hterm : ∀ n t, ‖LSeries.term (aX X) (ρ + w t) n‖ = ‖LSeries.term (aX X) (ρ + 2) n‖ := by
    intro n t
    simp only [LSeries.norm_term_eq]
    congr 3
    simp [hw]
  have hY2 : ∀ t, ‖(Y : ℂ) ^ (w t)‖ = Y ^ (2 : ℝ) := fun t => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]; simp [hw]
  have hKint : Integrable K := by
    have := kernel_integrable (c := 2) (x := 1) (by norm_num) le_rfl one_pos (ρ - 1)
    simpa [hK, hw] using this
  have hnormF : ∀ n t, ‖F n t‖ = ‖LSeries.term (aX X) (ρ + 2) n‖ * Y ^ (2 : ℝ) * ‖K t‖ := by
    intro n t
    simp only [F, norm_mul, hterm, hY2]
    ring
  -- each term in kernel form
  have hFk : ∀ n : ℕ, n ≠ 0 → ∀ t, F n t = (aX X n * (n : ℂ) ^ (-ρ)) *
      ((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((2 : ℝ) + t * I : ℂ)) *
        (Complex.Gamma (((2 : ℝ) : ℂ) + t * I + 1) + (ρ - 1) * Complex.Gamma (((2 : ℝ) : ℂ) + t * I))) := by
    intro n hn t
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [F, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hn', ← div_div]
    have := SmoothPerron.div_cpow_mul_cpow hn hY (aX X n / (n : ℂ) ^ ρ) (K t) (w t)
    rw [this, smul_eq_mul, Complex.cpow_neg (n : ℂ) ρ, div_eq_mul_inv]
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [F, LSeries.term_zero, zero_mul]; exact integrable_zero _ _ _
    · have hx : (0 : ℝ) < (n : ℝ) / Y := div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) hY
      have := (kernel_integrable (c := 2) (by norm_num) le_rfl hx (ρ - 1)).const_mul (aX X n * (n : ℂ) ^ (-ρ))
      refine this.congr (Eventually.of_forall fun t => ?_)
      rw [hFk n hn t]
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    exact (hsumm.norm.mul_right (Y ^ (2 : ℝ))).mul_right _
  have hsum_pt : ∀ t : ℝ, LSeries (aX X) (ρ + w t) * K t * (Y : ℂ) ^ (w t) = ∑' n, F n t := by
    intro t
    simp only [F, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
  have hint_n : ∀ n : ℕ, (1 / (2 * π) : ℂ) * ∫ t, F n t
      = aX X n * (n : ℂ) ^ (-ρ) * ((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1)) * (Real.exp (-((n : ℝ) / Y)) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, aX_zero]
    · have hx : (0 : ℝ) < (n : ℝ) / Y := div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) hY
      have hk := integral_kernel_line (c := 2) (by norm_num) le_rfl hx (ρ - 1)
      simp_rw [hFk n hn]
      rw [integral_const_mul, ← mul_assoc, mul_comm (1 / (2 * π) : ℂ), mul_assoc, hk]
      ring
  calc (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries (aX X) (ρ + (((2 : ℝ) : ℂ) + t * I)) *
        (Complex.Gamma (((2 : ℝ) : ℂ) + t * I + 1) + (ρ - 1) * Complex.Gamma (((2 : ℝ) : ℂ) + t * I)) *
        (Y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I)
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, ∑' n, F n t := by
        congr 1; congr 1; funext t; exact hsum_pt t
    _ = (1 / (2 * π) : ℂ) * ∑' n, ∫ t, F n t := by
        rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = ∑' n, (1 / (2 * π) : ℂ) * ∫ t, F n t := by rw [tsum_mul_left]
    _ = _ := by congr 1; funext n; exact hint_n n

/-! ### The identity at a zero -/

/-- **The identity at a zero.** For a zero `ρ` of `ζ` with `½ < Re ρ < 1`, `X ≥ 0` and `Y ≥ 1`:
`Σ_n a_n n^{−ρ}(n/Y + ρ − 1)e^{−n/Y} = (1/2π) ∫ G(½ − Re ρ + iv) dv`. The kernel
`Γ(w + 1) + (ρ − 1)Γ(w) = (w + ρ − 1)Γ(w)` turns `M_X ζ` into `M_X Z` on `Re w = 2`, and the zero of `Z` at `ρ` cancels
the pole of `Γ(w)` at `w = 0`, so the line moves to `Re(ρ + w) = ½` with no residue. -/
theorem detect_identity (X : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) :
    ∑' n : ℕ, aX X n * (n : ℂ) ^ (-ρ) * ((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1)) *
        (Real.exp (-((n : ℝ) / Y)) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ v : ℝ, Gfun X Y ρ (((1 / 2 - ρ.re : ℝ) : ℂ) + v * I) := by
  have hY0 : 0 < Y := by linarith
  have hρne : ρ ≠ 1 := fun h => by rw [h] at hρ2; simp at hρ2
  have hZ := Zr_zero_of_zeta hρ hρne
  obtain ⟨C, hC⟩ := Gfun_strip_bound X hY hZ hρ1 hρ2
  rw [← sum_side X hY0 (by linarith : 0 < ρ.re)]
  have hright : ∀ t : ℝ, LSeries (aX X) (ρ + (((2 : ℝ) : ℂ) + t * I)) *
        (Complex.Gamma (((2 : ℝ) : ℂ) + t * I + 1) + (ρ - 1) * Complex.Gamma (((2 : ℝ) : ℂ) + t * I)) *
        (Y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) = Gfun X Y ρ (((2 : ℝ) : ℂ) + t * I) := by
    intro t
    have hw0 : ((2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    rw [Gfun_eq_LSeries X Y hρ hρne hw0 (by simp; linarith)]
  simp_rw [hright]
  have hhol : HolomorphicOn (Gfun X Y ρ) (Icc (1 / 2 - ρ.re) 2 ×ℂ univ) := by
    intro w hw
    rw [mem_reProdIm] at hw
    exact (differentiableAt_Gfun X hY0 ρ (by linarith [hw.1.1])).differentiableWithinAt
  have hshift := SmoothPerron.verticalIntegral_shift (G := Gfun X Y ρ) (σ' := 1 / 2 - ρ.re) (σ := 2)
    (by linarith) hhol (Gfun_line_integrable X hY0 hC hρ2 (by linarith) le_rfl)
    (Gfun_line_integrable X hY0 hC hρ2 le_rfl (by linarith)) (Gfun_decay X hC)
  simp only [VerticalIntegral] at hshift
  congr 1
  exact smul_right_injective ℂ I_ne_zero hshift

/-! ### The three pieces -/

/-- The `n`-th term of the identity: `a_n n^{−ρ}(n/Y + ρ − 1)e^{−n/Y}`. -/
def cn (X : ℕ) (Y : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  aX X n * (n : ℂ) ^ (-ρ) * ((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1)) * (Real.exp (-((n : ℝ) / Y)) : ℂ)

/-- `b_j = a_j e^{−j/Y}`. -/
def b1 (X : ℕ) (Y : ℝ) (j : ℕ) : ℂ := aX X j * (Real.exp (-((j : ℝ) / Y)) : ℂ)

/-- `b_j = a_j (j/Y) e^{−j/Y}`. -/
def b2 (X : ℕ) (Y : ℝ) (j : ℕ) : ℂ := aX X j * ((((j : ℝ) / Y) * Real.exp (-((j : ℝ) / Y)) : ℝ) : ℂ)

/-- The Dirichlet polynomial `Σ_{X<j≤XN} b_j j^{−β−iγ}`. -/
def Pv (b : ℕ → ℂ) (X N : ℕ) (β γ : ℝ) : ℂ :=
  DirMean.dp (Finset.Ioc X (X * N)) (fun j => b j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

theorem exp_neg_div_le_one {Y : ℝ} (hY : 0 < Y) (j : ℕ) : Real.exp (-((j : ℝ) / Y)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by have := div_nonneg (Nat.cast_nonneg (α := ℝ) j) hY.le; linarith)

theorem norm_b1_le (X : ℕ) {Y : ℝ} (hY : 0 < Y) (j : ℕ) : ‖b1 X Y j‖ ≤ (j.divisors.card : ℝ) := by
  unfold b1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖aX X j‖ * Real.exp (-((j : ℝ) / Y)) ≤ (j.divisors.card : ℝ) * 1 :=
        mul_le_mul (norm_aX_le X j) (exp_neg_div_le_one hY j) (Real.exp_pos _).le (by positivity)
    _ = (j.divisors.card : ℝ) := mul_one _

theorem norm_b2_le (X : ℕ) {Y : ℝ} (hY : 0 < Y) (j : ℕ) : ‖b2 X Y j‖ ≤ (j.divisors.card : ℝ) := by
  unfold b2
  have hx : 0 ≤ (j : ℝ) / Y := div_nonneg (Nat.cast_nonneg j) hY.le
  have h1 : (j : ℝ) / Y * Real.exp (-((j : ℝ) / Y)) ≤ 1 := by
    have := pow_mul_exp_neg_le 1 hx
    simpa using this
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖aX X j‖ * ((j : ℝ) / Y * Real.exp (-((j : ℝ) / Y))) ≤ (j.divisors.card : ℝ) * 1 :=
        mul_le_mul (norm_aX_le X j) h1 (by positivity) (by positivity)
    _ = (j.divisors.card : ℝ) := mul_one _

theorem cn_zero (X : ℕ) (Y : ℝ) (ρ : ℂ) : cn X Y ρ 0 = 0 := by simp [cn, aX_zero]

theorem cn_one {X : ℕ} (hX : 1 ≤ X) (Y : ℝ) (ρ : ℂ) :
    cn X Y ρ 1 = (((1 / Y : ℝ) : ℂ) + (ρ - 1)) * (Real.exp (-(1 / Y)) : ℂ) := by
  simp [cn, aX_one hX]

theorem cn_eq_zero {X n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ X) (Y : ℝ) (ρ : ℂ) : cn X Y ρ n = 0 := by
  simp [cn, aX_eq_zero h2 hn]

/-- `|c_n| ≤ n(n/Y + |ρ − 1|)e^{−n/Y}` for `Re ρ ≥ 0`. -/
theorem norm_cn_le (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re) (n : ℕ) :
    ‖cn X Y ρ n‖ ≤ n * ((n : ℝ) / Y + ‖ρ - 1‖) * Real.exp (-((n : ℝ) / Y)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cn_zero]
  unfold cn
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_natCast_cpow_of_pos hn]
  have h1 : (n : ℝ) ^ (-ρ).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
  have h2 : ‖((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1))‖ ≤ (n : ℝ) / Y + ‖ρ - 1‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hY.le)]
  calc ‖aX X n‖ * (n : ℝ) ^ (-ρ).re * ‖((((n : ℝ) / Y : ℝ) : ℂ) + (ρ - 1))‖ * Real.exp (-((n : ℝ) / Y))
      ≤ n * 1 * ((n : ℝ) / Y + ‖ρ - 1‖) * Real.exp (-((n : ℝ) / Y)) := by
        gcongr
        exact norm_aX_le_self X n
    _ = n * ((n : ℝ) / Y + ‖ρ - 1‖) * Real.exp (-((n : ℝ) / Y)) := by ring

theorem summable_cn (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re) : Summable (cn X Y ρ) := by
  have hr : 0 < 1 / Y := by positivity
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hr
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  refine Summable.of_norm_bounded ((h2.mul_left (1 / Y)).add (h1.mul_left ‖ρ - 1‖)) fun n => ?_
  refine (norm_cn_le X hY hρ n).trans (le_of_eq ?_)
  have e : -(1 / Y) * (n : ℝ) = -((n : ℝ) / Y) := by ring
  simp only [e]
  ring

/-! ### The tail -/

/-- **The tail beyond `M ≥ 22 Y log Y`** is at most `1/16`, for `Y ≥ 8`, `2 ≤ U ≤ Y` and `|ρ − 1| ≤ 3U`. -/
theorem tail_le (X : ℕ) {Y U : ℝ} (hY : 8 ≤ Y) (hU : 2 ≤ U) (hUY : U ≤ Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re)
    (hρ1 : ‖ρ - 1‖ ≤ 2 * U + 1) {M : ℕ} (hM : 22 * Y * Real.log Y ≤ M) :
    ‖∑' n : ℕ, if M < n then cn X Y ρ n else 0‖ ≤ 1 / 16 := by
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  -- `e^{−M/(2Y)} ≤ Y^{−11}`
  have hexp : Real.exp ((M : ℝ) / (2 * Y)) ≥ Y ^ 11 := by
    have h1 : 11 * Real.log Y ≤ (M : ℝ) / (2 * Y) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc Y ^ 11 = Real.exp (((11 : ℕ) : ℝ) * Real.log Y) := by
          rw [Real.exp_nat_mul, Real.exp_log hY0]
      _ ≤ Real.exp ((M : ℝ) / (2 * Y)) := Real.exp_le_exp.2 (by push_cast; linarith)
  set K : ℝ := 1152 * U * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ n : ℕ, ‖if M < n then cn X Y ρ n else 0‖ ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n
    split_ifs with hn
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn.le
      refine (norm_cn_le X hY0 hρ n).trans ?_
      -- `n(n/Y + |ρ − 1|) ≤ 3U n²`
      have hA : (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) ≤ 3 * U * (n : ℝ) ^ 2 := by
        have h1 : (n : ℝ) / Y ≤ n := div_le_self hn0.le (by linarith)
        have h2 : (n : ℝ) / Y + ‖ρ - 1‖ ≤ n + (2 * U + 1) := by linarith
        have h3 : (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) ≤ n * (n + (2 * U + 1)) :=
          mul_le_mul_of_nonneg_left h2 hn0.le
        have h4 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have h5 : (2 * U + 1) * (n : ℝ) ≤ (2 * U + 1) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        have h6 : (2 * U + 2) * (n : ℝ) ^ 2 ≤ 3 * U * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith
      -- `n² e^{−n/Y} ≤ 384 Y⁴ e^{−M/(2Y)} / n²`
      have hB : (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
          ≤ 384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) := by
        have hy : 0 ≤ (n : ℝ) / (2 * Y) := by positivity
        have h4 := pow_mul_exp_neg_le 4 hy
        have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
        rw [hf] at h4
        have hsplit : Real.exp (-((n : ℝ) / Y))
            = Real.exp (-((n : ℝ) / (2 * Y))) * Real.exp (-((n : ℝ) / (2 * Y))) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        have hmono : Real.exp (-((n : ℝ) / (2 * Y))) ≤ Real.exp (-((M : ℝ) / (2 * Y))) :=
          Real.exp_le_exp.2 (by
            have : (M : ℝ) / (2 * Y) ≤ (n : ℝ) / (2 * Y) := by gcongr
            linarith)
        have e4 : (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = 16 * Y ^ 4 * ((n : ℝ) / (2 * Y)) ^ 4 := by
          field_simp; ring
        calc (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
            = 16 * Y ^ 4 * (((n : ℝ) / (2 * Y)) ^ 4 * Real.exp (-((n : ℝ) / (2 * Y))))
              * Real.exp (-((n : ℝ) / (2 * Y))) := by rw [hsplit]; nlinarith [e4]
          _ ≤ 16 * Y ^ 4 * 24 * Real.exp (-((M : ℝ) / (2 * Y))) := by gcongr
          _ = 384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) := by ring
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      rw [mul_one_div, le_div_iff₀ hn2]
      calc (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
          ≤ 3 * U * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2 := by gcongr
        _ = 3 * U * ((n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2) := by ring
        _ ≤ 3 * U * (384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y)))) := by gcongr
        _ = K := by rw [hK]; ring
    · rw [norm_zero]; positivity
  have hsum : HasSum (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) (K * (π ^ 2 / 6)) :=
    hasSum_zeta_two.mul_left K
  refine (tsum_of_norm_bounded hsum hpt).trans ?_
  -- `K π²/6 ≤ 2K ≤ 2304 U Y⁴ Y^{−11} ≤ 2304 / Y⁶ ≤ 1/16`
  have hpi : π ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  have hY11 : 0 < Y ^ 11 := by positivity
  have hKle : K ≤ 1152 * U * Y ^ 4 / Y ^ 11 := by
    rw [hK, Real.exp_neg, ← div_eq_mul_inv]
    gcongr
  have hfin : 2 * (1152 * U * Y ^ 4 / Y ^ 11) ≤ 1 / 16 := by
    rw [mul_div_assoc', div_le_div_iff₀ hY11 (by norm_num)]
    have hY6 : (8 : ℝ) ^ 6 ≤ Y ^ 6 := by gcongr
    have hUY' : U * Y ^ 4 ≤ Y ^ 5 := by
      calc U * Y ^ 4 ≤ Y * Y ^ 4 := by gcongr
        _ = Y ^ 5 := by ring
    have e : Y ^ 11 = Y ^ 6 * Y ^ 5 := by ring
    rw [e]
    have hY5 : 0 ≤ Y ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hY6 hY5]
  calc K * (π ^ 2 / 6) ≤ K * 2 := by gcongr
    _ = 2 * K := by ring
    _ ≤ 2 * (1152 * U * Y ^ 4 / Y ^ 11) := by gcongr
    _ ≤ 1 / 16 := hfin

/-! ### The split and the trichotomy -/

/-- `Σ_{X<n≤XN} c_n = P₂ + (ρ − 1)P₁` at `ρ = β + iγ`. -/
theorem sum_cn_eq (X N : ℕ) (Y β γ : ℝ) :
    ∑ n ∈ Finset.Ioc X (X * N), cn X Y ((β : ℂ) + γ * I) n
      = Pv (b2 X Y) X N β γ + ((β : ℂ) + γ * I - 1) * Pv (b1 X Y) X N β γ := by
  unfold Pv DirMean.dp
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
  rw [cn, natCast_cpow_neg n hn0 β γ]
  simp only [b1, b2]
  push_cast
  ring

/-- **The split**: `Σ' c_n = c₁ + Σ_{X<n≤M} c_n + Σ'_{n>M} c_n` for `1 ≤ X ≤ M`. -/
theorem tsum_cn_split {X M : ℕ} (hX : 1 ≤ X) (hXM : X ≤ M) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ∑' n, cn X Y ρ n = cn X Y ρ 1 + ∑ n ∈ Finset.Ioc X M, cn X Y ρ n
      + ∑' n : ℕ, if M < n then cn X Y ρ n else 0 := by
  have hs := summable_cn X hY hρ
  set f := cn X Y ρ with hf
  have hpt : ∀ n, f n = ((if n = 1 then f 1 else 0) + (if n ∈ Finset.Ioc X M then f n else 0))
      + (if M < n then f n else 0) := by
    intro n
    rcases Nat.lt_or_ge M n with h | h
    · have h1 : n ≠ 1 := by omega
      have h2 : n ∉ Finset.Ioc X M := fun hm => by have := (Finset.mem_Ioc.1 hm).2; omega
      simp [h1, h2, h]
    · have h3 : ¬ M < n := by omega
      rcases Nat.lt_or_ge X n with hXn | hXn
      · have h1 : n ≠ 1 := by omega
        have h2 : n ∈ Finset.Ioc X M := Finset.mem_Ioc.2 ⟨hXn, h⟩
        simp [h1, h2, h3]
      · have h2 : n ∉ Finset.Ioc X M := fun hm => by have := (Finset.mem_Ioc.1 hm).1; omega
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · interval_cases n
          · simp [hf, cn_zero]
          · simp [h2, h3]
        · have h1 : n ≠ 1 := by omega
          simp [h1, h2, h3, hf, cn_eq_zero hn2 hXn]
  have hs1 : Summable fun n : ℕ => if n = 1 then f 1 else 0 :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
  have hs2 : Summable fun n : ℕ => if n ∈ Finset.Ioc X M then f n else 0 :=
    summable_of_ne_finset_zero (s := Finset.Ioc X M) fun n hn => by simp [hn]
  have hs3 : Summable fun n : ℕ => if M < n then f n else 0 := by
    refine Summable.of_norm_bounded hs.norm fun n => ?_
    split_ifs <;> simp
  calc ∑' n, f n = ∑' n, (((if n = 1 then f 1 else 0) + (if n ∈ Finset.Ioc X M then f n else 0))
        + (if M < n then f n else 0)) := tsum_congr hpt
    _ = (∑' n : ℕ, if n = 1 then f 1 else 0) + (∑' n : ℕ, if n ∈ Finset.Ioc X M then f n else 0)
        + ∑' n : ℕ, if M < n then f n else 0 := by
        rw [Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2]
    _ = f 1 + ∑ n ∈ Finset.Ioc X M, f n + ∑' n : ℕ, if M < n then f n else 0 := by
        congr 2
        · exact tsum_ite_eq 1 (fun _ : ℕ => f 1)
        · rw [tsum_eq_sum (s := Finset.Ioc X M) fun n hn => by simp [hn]]
          exact Finset.sum_congr rfl fun n hn => by simp [hn]

/-- The right side of the identity. -/
def Iv (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ := (1 / (2 * π) : ℂ) * ∫ v : ℝ, Gfun X Y ρ (((1 / 2 - ρ.re : ℝ) : ℂ) + v * I)

/-- **The trichotomy at a zero.** Let `ρ = β + iγ` be a zero of `ζ` with `½ < β < 1` and `U ≤ |γ| ≤ 2U`, and let
`8 ≤ Y`, `2 ≤ U ≤ Y`, `1 ≤ X`, `22 Y log Y ≤ XN`. Then `|P₁(ρ)| ≥ ¼`, or `|P₂(ρ)| ≥ ¼`, or `|I(ρ)| ≥ U/4`. -/
theorem trichotomy {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) {Y U : ℝ} (hY : 8 ≤ Y) (hU : 2 ≤ U) (hUY : U ≤ Y)
    (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ)) {β γ : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (hγ1 : U ≤ |γ|) (hγ2 : |γ| ≤ 2 * U) (hz : riemannZeta ((β : ℂ) + γ * I) = 0) :
    1 / 4 ≤ ‖Pv (b1 X Y) X N β γ‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N β γ‖ ∨ U / 4 ≤ ‖Iv X Y ((β : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (β : ℂ) + γ * I with hρdef
  have hY0 : 0 < Y := by linarith
  have hρre : ρ.re = β := by simp [hρdef]
  have hρim : ρ.im = γ := by simp [hρdef]
  have hXM : X ≤ X * N := Nat.le_mul_of_pos_right X hN
  have hid := detect_identity X (Y := Y) (by linarith) hz (by rw [hρre]; exact hβ1) (by rw [hρre]; exact hβ2)
  have hsplit := tsum_cn_split hX hXM hY0 (ρ := ρ) (by rw [hρre]; linarith)
  have hsum := sum_cn_eq X N Y β γ
  rw [← hρdef] at hsum
  -- `c₁ + P₂ + (ρ − 1)P₁ + T = I`
  set T := ∑' n : ℕ, if X * N < n then cn X Y ρ n else 0 with hT
  set P1 := Pv (b1 X Y) X N β γ
  set P2 := Pv (b2 X Y) X N β γ
  set II := Iv X Y ρ with hII
  have heq : cn X Y ρ 1 + (P2 + (ρ - 1) * P1) + T = II := by
    rw [← hsum, ← hsplit]; exact hid
  have hR1 : |γ| ≤ ‖ρ - 1‖ := by
    have := Complex.abs_im_le_norm (ρ - 1)
    simpa [hρim] using this
  have hR2 : ‖ρ - 1‖ ≤ 2 * U + 1 := by
    calc ‖ρ - 1‖ ≤ |(ρ - 1).re| + |(ρ - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |β - 1| + |γ| := by simp [hρre, hρim]
      _ ≤ 2 * U + 1 := by rw [abs_of_neg (by linarith)]; linarith
  have hT16 : ‖T‖ ≤ 1 / 16 := tail_le X hY hU hUY (by rw [hρre]; linarith) hR2 hM
  set R := ‖ρ - 1‖ with hRdef
  have hRU : U ≤ R := hγ1.trans hR1
  -- `|c₁| ≥ (105/128) R`
  have hc1 : (105 / 128) * R ≤ ‖cn X Y ρ 1‖ := by
    rw [cn_one hX, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : R - 1 / Y ≤ ‖(((1 / Y : ℝ) : ℂ) + (ρ - 1))‖ := by
      have := norm_sub_norm_le (ρ - 1) (-(((1 / Y : ℝ) : ℂ)))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), sub_neg_eq_add,
        add_comm] at this
      linarith
    have h2 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / Y)) := by
      have := Real.add_one_le_exp (-(1 / Y))
      have : 1 / Y ≤ 1 / 8 := by gcongr
      linarith
    have h3 : (15 / 16) * R ≤ R - 1 / Y := by
      have : 1 / Y ≤ 1 / 8 := by gcongr
      linarith
    calc (105 / 128) * R = ((15 / 16) * R) * (7 / 8) := by ring
      _ ≤ ‖(((1 / Y : ℝ) : ℂ) + (ρ - 1))‖ * Real.exp (-(1 / Y)) := by
          gcongr
          linarith
  -- `|c₁| ≤ |P₂| + R|P₁| + |T| + |I|`
  have hle : ‖cn X Y ρ 1‖ ≤ ‖P2‖ + R * ‖P1‖ + ‖T‖ + ‖II‖ := by
    have e : cn X Y ρ 1 = II - P2 - (ρ - 1) * P1 - T := by rw [← heq]; ring
    rw [e]
    calc ‖II - P2 - (ρ - 1) * P1 - T‖ ≤ ‖II‖ + ‖P2‖ + ‖(ρ - 1) * P1‖ + ‖T‖ := by
          refine (norm_sub_le _ _).trans ?_
          have h1 := norm_sub_le (II - P2) ((ρ - 1) * P1)
          have h2 := norm_sub_le II P2
          linarith
      _ = ‖P2‖ + R * ‖P1‖ + ‖T‖ + ‖II‖ := by rw [norm_mul]; ring
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hP1R : R * ‖P1‖ ≤ R * (1 / 4) := mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
  nlinarith

end InghamDensity

#print axioms InghamDensity.norm_Gamma_poly_le
#print axioms InghamDensity.norm_Gamma_strip_le
#print axioms InghamDensity.norm_Gamma_exp_le
#print axioms InghamDensity.integral_kernel_line
#print axioms InghamDensity.LSeries_aX
#print axioms InghamDensity.sum_side
#print axioms InghamDensity.Gfun_strip_bound
#print axioms InghamDensity.detect_identity
#print axioms InghamDensity.tail_le
#print axioms InghamDensity.trichotomy
