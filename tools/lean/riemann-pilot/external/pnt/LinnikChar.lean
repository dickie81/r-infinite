/-
# Round 520, part 1: the bound for one character with the weight `e^{−n/x}`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `χ ≠ 1` be a Dirichlet character mod `q`, `S_χ(x) = Σ_n χ(n)Λ(n)e^{−n/x}` (`Sx`),
`½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`, `T ≥ 0` and `x ≥ 1`. If `L(·, χ)` has no zero in `Re s > θ`, `|Im s| < T + 1`, then
`|S_χ(x)| ≤ M log(q + 2)(x^{θ+δ} + 2x^{11/12+δ}e^{−T/2})`, with `M = Mc(θ, θ + δ) + Mc(11/12, 11/12 + δ)` depending on
`θ` and `δ` only (`norm_Sx_le`). Off that region the zeros are excluded by round 495's half-plane
`Eis.LFunction_ne_zero_of_re_gt`.

* `perron_exp`: `Σ_n a_n e^{−n/x} = (1/2π) ∫ L(a, c + it)Γ(c + it)x^{c+it} dt` for `a_0 = 0`, `½ ≤ c ≤ 3`, `x > 0`
  and `L(a, c)` absolutely convergent: round 518's Mellin inversion for `e^{−y}` (`InghamDensity.integral_Gamma_line`)
  at each `y = n/x`, summed with `integral_tsum_of_summable_integral_norm`.
* `logDeriv_LFunction_le`: `|L′/L(σ + it, χ)| ≤ KL θ θ'(log(q + 2) + log(|t| + 4))` for `σ ≥ θ'` when `L(·, χ)` has no
  zero in the disc of radius `3/2 − θ` about `3/2 + it`: `LogDerivDisc.logDeriv_le_ball` with `c = 3(q + 1)`
  (`LFunction_growth`, from round 254's `PsiOmega.norm_LFunction_leC`), `A = ζ(3/2)` and `C₀ = −ζ′/ζ(3/2)`
  (`ChiUniform.LFunction_ctr_inv_le`, `ChiUniform.logDeriv_LFunction_right`).
* `norm_pf_le`: there the Perron integrand `−L′/L(s, χ)Γ(s)x^s` (`pf`) is at most
  `Mc θ θ' log(q + 2)x^σ e^{−|t|/2}/(1 + t²)` on `θ' ≤ σ ≤ 3`, with `InghamDensity.norm_Gamma_exp_le`.
* `Sx_eq_integral`, `integral_pf_shift`: `S_χ(x)` is the integral on `Re s = 2`, and the line moves to
  `Re s = 11/12 + δ` (`SmoothPerron.verticalIntegral_shift`), where the half-plane gives the bound at every `t`
  (`norm_pf_global`).
* `norm_Sx_le`: below height `T` the line moves across the rectangle `[θ + δ, 11/12 + δ] × [−T, T]`
  (`HolomorphicOn.vanishesOnRectangle`). The vertical side at `θ + δ` costs `x^{θ+δ}`; the horizontal sides and the
  tails `|t| ≥ T` cost `x^{11/12+δ}e^{−T/2}`.
-/
import InghamDetect
import ChiUniform

open Complex Set Real Filter Topology MeasureTheory
open scoped Interval

noncomputable section

namespace Linnik

open LogDerivDisc ChiUniform DirichletCharacter InghamDensity

variable {q : ℕ} [NeZero q]

/-! ### Perron's formula for the weight `e^{−n/x}` -/

/-- `t ↦ y^{−(c+it)} Γ(c + it)` is integrable for `y > 0` and `½ ≤ c ≤ 3`. -/
theorem kernelG_integrable {c y : ℝ} (hc : 1 / 2 ≤ c) (hc3 : c ≤ 3) (hy : 0 < y) :
    Integrable fun t : ℝ => (y : ℂ) ^ (-((c : ℂ) + t * I)) * Complex.Gamma (c + t * I) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  refine Integrable.mono' ((Gamma_line_integrable hc hc3).norm.const_mul (y ^ (-c))) ?_
    (Eventually.of_forall fun t => ?_)
  · exact (Continuous.mul (Continuous.const_cpow (by fun_prop) (Or.inl hy'))
      (continuous_Gamma_line (by linarith))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : (-((c : ℂ) + t * I)).re = -c := by simp
    rw [hre]

/-- **Perron's formula for `e^{−n/x}`.** For `a 0 = 0`, `½ ≤ c ≤ 3`, `x > 0` and `L(a, c)` absolutely
convergent, `Σ_n a_n e^{−n/x} = (1/2π) ∫ L(a, c + it) Γ(c + it) x^{c+it} dt`: Mellin inversion for `e^{−y}`
(`InghamDensity.integral_Gamma_line`) at each `y = n/x`, summed with `integral_tsum_of_summable_integral_norm`. -/
theorem perron_exp {a : ℕ → ℂ} (ha0 : a 0 = 0) {c x : ℝ} (hc : 1 / 2 ≤ c) (hc3 : c ≤ 3) (hx : 0 < x)
    (ha : LSeriesSummable a c) :
    ∑' n : ℕ, a n * (Real.exp (-((n : ℝ) / x)) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * Complex.Gamma ((c : ℂ) + t * I) *
        (x : ℂ) ^ ((c : ℂ) + t * I) := by
  let F : ℕ → ℝ → ℂ := fun n t => LSeries.term a ((c : ℂ) + t * I) n * Complex.Gamma ((c : ℂ) + t * I) *
    (x : ℂ) ^ ((c : ℂ) + t * I)
  have hterm : ∀ n (t : ℝ), ‖LSeries.term a ((c : ℂ) + t * I) n‖ = ‖LSeries.term a c n‖ := by
    intro n t
    simp only [LSeries.norm_term_eq]
    congr 3
    simp
  have hxc : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := fun t => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hnormF : ∀ n t, ‖F n t‖ = ‖LSeries.term a c n‖ * x ^ c * ‖Complex.Gamma ((c : ℂ) + t * I)‖ := by
    intro n t
    simp only [F, norm_mul, hterm, hxc]
    ring
  have hFk : ∀ n : ℕ, n ≠ 0 → ∀ t : ℝ, F n t = a n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
      Complex.Gamma ((c : ℂ) + t * I)) := by
    intro n hn t
    simp only [F, LSeries.term_of_ne_zero hn]
    have := SmoothPerron.div_cpow_mul_cpow hn hx (a n) (Complex.Gamma ((c : ℂ) + t * I)) ((c : ℂ) + t * I)
    rw [this, smul_eq_mul]
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [F, LSeries.term_zero, zero_mul]; exact integrable_zero _ _ _
    · have hy : (0 : ℝ) < (n : ℝ) / x := div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) hx
      refine ((kernelG_integrable hc hc3 hy).const_mul (a n)).congr (Eventually.of_forall fun t => ?_)
      rw [hFk n hn t]
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    exact (ha.norm.mul_right (x ^ c)).mul_right _
  have hsum_pt : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * Complex.Gamma ((c : ℂ) + t * I) *
      (x : ℂ) ^ ((c : ℂ) + t * I) = ∑' n, F n t := by
    intro t
    simp only [F, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
  have hint_n : ∀ n : ℕ, (1 / (2 * π) : ℂ) * ∫ t, F n t = a n * (Real.exp (-((n : ℝ) / x)) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha0]
    · have hy : (0 : ℝ) < (n : ℝ) / x := div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) hx
      have hk := integral_Gamma_line hc hc3 hy
      simp_rw [hFk n hn]
      rw [integral_const_mul, ← mul_assoc, mul_comm (1 / (2 * π) : ℂ), mul_assoc, hk]
  calc ∑' n : ℕ, a n * (Real.exp (-((n : ℝ) / x)) : ℂ)
      = ∑' n, (1 / (2 * π) : ℂ) * ∫ t, F n t := by congr 1; funext n; exact (hint_n n).symm
    _ = (1 / (2 * π) : ℂ) * ∑' n, ∫ t, F n t := by rw [tsum_mul_left]
    _ = (1 / (2 * π) : ℂ) * ∫ t, ∑' n, F n t := by rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = _ := by congr 1; congr 1; funext t; exact (hsum_pt t).symm

/-! ### `L′/L(·, χ)` where `L(·, χ)` has no zero in one disc -/

/-- `‖L(s, χ)‖ ≤ 3(q + 1)(|Im s| + 2)` on `½ ≤ Re s ≤ 3`, for `χ ≠ 1` (round 254's `norm_LFunction_leC`). -/
theorem LFunction_growth {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (h1 : 1 / 2 ≤ s.re)
    (h3 : s.re ≤ 3) : ‖LFunction χ s‖ ≤ 3 * (q + 1) * (|s.im| + 2) := by
  have hre : 0 < s.re := by linarith
  have hn : ‖s‖ ≤ 3 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 3 + |s.im| := by rw [abs_of_pos hre]; linarith
  have hq : (0 : ℝ) ≤ q + 1 := by positivity
  calc ‖LFunction χ s‖ ≤ (q + 1) * ‖s‖ / s.re := PsiOmega.norm_LFunction_leC hχ hre
    _ ≤ (q + 1) * (3 + |s.im|) / (1 / 2) := by gcongr
    _ ≤ 3 * (q + 1) * (|s.im| + 2) := by
        rw [div_le_iff₀ (by norm_num)]
        have := mul_nonneg hq (abs_nonneg s.im)
        nlinarith

/-- The constant of `logDeriv_LFunction_le`: `Kld θ θ'(1 + log(2 + 6ζ(3/2))) − ζ′/ζ(3/2)`. -/
def KL (θ θ' : ℝ) : ℝ := Kld θ θ' * (1 + Real.log (2 + 6 * zeta32)) + logDerivZeta32

lemma KL_pos {θ θ' : ℝ} (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) : 0 < KL θ θ' := by
  have hK := Kld_pos hθθ' hθ'32
  have h1 : 0 ≤ Real.log (2 + 6 * zeta32) := Real.log_nonneg (by linarith [zeta32_nonneg])
  have := logDerivZeta32_nonneg
  unfold KL; positivity

lemma one_le_log_add_two (q : ℕ) [NeZero q] : 1 ≤ Real.log (q + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have h3 := one_lt_log_three
  have : Real.log 3 ≤ Real.log (q + 2) := Real.log_le_log (by norm_num) (by linarith)
  linarith

/-- **`L′/L(·, χ)` where `L(·, χ)` has no zero in one disc.** For `χ ≠ 1` mod `q`, `½ ≤ θ < θ' < 3/2` and
`σ ≥ θ'`: if `L(·, χ)` has no zero in the disc of radius `3/2 − θ` about `3/2 + it`, then
`‖L′/L(σ + it, χ)‖ ≤ KL θ θ' (log(q + 2) + log(|t| + 4))`. -/
theorem logDeriv_LFunction_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ θ' σ t : ℝ} (hθ : 1 / 2 ≤ θ)
    (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) (hσ : θ' ≤ σ)
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), LFunction χ s ≠ 0) :
    ‖deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)‖ ≤
      KL θ θ' * (Real.log (q + 2) + Real.log (|t| + 4)) := by
  have hz0 := zeta32_nonneg
  have hd0 := logDerivZeta32_nonneg
  have hK := Kld_pos hθθ' hθ'32
  have hc0 : (0 : ℝ) ≤ 3 * (q + 1) := by positivity
  have h := LogDerivDisc.logDeriv_le_ball (by linarith) hθθ' hθ'32 (differentiable_LFunction hχ) hc0 hz0
    (fun s hs1 hs3 => LFunction_growth hχ (by linarith) hs3) (fun s hs => logDeriv_LFunction_right χ hs) hσ
    (LFunction_ctr_inv_le χ t) hzf
  have hlq := one_le_log_add_two q
  have hl4 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hc' : 0 ≤ Real.log (2 + 6 * zeta32) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 + 2 * (3 * (q + 1)) * zeta32) ≤ Real.log (q + 2) + Real.log (2 + 6 * zeta32) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  calc ‖deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)‖
      ≤ Kld θ θ' * (Real.log (2 + 2 * (3 * (q + 1)) * zeta32) + Real.log (|t| + 4)) + logDerivZeta32 := h
    _ ≤ Kld θ θ' * (Real.log (q + 2) + Real.log (2 + 6 * zeta32) + Real.log (|t| + 4)) + logDerivZeta32 := by
        gcongr
    _ ≤ KL θ θ' * (Real.log (q + 2) + Real.log (|t| + 4)) := by
        unfold KL
        have e1 : Kld θ θ' * Real.log (2 + 6 * zeta32) ≤
            Kld θ θ' * Real.log (2 + 6 * zeta32) * Real.log (q + 2) := le_mul_of_one_le_right (by positivity) hlq
        have e2 : logDerivZeta32 ≤ logDerivZeta32 * Real.log (q + 2) := le_mul_of_one_le_right hd0 hlq
        have e3 : 0 ≤ Kld θ θ' * Real.log (2 + 6 * zeta32) * Real.log (|t| + 4) := by positivity
        have e4 : 0 ≤ logDerivZeta32 * Real.log (|t| + 4) := by positivity
        nlinarith

/-! ### The bound for one character -/

/-- `(a + log(|t| + 4))e^{−|t|} ≤ e^{−|t|/2} · 48e^{1/2}(a + 3)/(1 + t²)` for `a ≥ 0`: `log y ≤ y − 1`,
`1 + t² ≤ (1 + |t|)²` and `y³e^{−y} ≤ 3!` at `y = (1 + |t|)/2`. -/
lemma log_exp_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (a + Real.log (|t| + 4)) * Real.exp (-|t|) ≤
      Real.exp (-|t| / 2) * (48 * Real.exp (1 / 2) * (a + 3) / (1 + t ^ 2)) := by
  have ht := abs_nonneg t
  have hlog : Real.log (|t| + 4) ≤ |t| + 3 := by
    have := Real.log_le_sub_one_of_pos (show 0 < |t| + 4 by linarith); linarith
  have hl0 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith)
  have h1 : a + Real.log (|t| + 4) ≤ (a + 3) * (1 + |t|) := by nlinarith
  have h2 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t]
  have hy : 0 ≤ (1 + |t|) / 2 := by positivity
  have h3' := pow_mul_exp_neg_le 3 hy
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h3'
  have h3 : (1 + |t|) ^ 3 * Real.exp (-|t| / 2) ≤ 48 * Real.exp (1 / 2) := by
    have e : Real.exp (-|t| / 2) = Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    calc (1 + |t|) ^ 3 * (Real.exp (-((1 + |t|) / 2)) * Real.exp (1 / 2))
        = 8 * (((1 + |t|) / 2) ^ 3 * Real.exp (-((1 + |t|) / 2))) * Real.exp (1 / 2) := by ring
      _ ≤ 8 * 6 * Real.exp (1 / 2) := by gcongr
      _ = 48 * Real.exp (1 / 2) := by ring
  have hsplit : Real.exp (-|t|) = Real.exp (-|t| / 2) * Real.exp (-|t| / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have key : (a + Real.log (|t| + 4)) * Real.exp (-|t| / 2) ≤
      48 * Real.exp (1 / 2) * (a + 3) / (1 + t ^ 2) := by
    rw [le_div_iff₀ hpos]
    calc (a + Real.log (|t| + 4)) * Real.exp (-|t| / 2) * (1 + t ^ 2)
        ≤ ((a + 3) * (1 + |t|)) * Real.exp (-|t| / 2) * (1 + |t|) ^ 2 := by gcongr
      _ = (a + 3) * ((1 + |t|) ^ 3 * Real.exp (-|t| / 2)) := by ring
      _ ≤ (a + 3) * (48 * Real.exp (1 / 2)) := by gcongr
      _ = 48 * Real.exp (1 / 2) * (a + 3) := by ring
  calc (a + Real.log (|t| + 4)) * Real.exp (-|t|)
      = Real.exp (-|t| / 2) * ((a + Real.log (|t| + 4)) * Real.exp (-|t| / 2)) := by rw [hsplit]; ring
    _ ≤ Real.exp (-|t| / 2) * (48 * Real.exp (1 / 2) * (a + 3) / (1 + t ^ 2)) := by gcongr

/-- The Perron integrand `−L′/L(s, χ) Γ(s) x^s`. -/
def pf (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * Complex.Gamma s * (x : ℂ) ^ s

theorem differentiableAt_pf {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : 0 < s.re) (hL : LFunction χ s ≠ 0) : DifferentiableAt ℂ (pf χ x) s := by
  have hF := differentiable_LFunction hχ
  have hdF : DifferentiableAt ℂ (deriv (LFunction χ)) s := (hF.analyticAt s).deriv.differentiableAt
  have hG : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma _ fun m h => ?_
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s := differentiableAt_id.const_cpow (Or.inl hx')
  exact (((hdF.div (hF s) hL).neg).mul hG).mul hc

/-- The constant of `norm_pf_le`. -/
def Mc (θ θ' : ℝ) : ℝ := 192 * Real.exp (1 / 2) * KE * KL θ θ'

lemma Mc_pos {θ θ' : ℝ} (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) : 0 < Mc θ θ' := by
  have := KL_pos hθθ' hθ'32
  have := KE_pos
  unfold Mc; positivity

/-- **The integrand where `L(·, χ)` has no zero in one disc**: for `χ ≠ 1`, `½ ≤ θ < θ' < 3/2`,
`θ' ≤ σ ≤ 3` and `x > 0`, if `L(·, χ)` has no zero in the disc of radius `3/2 − θ` about `3/2 + it`, then
`|L′/L(σ + it, χ)Γ(σ + it)x^{σ+it}| ≤ Mc θ θ' log(q + 2) x^σ e^{−|t|/2}/(1 + t²)`. -/
theorem norm_pf_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ θ' σ t x : ℝ} (hθ : 1 / 2 ≤ θ)
    (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) (hσ : θ' ≤ σ) (hσ3 : σ ≤ 3) (hx : 0 < x)
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), LFunction χ s ≠ 0) :
    ‖pf χ x (σ + t * I)‖ ≤ Mc θ θ' * Real.log (q + 2) * x ^ σ * (Real.exp (-|t| / 2) / (1 + t ^ 2)) := by
  have hL := logDeriv_LFunction_le hχ hθ hθθ' hθ'32 hσ hzf
  have hG := norm_Gamma_exp_le (x := σ) (by linarith) hσ3 t
  have hxs : ‖(x : ℂ) ^ ((σ : ℂ) + t * I)‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hlq := one_le_log_add_two q
  have hKL := KL_pos hθθ' hθ'32
  have hKE := KE_pos
  have hle := log_exp_le (a := Real.log (q + 2)) (by linarith) t
  have hxσ : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le _
  have hE : 0 ≤ Real.exp (-|t| / 2) / (1 + t ^ 2) := by positivity
  have hl4 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hB0 : 0 ≤ KL θ θ' * (Real.log (q + 2) + Real.log (|t| + 4)) := mul_nonneg hKL.le (by linarith)
  have e : Real.exp (-|t| / 2) * (48 * Real.exp (1 / 2) * (Real.log (q + 2) + 3) / (1 + t ^ 2)) =
      48 * Real.exp (1 / 2) * (Real.log (q + 2) + 3) * (Real.exp (-|t| / 2) / (1 + t ^ 2)) := by ring
  calc ‖pf χ x (σ + t * I)‖ = ‖deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)‖ *
        ‖Complex.Gamma (σ + t * I)‖ * x ^ σ := by
        rw [pf, norm_mul, norm_mul, norm_neg, hxs]
    _ ≤ (KL θ θ' * (Real.log (q + 2) + Real.log (|t| + 4))) * (KE * Real.exp (-|t|)) * x ^ σ := by gcongr
    _ = KL θ θ' * KE * x ^ σ * ((Real.log (q + 2) + Real.log (|t| + 4)) * Real.exp (-|t|)) := by ring
    _ ≤ KL θ θ' * KE * x ^ σ *
        (Real.exp (-|t| / 2) * (48 * Real.exp (1 / 2) * (Real.log (q + 2) + 3) / (1 + t ^ 2))) := by gcongr
    _ = KL θ θ' * KE * x ^ σ *
        (48 * Real.exp (1 / 2) * (Real.log (q + 2) + 3) * (Real.exp (-|t| / 2) / (1 + t ^ 2))) := by rw [e]
    _ ≤ KL θ θ' * KE * x ^ σ *
        (48 * Real.exp (1 / 2) * (4 * Real.log (q + 2)) * (Real.exp (-|t| / 2) / (1 + t ^ 2))) := by
        gcongr; linarith
    _ = Mc θ θ' * Real.log (q + 2) * x ^ σ * (Real.exp (-|t| / 2) / (1 + t ^ 2)) := by unfold Mc; ring

/-- `S_χ(x) = Σ_n χ(n)Λ(n)e^{−n/x}`. -/
def Sx (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)

/-- **Perron for `S_χ`**: `S_χ(x) = (1/2π) ∫ −L′/L(2 + it, χ)Γ(2 + it)x^{2+it} dt`. -/
theorem Sx_eq_integral (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Sx χ x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, pf χ x (((2 : ℝ) : ℂ) + t * I) := by
  have h := perron_exp (a := fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp) (c := 2)
    (by norm_num) (by norm_num) hx (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num))
  rw [Sx, h]
  congr 2
  funext t
  rw [ChiPNT.LSeries_twist_vonMangoldt_eq_LFunction χ (by simp), pf]

/-- The disc of radius `3/2 − 11/12` about any `3/2 + it` holds no zero of `L(·, χ)`, `χ ≠ 1` (the half-plane). -/
lemma zeroFree_ball_global {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) :
    ∀ s ∈ Metric.ball (ctr t) (3 / 2 - 11 / 12), LFunction χ s ≠ 0 := fun _ hs =>
  Eis.LFunction_ne_zero_of_re_gt χ (LogDerivDisc.re_gt_of_mem_ball hs) (Or.inl hχ)

/-- The disc of radius `3/2 − θ` about `3/2 + it`, `|t| ≤ T`, holds no zero when `L(·, χ)` has none in
`Re s > θ`, `|Im s| < T + 1`. -/
lemma zeroFree_ball_local {χ : DirichletCharacter ℂ q} {θ T t : ℝ} (hθ : 1 / 2 ≤ θ) (ht : |t| ≤ T)
    (hloc : ∀ s : ℂ, θ < s.re → |s.im| < T + 1 → LFunction χ s ≠ 0) :
    ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), LFunction χ s ≠ 0 := fun s hs => by
  refine hloc s (LogDerivDisc.re_gt_of_mem_ball hs) ?_
  have h1 := LogDerivDisc.im_sub_lt_of_mem_ball hθ hs
  have h2 : |s.im| ≤ |s.im - t| + |t| := by
    have := abs_add_le (s.im - t) t; simpa using this
  linarith

lemma integrable_of_le_inv {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2)⁻¹) :
    Integrable f :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hf.aestronglyMeasurable (Eventually.of_forall hC)

lemma exp_div_le_inv (t : ℝ) : Real.exp (-|t| / 2) / (1 + t ^ 2) ≤ (1 + t ^ 2)⁻¹ := by
  rw [div_eq_mul_inv]
  have : Real.exp (-|t| / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg t])
  have : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  nlinarith

/-- The integrand is continuous on `Re s = σ ≥ 11/12 + δ`. -/
lemma continuous_pf_line {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 11 / 12 < σ) :
    Continuous fun t : ℝ => pf χ x ((σ : ℂ) + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  exact ContinuousAt.comp (g := pf χ x) (f := fun t : ℝ => (σ : ℂ) + t * I)
    (differentiableAt_pf hχ hx (by rw [hre]; linarith)
      (Eis.LFunction_ne_zero_of_re_gt χ (by rw [hre]; exact hσ) (Or.inl hχ))).continuousAt (by fun_prop)

/-- The bound on `Re s ≥ 11/12 + δ`: `|pf(σ + it)| ≤ Mc(11/12, 11/12 + δ) log(q + 2) x^σ e^{−|t|/2}/(1 + t²)`. -/
lemma norm_pf_global {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {δ σ t x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24)
    (hσ : 11 / 12 + δ ≤ σ) (hσ3 : σ ≤ 3) (hx : 0 < x) :
    ‖pf χ x (σ + t * I)‖ ≤
      Mc (11 / 12) (11 / 12 + δ) * Real.log (q + 2) * x ^ σ * (Real.exp (-|t| / 2) / (1 + t ^ 2)) :=
  norm_pf_le hχ (by norm_num) (by linarith) (by linarith) hσ hσ3 hx (zeroFree_ball_global hχ t)

/-- **The line moves from `Re s = 2` to `Re s = 11/12 + δ`** (`SmoothPerron.verticalIntegral_shift`). -/
theorem integral_pf_shift {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 24) :
    ∫ t : ℝ, pf χ x (((2 : ℝ) : ℂ) + t * I) = ∫ t : ℝ, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I) := by
  have hx0 : 0 < x := by linarith
  set M₀ : ℝ := Mc (11 / 12) (11 / 12 + δ) * Real.log (q + 2) * x ^ (2 : ℝ) with hM₀
  have hM₀0 : 0 ≤ M₀ := by
    have := Mc_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
    have := one_le_log_add_two q
    positivity
  have hb : ∀ σ ∈ Icc (11 / 12 + δ) 2, ∀ t : ℝ, ‖pf χ x (σ + t * I)‖ ≤ M₀ * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    refine (norm_pf_global hχ hδ hδ1 hσ.1 (by linarith [hσ.2]) hx0).trans ?_
    have hxσ : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have := Mc_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
    have := one_le_log_add_two q
    have hE := exp_div_le_inv t
    have hE0 : 0 ≤ Real.exp (-|t| / 2) / (1 + t ^ 2) := by positivity
    calc Mc (11 / 12) (11 / 12 + δ) * Real.log (q + 2) * x ^ σ * (Real.exp (-|t| / 2) / (1 + t ^ 2))
        ≤ Mc (11 / 12) (11 / 12 + δ) * Real.log (q + 2) * x ^ (2 : ℝ) * (1 + t ^ 2)⁻¹ := by gcongr
      _ = M₀ * (1 + t ^ 2)⁻¹ := by rw [hM₀]
  have hhol : HolomorphicOn (pf χ x) (Icc (11 / 12 + δ) 2 ×ℂ univ) := by
    intro s hs
    rw [mem_reProdIm] at hs
    exact (differentiableAt_pf hχ hx0 (by linarith [hs.1.1])
      (Eis.LFunction_ne_zero_of_re_gt χ (by linarith [hs.1.1]) (Or.inl hχ))).differentiableWithinAt
  have hint2 := integrable_of_le_inv (continuous_pf_line hχ hx0 (σ := 2) (by norm_num))
    (hb 2 ⟨by linarith, le_rfl⟩)
  have hint1 := integrable_of_le_inv (continuous_pf_line hχ hx0 (σ := 11 / 12 + δ) (by linarith))
    (hb (11 / 12 + δ) ⟨le_rfl, by linarith⟩)
  have hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ σ ∈ Icc (11 / 12 + δ) 2, ∀ y : ℝ, T₀ ≤ |y| →
      ‖pf χ x (σ + y * I)‖ ≤ η := by
    intro η hη
    refine ⟨M₀ / η + 1, fun σ hσ y hy => ?_⟩
    refine (hb σ hσ y).trans ?_
    have hpos : 0 < 1 + y ^ 2 := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have h1 : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have h2 : M₀ / η * η = M₀ := div_mul_cancel₀ _ hη.ne'
    nlinarith
  have hshift := SmoothPerron.verticalIntegral_shift (G := pf χ x) (σ' := 11 / 12 + δ) (σ := 2)
    (by linarith) hhol hint2 hint1 hdecay
  simp only [VerticalIntegral] at hshift
  exact smul_right_injective ℂ I_ne_zero hshift

/-! ### The bound for one character, below height `T` -/

/-- `‖∫_S f‖ ≤ Cπ` when `‖f(t)‖ ≤ C(1 + t²)⁻¹` on a measurable `S`. -/
lemma norm_setIntegral_le_pi {f : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t ∈ S, ‖f t‖ ≤ C * (1 + t ^ 2)⁻¹) : ‖∫ t in S, f t‖ ≤ C * π := by
  have hg : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  calc ‖∫ t in S, f t‖ ≤ ∫ t in S, C * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hg.integrableOn ((ae_restrict_iff' hS).2 (Eventually.of_forall hf))
    _ ≤ ∫ t, C * (1 + t ^ 2)⁻¹ := setIntegral_le_integral hg (Eventually.of_forall fun t => by positivity)
    _ = C * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- **The bound for one character.** Let `χ ≠ 1` mod `q`, `½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`, `T ≥ 0` and
`x ≥ 1`. If `L(·, χ)` has no zero in `Re s > θ`, `|Im s| < T + 1`, then
`|S_χ(x)| ≤ M log(q + 2)(x^{θ+δ} + 2x^{11/12+δ}e^{−T/2})`, `M = Mc(θ, θ + δ) + Mc(11/12, 11/12 + δ)`: the line
`Re s = 2` moves to `11/12 + δ`, and below height `T` across one rectangle to `θ + δ`. -/
theorem norm_Sx_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {θ δ T x : ℝ} (hθ : 1 / 2 ≤ θ)
    (hθ1 : θ ≤ 11 / 12) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hT : 0 ≤ T) (hx : 1 ≤ x)
    (hloc : ∀ s : ℂ, θ < s.re → |s.im| < T + 1 → LFunction χ s ≠ 0) :
    ‖Sx χ x‖ ≤ (Mc θ (θ + δ) + Mc (11 / 12) (11 / 12 + δ)) * Real.log (q + 2) *
      (x ^ (θ + δ) + 2 * x ^ (11 / 12 + δ) * Real.exp (-T / 2)) := by
  have hx0 : 0 < x := by linarith
  have hS := Sx_eq_integral χ hx0
  rw [integral_pf_shift hχ hx hδ hδ1] at hS
  have hMl : 0 < Mc θ (θ + δ) := Mc_pos (by linarith) (by linarith)
  have hMg : 0 < Mc (11 / 12) (11 / 12 + δ) := Mc_pos (by linarith) (by linarith)
  have hℓ1 : 1 ≤ Real.log (q + 2) := one_le_log_add_two q
  have hE0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hint1 : Integrable fun t : ℝ => pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I) := by
    refine integrable_of_le_inv (continuous_pf_line hχ hx0 (by linarith))
      (C := Mc (11 / 12) (11 / 12 + δ) * Real.log (q + 2) * x ^ (11 / 12 + δ)) fun t => ?_
    refine (norm_pf_global hχ hδ hδ1 le_rfl (by linarith) hx0).trans ?_
    have := exp_div_le_inv t
    have : 0 ≤ x ^ (11 / 12 + δ) := Real.rpow_nonneg hx0.le _
    gcongr
  have hsplit := verticalIntegral_split_three (f := pf χ x) (σ := 11 / 12 + δ) (-T) T hint1
  -- the rectangle `[θ + δ, 11/12 + δ] × [−T, T]`
  have hrect : RectangleIntegral (pf χ x) (((θ + δ : ℝ) : ℂ) - I * T) (((11 / 12 + δ : ℝ) : ℂ) + I * T) = 0 := by
    refine HolomorphicOn.vanishesOnRectangle (U := Rectangle (((θ + δ : ℝ) : ℂ) - I * T)
      (((11 / 12 + δ : ℝ) : ℂ) + I * T)) ?_ subset_rfl
    intro s hs
    rw [Rectangle, mem_reProdIm] at hs
    have hre1 : (((θ + δ : ℝ) : ℂ) - I * T).re = θ + δ := by simp
    have him1 : (((θ + δ : ℝ) : ℂ) - I * T).im = -T := by simp
    have hre2 : (((11 / 12 + δ : ℝ) : ℂ) + I * T).re = 11 / 12 + δ := by simp
    have him2 : (((11 / 12 + δ : ℝ) : ℂ) + I * T).im = T := by simp
    rw [hre1, him1, hre2, him2, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hs
    have hsre : θ + δ ≤ s.re := hs.1.1
    have hsim : |s.im| ≤ T := abs_le.2 ⟨hs.2.1, hs.2.2⟩
    exact (differentiableAt_pf hχ hx0 (by linarith)
      (hloc s (by linarith) (by linarith))).differentiableWithinAt
  have hre1 : (((θ + δ : ℝ) : ℂ) - I * T).re = θ + δ := by simp
  have him1 : (((θ + δ : ℝ) : ℂ) - I * T).im = -T := by simp
  have hre2 : (((11 / 12 + δ : ℝ) : ℂ) + I * T).re = 11 / 12 + δ := by simp
  have him2 : (((11 / 12 + δ : ℝ) : ℂ) + I * T).im = T := by simp
  rw [RectangleIntegral, hre1, him1, hre2, him2] at hrect
  have hV1 : VIntegral (pf χ x) (11 / 12 + δ) (-T) T = VIntegral (pf χ x) (θ + δ) (-T) T +
      HIntegral (pf χ x) (θ + δ) (11 / 12 + δ) T - HIntegral (pf χ x) (θ + δ) (11 / 12 + δ) (-T) := by
    linear_combination hrect
  -- the pieces
  set ℓ : ℝ := Real.log (q + 2) with hℓ
  set E : ℝ := Real.exp (-T / 2) with hE
  have hxθ₁ : 0 ≤ x ^ (11 / 12 + δ) := Real.rpow_nonneg hx0.le _
  have hxθ : 0 ≤ x ^ (θ + δ) := Real.rpow_nonneg hx0.le _
  have htail : ∀ t : ℝ, T ≤ |t| → ‖pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * (1 + t ^ 2)⁻¹ := by
    intro t ht
    refine (norm_pf_global hχ hδ hδ1 le_rfl (by linarith) hx0).trans ?_
    have h1 : Real.exp (-|t| / 2) ≤ E := Real.exp_le_exp.2 (by linarith)
    rw [div_eq_mul_inv]
    have : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    have : 0 ≤ Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) := by positivity
    calc Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * (Real.exp (-|t| / 2) * (1 + t ^ 2)⁻¹)
        ≤ Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * (E * (1 + t ^ 2)⁻¹) := by gcongr
      _ = Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * (1 + t ^ 2)⁻¹ := by ring
  have hCg : 0 ≤ Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E := by positivity
  have hA : ‖∫ t in Iic (-T), pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * π :=
    norm_setIntegral_le_pi measurableSet_Iic hCg fun t ht => htail t (by
      rw [mem_Iic] at ht; rw [abs_of_nonpos (by linarith)]; linarith)
  have hB : ‖∫ t in Ici T, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * π :=
    norm_setIntegral_le_pi measurableSet_Ici hCg fun t ht => htail t (by
      rw [mem_Ici] at ht; rw [abs_of_nonneg (by linarith)]; exact ht)
  have hCl : 0 ≤ Mc θ (θ + δ) * ℓ * x ^ (θ + δ) := by positivity
  have hV0 : ‖VIntegral (pf χ x) (θ + δ) (-T) T‖ ≤ Mc θ (θ + δ) * ℓ * x ^ (θ + δ) * π := by
    rw [VIntegral, norm_smul, norm_I, one_mul, intervalIntegral.integral_of_le (by linarith)]
    refine norm_setIntegral_le_pi measurableSet_Ioc hCl fun t ht => ?_
    have ht' : |t| ≤ T := abs_le.2 ⟨ht.1.le, ht.2⟩
    refine (norm_pf_le hχ hθ (by linarith) (by linarith) le_rfl (by linarith) hx0
      (zeroFree_ball_local hθ ht' hloc)).trans ?_
    have := exp_div_le_inv t
    gcongr
  have hH : ∀ y : ℝ, |y| = T → ‖HIntegral (pf χ x) (θ + δ) (11 / 12 + δ) y‖ ≤
      Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E := by
    intro y hy
    have hC : 0 ≤ Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E := by positivity
    have hb : ∀ σ ∈ Ι (θ + δ) (11 / 12 + δ), ‖pf χ x (σ + y * I)‖ ≤ Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E := by
      intro σ hσ
      rw [uIoc_of_le (by linarith)] at hσ
      refine (norm_pf_le hχ hθ (by linarith) (by linarith) hσ.1.le (by linarith [hσ.2]) hx0
        (zeroFree_ball_local hθ hy.le hloc)).trans ?_
      have hxσ : x ^ σ ≤ x ^ (11 / 12 + δ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
      have hEy : Real.exp (-|y| / 2) / (1 + y ^ 2) ≤ E := by
        rw [hy, div_le_iff₀ (by positivity)]
        have : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith
      have : 0 ≤ Real.exp (-|y| / 2) / (1 + y ^ 2) := by positivity
      have : 0 ≤ x ^ σ := Real.rpow_nonneg hx0.le _
      gcongr
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [HIntegral]
    refine hI.trans ?_
    have hlen : |11 / 12 + δ - (θ + δ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E * |11 / 12 + δ - (θ + δ)|
        ≤ Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E * 1 := by gcongr
      _ = Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E := mul_one _
  have hHp := hH T (abs_of_nonneg hT)
  have hHm := hH (-T) (by rw [abs_neg, abs_of_nonneg hT])
  -- assembly
  have hVI : ‖∫ t : ℝ, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * π +
        (Mc θ (θ + δ) * ℓ * x ^ (θ + δ) * π + Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E +
          Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E) +
        Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E * π := by
    have e : ‖∫ t : ℝ, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ = ‖VerticalIntegral (pf χ x) (11 / 12 + δ)‖ := by
      rw [VerticalIntegral, norm_smul, norm_I, one_mul]
    rw [e, hsplit, hV1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, norm_I, one_mul]; exact hA
    · refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hV0 hHp)) hHm)
    · rw [norm_smul, norm_I, one_mul]; exact hB
  have hpi : 0 < π := Real.pi_pos
  have hSn : ‖Sx χ x‖ = (1 / (2 * π)) * ‖∫ t : ℝ, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ := by
    rw [hS, norm_mul]
    congr 1
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  rw [hSn]
  set a : ℝ := Mc (11 / 12) (11 / 12 + δ) * ℓ * x ^ (11 / 12 + δ) * E with ha
  set b : ℝ := Mc θ (θ + δ) * ℓ * x ^ (θ + δ) with hb
  set c : ℝ := Mc θ (θ + δ) * ℓ * x ^ (11 / 12 + δ) * E with hc
  have ha0 : 0 ≤ a := hCg
  have hb0 : 0 ≤ b := hCl
  have hc0 : 0 ≤ c := by positivity
  have hstep : 1 / (2 * π) * (a * π + (b * π + c + c) + a * π) = a + b / 2 + c / π := by
    field_simp; ring
  have hcpi : c / π ≤ c := div_le_self hc0 (by linarith [Real.pi_gt_three])
  have hgoal : a + b / 2 + c / π ≤ (Mc θ (θ + δ) + Mc (11 / 12) (11 / 12 + δ)) * ℓ *
      (x ^ (θ + δ) + 2 * x ^ (11 / 12 + δ) * E) := by
    have e1 : b ≤ (Mc θ (θ + δ) + Mc (11 / 12) (11 / 12 + δ)) * ℓ * x ^ (θ + δ) := by
      rw [hb]; gcongr; linarith
    have e2 : a + c = (Mc θ (θ + δ) + Mc (11 / 12) (11 / 12 + δ)) * ℓ * x ^ (11 / 12 + δ) * E := by
      rw [ha, hc]; ring
    have e3 : 0 ≤ (Mc θ (θ + δ) + Mc (11 / 12) (11 / 12 + δ)) * ℓ * x ^ (11 / 12 + δ) * E := by positivity
    nlinarith
  calc 1 / (2 * π) * ‖∫ t : ℝ, pf χ x (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖
      ≤ 1 / (2 * π) * (a * π + (b * π + c + c) + a * π) := by gcongr
    _ = a + b / 2 + c / π := hstep
    _ ≤ _ := hgoal

end Linnik

#print axioms Linnik.perron_exp
#print axioms Linnik.logDeriv_LFunction_le
#print axioms Linnik.norm_pf_le
#print axioms Linnik.Sx_eq_integral
#print axioms Linnik.integral_pf_shift
#print axioms Linnik.norm_Sx_le
