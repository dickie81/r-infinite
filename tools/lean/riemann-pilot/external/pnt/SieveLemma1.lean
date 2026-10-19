/-
# Round 591: weighted prime sums at a height inside a zero-free rectangle (Lemma 1 of the sieve route, `Λ` form)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`norm_Sw_le`). Let `χ ≠ 1` be a Dirichlet character mod `q`, `½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`,
`H ≥ 0`, `X ≥ 1`, `y` real, and `w` a weight, continuous on `(0, ∞)`, whose Mellin transform converges at `2`, is
differentiable on `Re s ≥ θ + δ` and satisfies `(1 + |t − y|)^{K+3}|𝓜w(σ + it)| ≤ B` for `θ + δ ≤ σ ≤ 2`. If
`L(·, χ)` has no zero in `Re s > θ`, `|Im s − y| < H + 1`, then
`|Σ_n χ(n)Λ(n)w(n/X)| ≤ M A B(X^{θ+δ} + X^{11/12+δ}(1 + H)^{−K})`, with
`M = KL(θ, θ + δ) + KL(11/12, 11/12 + δ)` and `A = log(q + 2) + log(|y| + 4) + 1`.

This is round 520's `Linnik.norm_Sx_le` with the weight `w` in place of `e^{−u}`, and with the rectangle centred at
height `y`. For `w(u) = u^{−iy}ψ(u)`, `𝓜w(s) = 𝓜ψ(s − iy)`, the sum is `X^{iy}Σ_n χ(n)Λ(n)n^{−iy}ψ(n/X)`:
`frontier/linnik/SIEVE-ROUTE.md` §3's Lemma 1 at height `y`, for von Mangoldt's weights.

* `perron_weight`: `(1/2π) ∫ L(f, σ + it)𝓜w(σ + it)X^{σ+it} dt = Σ_n f(n)w(n/X)`
  (`SmoothPerron.verticalIntegral_eq_smoothedSum` with `w` in place of `Smooth1`).
* `norm_pw_le`: the integrand `−L′/L(s, χ)𝓜w(s)X^s` (`pw`) is at most `KL(θ, θ′)A B X^σ(1 + |t − y|)^{−(K+2)}`
  where `L(·, χ)` has no zero in the disc of radius `3/2 − θ` about `3/2 + it`.
* `integral_pw_shift`: the line `Re s = 2` moves to `Re s = 11/12 + δ` (`SmoothPerron.verticalIntegral_shift`).
* `norm_Sw_le`: for `|t − y| ≤ H` the line moves across the rectangle `[θ + δ, 11/12 + δ] × [y − H, y + H]`.
-/
import LinnikChar

open Complex Set Real Filter Topology MeasureTheory
open scoped Interval

noncomputable section

namespace SieveLemma1

open LogDerivDisc ChiUniform DirichletCharacter InghamDensity Linnik

/-! ### Perron's formula with a weight -/

/-- **Perron's formula with a weight `w`.** For `f(0) = 0`, `L(f, σ)` absolutely convergent, `X > 0`, and `w`
continuous on `(0, ∞)` with `𝓜w` convergent at `σ` and integrable and continuous on `Re s = σ`:
`(1/2π) ∫ L(f, σ + it)𝓜w(σ + it)X^{σ+it} dt = Σ_n f(n)w(n/X)`. -/
theorem perron_weight {f : ℕ → ℂ} (hf0 : f 0 = 0) {w : ℝ → ℂ} {σ X : ℝ} (hX : 0 < X)
    (hw : ∀ x : ℝ, 0 < x → ContinuousAt w x) (hMc : MellinConvergent w σ)
    (hMv : VerticalIntegrable (mellin w) σ) (hMcont : Continuous fun t : ℝ => mellin w (σ + t * I))
    (hf : LSeriesSummable f σ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries f (σ + t * I) * mellin w (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I) =
      ∑' n : ℕ, f n * w (n / X) := by
  let F : ℕ → ℝ → ℂ := fun n t ↦
    LSeries.term f (σ + t * I) n * mellin w (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I)
  have hnormF : ∀ n t, ‖F n t‖ = ‖LSeries.term f σ n‖ * X ^ σ * ‖mellin w (σ + t * I)‖ := by
    intro n t
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos hX, LSeries.norm_term_eq]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
    ring
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [F, LSeries.term_zero, zero_mul]
      exact continuous_const
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 hX.ne'
      have e : F n = fun t : ℝ ↦ f n / (n : ℂ) ^ ((σ : ℂ) + t * I) * mellin w (σ + t * I) *
          (X : ℂ) ^ ((σ : ℂ) + t * I) := by
        funext t
        simp only [F, LSeries.term_of_ne_zero hn]
      rw [e]
      have h1 : Continuous fun t : ℝ ↦ (n : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hn')
      have h2 : Continuous fun t : ℝ ↦ (X : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hX')
      have h3 : ∀ t : ℝ, (n : ℂ) ^ ((σ : ℂ) + t * I) ≠ 0 := fun t ↦ by
        rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn' h.1
      exact ((continuous_const.div h1 h3).mul hMcont).mul h2
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    refine Integrable.mono' (hMv.norm.const_mul (‖LSeries.term f σ n‖ * X ^ σ))
      (hFcont n).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t ↦ (hnormF n t).le
  have hFsum : Summable fun n ↦ ∫ t, ‖F n t‖ := by
    simp_rw [hnormF, integral_const_mul]
    exact (hf.norm.mul_right (X ^ σ)).mul_right _
  have hsum_pt : ∀ t : ℝ, LSeries f (σ + t * I) * mellin w (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I) =
      ∑' n, F n t := by
    intro t
    simp only [F, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
  calc (1 / (2 * π) : ℂ) * ∫ t : ℝ, LSeries f (σ + t * I) * mellin w (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I)
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, ∑' n, F n t := by simp_rw [hsum_pt]
    _ = (1 / (2 * π) : ℂ) * ∑' n, ∫ t : ℝ, F n t := by
        rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = ∑' n, (1 / (2 * π) : ℂ) * ∫ t : ℝ, F n t := by rw [tsum_mul_left]
    _ = ∑' n : ℕ, f n * w (n / X) := by
        congr 1
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [F, hf0]
        · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
          have hx : 0 < (n : ℝ) / X := div_pos hnpos hX
          have hinv := mellinInv_mellin_eq σ w hx hMc hMv (hw _ hx)
          rw [mellinInv] at hinv
          have hpt : ∀ t : ℝ, F n t = f n * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) •
              mellin w (σ + t * I)) := by
            intro t
            simp only [F, LSeries.term_of_ne_zero hn]
            exact SmoothPerron.div_cpow_mul_cpow hn hX _ _ _
          simp_rw [hpt]
          rw [integral_const_mul, ← hinv, Complex.real_smul]
          push_cast
          ring

/-! ### The integrand -/

variable {q : ℕ} [NeZero q]

/-- The weighted sum `Σ_n χ(n)Λ(n)w(n/X)`. -/
def Sw (χ : DirichletCharacter ℂ q) (w : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * w (n / X)

/-- The Perron integrand `−L′/L(s, χ)𝓜w(s)X^s`. -/
def pw (χ : DirichletCharacter ℂ q) (w : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * mellin w s * (X : ℂ) ^ s

theorem differentiableAt_pw {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℝ → ℂ} {X : ℝ} (hX : 0 < X) {s : ℂ}
    (hM : DifferentiableAt ℂ (mellin w) s) (hL : LFunction χ s ≠ 0) : DifferentiableAt ℂ (pw χ w X) s := by
  have hF := differentiable_LFunction hχ
  have hdF : DifferentiableAt ℂ (deriv (LFunction χ)) s := (hF.analyticAt s).deriv.differentiableAt
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.2 hX.ne'
  have hc : DifferentiableAt ℂ (fun s : ℂ => (X : ℂ) ^ s) s := differentiableAt_id.const_cpow (Or.inl hX')
  exact (((hdF.div (hF s) hL).neg).mul hM).mul hc

/-- **Perron for `Σ_n χ(n)Λ(n)w(n/X)`**: it is `(1/2π) ∫ −L′/L(2 + it, χ)𝓜w(2 + it)X^{2+it} dt`. -/
theorem Sw_eq_integral (χ : DirichletCharacter ℂ q) {w : ℝ → ℂ} {X : ℝ} (hX : 0 < X)
    (hw : ∀ x : ℝ, 0 < x → ContinuousAt w x) (hMc : MellinConvergent w ((2 : ℝ) : ℂ))
    (hMv : VerticalIntegrable (mellin w) 2) (hMcont : Continuous fun t : ℝ => mellin w (((2 : ℝ) : ℂ) + t * I)) :
    Sw χ w X = (1 / (2 * π) : ℂ) * ∫ t : ℝ, pw χ w X (((2 : ℝ) : ℂ) + t * I) := by
  have h := perron_weight (f := fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp) hX hw hMc hMv
    hMcont (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num))
  rw [Sw, ← h]
  congr 2
  funext t
  rw [ChiPNT.LSeries_twist_vonMangoldt_eq_LFunction χ (by simp), pw]

/-- `log(|t| + 4) ≤ log(|y| + 4) + log(1 + |t − y|)`. -/
lemma log_abs_add_four_le (t y : ℝ) : Real.log (|t| + 4) ≤ Real.log (|y| + 4) + Real.log (1 + |t - y|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have h1 : |t| ≤ |y| + |t - y| := by
    have := abs_add_le y (t - y)
    rwa [add_sub_cancel] at this
  have h2 : 0 ≤ |y| * |t - y| := by positivity
  nlinarith [abs_nonneg (t - y)]

/-- **The integrand where `L(·, χ)` has no zero in one disc**: for `χ ≠ 1`, `½ ≤ θ < θ' < 3/2`, `θ' ≤ σ` and `X > 0`,
if `L(·, χ)` has no zero in the disc of radius `3/2 − θ` about `3/2 + it` and `(1 + |t − y|)^{K+3}|𝓜w(σ + it)| ≤ B`,
then `|pw(σ + it)| ≤ KL(θ, θ')(log(q + 2) + log(|y| + 4) + 1)B X^σ(1 + |t − y|)^{−(K+2)}`. -/
theorem norm_pw_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℝ → ℂ} {θ θ' σ t X y B : ℝ} {K : ℕ}
    (hθ : 1 / 2 ≤ θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2) (hσ : θ' ≤ σ) (hX : 0 < X)
    (hzf : ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), LFunction χ s ≠ 0)
    (hMw : (1 + |t - y|) ^ (K + 3) * ‖mellin w (σ + t * I)‖ ≤ B) :
    ‖pw χ w X (σ + t * I)‖ ≤
      KL θ θ' * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B * X ^ σ * ((1 + |t - y|) ^ (K + 2))⁻¹ := by
  have hL := logDeriv_LFunction_le hχ hθ hθθ' hθ'32 hσ hzf
  have hXs : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]; simp
  set u := |t - y| with hu
  have hu0 : 0 ≤ u := abs_nonneg _
  have hlq := one_le_log_add_two q
  have hly : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by linarith [abs_nonneg y])
  set A := Real.log (q + 2) + Real.log (|y| + 4) with hA
  have hA0 : 0 ≤ A := by linarith
  have hKL := KL_pos hθθ' hθ'32
  have hlog : Real.log (q + 2) + Real.log (|t| + 4) ≤ (A + 1) * (1 + u) := by
    have h1 := log_abs_add_four_le t y
    have h2 : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u); linarith
    nlinarith
  have hpos : 0 < (1 + u) ^ (K + 3) := by positivity
  have hM : ‖mellin w (σ + t * I)‖ ≤ B * ((1 + u) ^ (K + 3))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) hMw
  have hXσ : 0 ≤ X ^ σ := Real.rpow_nonneg hX.le _
  have hl4 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  have e : (1 + u) * ((1 + u) ^ (K + 3))⁻¹ = ((1 + u) ^ (K + 2))⁻¹ := by
    rw [pow_succ]; field_simp
  calc ‖pw χ w X (σ + t * I)‖ = ‖deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)‖ *
        ‖mellin w (σ + t * I)‖ * X ^ σ := by
        rw [pw, norm_mul, norm_mul, norm_neg, hXs]
    _ ≤ (KL θ θ' * (Real.log (q + 2) + Real.log (|t| + 4))) * (B * ((1 + u) ^ (K + 3))⁻¹) * X ^ σ := by
        gcongr
    _ ≤ (KL θ θ' * ((A + 1) * (1 + u))) * (B * ((1 + u) ^ (K + 3))⁻¹) * X ^ σ := by gcongr
    _ = KL θ θ' * (A + 1) * B * X ^ σ * ((1 + u) * ((1 + u) ^ (K + 3))⁻¹) := by ring
    _ = KL θ θ' * (A + 1) * B * X ^ σ * ((1 + u) ^ (K + 2))⁻¹ := by rw [e]

/-- `(1 + u)^{−(K+2)} ≤ (1 + u²)^{−1}` for `u ≥ 0`. -/
lemma inv_pow_le_inv_one_add_sq {u : ℝ} (hu : 0 ≤ u) (K : ℕ) : ((1 + u) ^ (K + 2))⁻¹ ≤ (1 + u ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  calc 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
    _ ≤ (1 + u) ^ (K + 2) := pow_le_pow_right₀ (by linarith) (by omega)

/-- `(1 + u)^{−(K+2)} ≤ (1 + H)^{−K}(1 + u²)^{−1}` for `u ≥ H ≥ 0`. -/
lemma inv_pow_le_tail {u H : ℝ} (hH : 0 ≤ H) (hu : H ≤ u) (K : ℕ) :
    ((1 + u) ^ (K + 2))⁻¹ ≤ ((1 + H) ^ K)⁻¹ * (1 + u ^ 2)⁻¹ := by
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (1 + H) ^ K * (1 + u ^ 2) ≤ (1 + u) ^ K * (1 + u) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) K) (by nlinarith) (by positivity)
          (pow_nonneg (by linarith) K)
    _ = (1 + u) ^ (K + 2) := by rw [pow_add]

/-- `‖∫_S f‖ ≤ Cπ` when `‖f(t)‖ ≤ C(1 + (t − y)²)⁻¹` on a measurable `S`. -/
lemma norm_setIntegral_le_pi_at {f : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S) {C y : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t ∈ S, ‖f t‖ ≤ C * (1 + (t - y) ^ 2)⁻¹) : ‖∫ t in S, f t‖ ≤ C * π := by
  have hg : Integrable (fun t : ℝ => C * (1 + (t - y) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_sub_right y).const_mul C
  calc ‖∫ t in S, f t‖ ≤ ∫ t in S, C * (1 + (t - y) ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hg.integrableOn ((ae_restrict_iff' hS).2 (Eventually.of_forall hf))
    _ ≤ ∫ t, C * (1 + (t - y) ^ 2)⁻¹ := setIntegral_le_integral hg (Eventually.of_forall fun t => by positivity)
    _ = C * π := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun t => (1 + t ^ 2)⁻¹) y,
          integral_univ_inv_one_add_sq]

lemma integrable_of_le_inv_at {f : ℝ → ℂ} (hf : Continuous f) {C y : ℝ}
    (hC : ∀ t, ‖f t‖ ≤ C * (1 + (t - y) ^ 2)⁻¹) : Integrable f :=
  Integrable.mono' ((integrable_inv_one_add_sq.comp_sub_right y).const_mul C) hf.aestronglyMeasurable
    (Eventually.of_forall hC)

/-- The disc of radius `3/2 − θ` about `3/2 + it`, `|t − y| ≤ H`, holds no zero when `L(·, χ)` has none in
`Re s > θ`, `|Im s − y| < H + 1`. -/
lemma zeroFree_ball_at {χ : DirichletCharacter ℂ q} {θ H y t : ℝ} (hθ : 1 / 2 ≤ θ) (ht : |t - y| ≤ H)
    (hloc : ∀ s : ℂ, θ < s.re → |s.im - y| < H + 1 → LFunction χ s ≠ 0) :
    ∀ s ∈ Metric.ball (ctr t) (3 / 2 - θ), LFunction χ s ≠ 0 := fun s hs => by
  refine hloc s (LogDerivDisc.re_gt_of_mem_ball hs) ?_
  have h1 := LogDerivDisc.im_sub_lt_of_mem_ball hθ hs
  have h2 : |s.im - y| ≤ |s.im - t| + |t - y| := abs_sub_le _ _ _
  linarith

/-! ### Moving the line to `Re s = 11/12 + δ` -/

/-- **The line moves from `Re s = 2` to `Re s = 11/12 + δ`** (`SmoothPerron.verticalIntegral_shift`), for weights with
`(1 + |t − y|)^{K+3}|𝓜w(σ + it)| ≤ B` on `11/12 + δ ≤ σ ≤ 2`. -/
theorem integral_pw_shift {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℝ → ℂ} {X δ y B : ℝ} {K : ℕ}
    (hX : 1 ≤ X) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24)
    (hMd : ∀ s : ℂ, 11 / 12 + δ ≤ s.re → DifferentiableAt ℂ (mellin w) s)
    (hMb : ∀ σ ∈ Icc (11 / 12 + δ) 2, ∀ t : ℝ, (1 + |t - y|) ^ (K + 3) * ‖mellin w (σ + t * I)‖ ≤ B) :
    ∫ t : ℝ, pw χ w X (((2 : ℝ) : ℂ) + t * I) = ∫ t : ℝ, pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I) := by
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) (hMb 2 ⟨by linarith, le_rfl⟩ 0)
  set M₀ : ℝ := KL (11 / 12) (11 / 12 + δ) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B * X ^ (2 : ℝ)
    with hM₀
  have hM₀0 : 0 ≤ M₀ := by
    have := KL_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
    have := one_le_log_add_two q
    have : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by linarith [abs_nonneg y])
    positivity
  have hb : ∀ σ ∈ Icc (11 / 12 + δ) 2, ∀ t : ℝ, ‖pw χ w X (σ + t * I)‖ ≤ M₀ * (1 + (t - y) ^ 2)⁻¹ := by
    intro σ hσ t
    refine (norm_pw_le hχ (θ := 11 / 12) (by norm_num) (by linarith) (by linarith) hσ.1 hX0
      (zeroFree_ball_global hχ t) (hMb σ hσ t)).trans ?_
    have hXσ : X ^ σ ≤ X ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hσ.2
    have hE := inv_pow_le_inv_one_add_sq (abs_nonneg (t - y)) K
    rw [sq_abs] at hE
    have := KL_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
    have := one_le_log_add_two q
    have : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by linarith [abs_nonneg y])
    have : 0 ≤ ((1 + |t - y|) ^ (K + 2))⁻¹ := by positivity
    calc KL (11 / 12) (11 / 12 + δ) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B * X ^ σ *
          ((1 + |t - y|) ^ (K + 2))⁻¹
        ≤ KL (11 / 12) (11 / 12 + δ) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B * X ^ (2 : ℝ) *
          (1 + (t - y) ^ 2)⁻¹ := by gcongr
      _ = M₀ * (1 + (t - y) ^ 2)⁻¹ := by rw [hM₀]
  have hhol : HolomorphicOn (pw χ w X) (Icc (11 / 12 + δ) 2 ×ℂ univ) := by
    intro s hs
    rw [mem_reProdIm] at hs
    exact (differentiableAt_pw hχ hX0 (hMd s hs.1.1)
      (Eis.LFunction_ne_zero_of_re_gt χ (by linarith [hs.1.1]) (Or.inl hχ))).differentiableWithinAt
  have hcont : ∀ σ ∈ Icc (11 / 12 + δ) 2, Continuous fun t : ℝ => pw χ w X ((σ : ℂ) + t * I) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro t
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    exact ContinuousAt.comp (g := pw χ w X) (f := fun t : ℝ => (σ : ℂ) + t * I)
      (differentiableAt_pw hχ hX0 (hMd _ (by rw [hre]; exact hσ.1))
        (Eis.LFunction_ne_zero_of_re_gt χ (by rw [hre]; linarith [hσ.1]) (Or.inl hχ))).continuousAt
      (by fun_prop)
  have hint2 := integrable_of_le_inv_at (hcont 2 ⟨by linarith, le_rfl⟩) (hb 2 ⟨by linarith, le_rfl⟩)
  have hint1 := integrable_of_le_inv_at (hcont (11 / 12 + δ) ⟨le_rfl, by linarith⟩)
    (hb (11 / 12 + δ) ⟨le_rfl, by linarith⟩)
  have hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ σ ∈ Icc (11 / 12 + δ) 2, ∀ t : ℝ, T₀ ≤ |t| →
      ‖pw χ w X (σ + t * I)‖ ≤ η := by
    intro η hη
    refine ⟨|y| + M₀ / η + 1, fun σ hσ t ht => ?_⟩
    refine (hb σ hσ t).trans ?_
    have hpos : 0 < 1 + (t - y) ^ 2 := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have h0 : |t| - |y| ≤ |t - y| := abs_sub_abs_le_abs_sub t y
    have h1 : |t - y| ≤ 1 + (t - y) ^ 2 := by nlinarith [sq_abs (t - y), abs_nonneg (t - y)]
    have h2 : M₀ / η * η = M₀ := div_mul_cancel₀ _ hη.ne'
    have h3 : M₀ / η ≤ 1 + (t - y) ^ 2 := by linarith
    nlinarith
  have hshift := SmoothPerron.verticalIntegral_shift (G := pw χ w X) (σ' := 11 / 12 + δ) (σ := 2)
    (by linarith) hhol hint2 hint1 hdecay
  simp only [VerticalIntegral] at hshift
  exact smul_right_injective ℂ I_ne_zero hshift

/-! ### The bound in a zero-free rectangle at height `y` -/

/-- **Lemma 1 in `Λ` form.** Let `χ ≠ 1`, `½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`, `H ≥ 0`, `X ≥ 1`, and let `w` be continuous
on `(0, ∞)` with `𝓜w` convergent at `2`, differentiable on `Re s ≥ θ + δ`, and
`(1 + |t − y|)^{K+3}|𝓜w(σ + it)| ≤ B` for `θ + δ ≤ σ ≤ 2`. If `L(·, χ)` has no zero in `Re s > θ`,
`|Im s − y| < H + 1`, then `|Σ_n χ(n)Λ(n)w(n/X)| ≤ M A B(X^{θ+δ} + X^{11/12+δ}(1 + H)^{−K})`, with
`M = KL(θ, θ + δ) + KL(11/12, 11/12 + δ)` and `A = log(q + 2) + log(|y| + 4) + 1`: the line `Re s = 2` moves to
`11/12 + δ`, and for `|t − y| ≤ H` across the rectangle `[θ + δ, 11/12 + δ] × [y − H, y + H]` to `θ + δ`. -/
theorem norm_Sw_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℝ → ℂ} {θ δ H X y B : ℝ} {K : ℕ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 11 / 12) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hH : 0 ≤ H) (hX : 1 ≤ X)
    (hw : ∀ x : ℝ, 0 < x → ContinuousAt w x) (hMc : MellinConvergent w ((2 : ℝ) : ℂ))
    (hMd : ∀ s : ℂ, θ + δ ≤ s.re → DifferentiableAt ℂ (mellin w) s)
    (hMb : ∀ σ ∈ Icc (θ + δ) 2, ∀ t : ℝ, (1 + |t - y|) ^ (K + 3) * ‖mellin w (σ + t * I)‖ ≤ B)
    (hloc : ∀ s : ℂ, θ < s.re → |s.im - y| < H + 1 → LFunction χ s ≠ 0) :
    ‖Sw χ w X‖ ≤ (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) *
      B * (X ^ (θ + δ) + X ^ (11 / 12 + δ) * ((1 + H) ^ K)⁻¹) := by
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) (hMb 2 ⟨by linarith, le_rfl⟩ 0)
  -- the Mellin transform on a line `Re s = σ ≥ θ + δ`
  have hMcont : ∀ σ : ℝ, θ + δ ≤ σ → Continuous fun t : ℝ => mellin w ((σ : ℂ) + t * I) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro t
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    exact ContinuousAt.comp (g := mellin w) (f := fun t : ℝ => (σ : ℂ) + t * I)
      (hMd _ (by rw [hre]; exact hσ)).continuousAt (by fun_prop)
  have hMb2 : ∀ t : ℝ, ‖mellin w (((2 : ℝ) : ℂ) + t * I)‖ ≤ B * (1 + (t - y) ^ 2)⁻¹ := by
    intro t
    have h := hMb 2 ⟨by linarith, le_rfl⟩ t
    have hpos : 0 < (1 + |t - y|) ^ (K + 3) := by positivity
    have hE := inv_pow_le_inv_one_add_sq (abs_nonneg (t - y)) (K + 1)
    rw [sq_abs] at hE
    calc ‖mellin w (((2 : ℝ) : ℂ) + t * I)‖ ≤ B * ((1 + |t - y|) ^ (K + 1 + 2))⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
      _ ≤ B * (1 + (t - y) ^ 2)⁻¹ := by gcongr
  have hMv : VerticalIntegrable (mellin w) 2 := integrable_of_le_inv_at (hMcont 2 (by linarith)) hMb2
  have hS := Sw_eq_integral χ hX0 hw hMc hMv (hMcont 2 (by linarith))
  rw [integral_pw_shift hχ hX hδ hδ1 (fun s hs => hMd s (by linarith))
    (fun σ hσ t => hMb σ ⟨by linarith [hσ.1], hσ.2⟩ t)] at hS
  set ℓ : ℝ := Real.log (q + 2) + Real.log (|y| + 4) + 1 with hℓ
  have hℓ0 : 0 ≤ ℓ := by
    have := one_le_log_add_two q
    have : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by linarith [abs_nonneg y])
    rw [hℓ]; linarith
  set E : ℝ := ((1 + H) ^ K)⁻¹ with hE
  have hE0 : 0 ≤ E := by positivity
  have hKl := KL_pos (θ := θ) (θ' := θ + δ) (by linarith) (by linarith)
  have hKg := KL_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
  -- the integrand on `Re s = 11/12 + δ`
  have hglob : ∀ t : ℝ, ‖pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * ((1 + |t - y|) ^ (K + 2))⁻¹ :=
    fun t => norm_pw_le hχ (θ := 11 / 12) (by norm_num) (by linarith) (by linarith) le_rfl hX0
      (zeroFree_ball_global hχ t) (hMb (11 / 12 + δ) ⟨by linarith, by linarith⟩ t)
  have hint1 : Integrable fun t : ℝ => pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I) := by
    have hcont : Continuous fun t : ℝ => pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hre : (((11 / 12 + δ : ℝ) : ℂ) + t * I).re = 11 / 12 + δ := by simp
      exact ContinuousAt.comp (g := pw χ w X) (f := fun t : ℝ => ((11 / 12 + δ : ℝ) : ℂ) + t * I)
        (differentiableAt_pw hχ hX0 (hMd _ (by rw [hre]; linarith))
          (Eis.LFunction_ne_zero_of_re_gt χ (by rw [hre]; linarith) (Or.inl hχ))).continuousAt (by fun_prop)
    refine integrable_of_le_inv_at hcont (C := KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ))
      (y := y) fun t => (hglob t).trans ?_
    have hE' := inv_pow_le_inv_one_add_sq (abs_nonneg (t - y)) K
    rw [sq_abs] at hE'
    have : 0 ≤ X ^ (11 / 12 + δ) := Real.rpow_nonneg hX0.le _
    gcongr
  have hsplit := verticalIntegral_split_three (f := pw χ w X) (σ := 11 / 12 + δ) (y - H) (y + H) hint1
  -- the rectangle `[θ + δ, 11/12 + δ] × [y − H, y + H]`
  have hre1 : (((θ + δ : ℝ) : ℂ) + I * (y - H)).re = θ + δ := by simp
  have him1 : (((θ + δ : ℝ) : ℂ) + I * (y - H)).im = y - H := by simp
  have hre2 : (((11 / 12 + δ : ℝ) : ℂ) + I * (y + H)).re = 11 / 12 + δ := by simp
  have him2 : (((11 / 12 + δ : ℝ) : ℂ) + I * (y + H)).im = y + H := by simp
  have hrect : RectangleIntegral (pw χ w X) (((θ + δ : ℝ) : ℂ) + I * (y - H))
      (((11 / 12 + δ : ℝ) : ℂ) + I * (y + H)) = 0 := by
    refine HolomorphicOn.vanishesOnRectangle (U := Rectangle (((θ + δ : ℝ) : ℂ) + I * (y - H))
      (((11 / 12 + δ : ℝ) : ℂ) + I * (y + H))) ?_ subset_rfl
    intro s hs
    rw [Rectangle, mem_reProdIm] at hs
    rw [hre1, him1, hre2, him2, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hs
    have hsre : θ + δ ≤ s.re := hs.1.1
    have hsim : |s.im - y| ≤ H := abs_le.2 ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
    exact (differentiableAt_pw hχ hX0 (hMd s hsre)
      (hloc s (by linarith) (by linarith))).differentiableWithinAt
  rw [RectangleIntegral, hre1, him1, hre2, him2] at hrect
  have hV1 : VIntegral (pw χ w X) (11 / 12 + δ) (y - H) (y + H) = VIntegral (pw χ w X) (θ + δ) (y - H) (y + H) +
      HIntegral (pw χ w X) (θ + δ) (11 / 12 + δ) (y + H) -
        HIntegral (pw χ w X) (θ + δ) (11 / 12 + δ) (y - H) := by
    linear_combination hrect
  -- the pieces
  have hX1 : 0 ≤ X ^ (11 / 12 + δ) := Real.rpow_nonneg hX0.le _
  have hXl : 0 ≤ X ^ (θ + δ) := Real.rpow_nonneg hX0.le _
  have hCg : 0 ≤ KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E := by positivity
  have htail : ∀ t : ℝ, H ≤ |t - y| → ‖pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * (1 + (t - y) ^ 2)⁻¹ := by
    intro t ht
    refine (hglob t).trans ?_
    have h := inv_pow_le_tail hH ht K
    rw [sq_abs] at h
    calc KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * ((1 + |t - y|) ^ (K + 2))⁻¹
        ≤ KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * (E * (1 + (t - y) ^ 2)⁻¹) := by gcongr
      _ = KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * (1 + (t - y) ^ 2)⁻¹ := by ring
  have hA : ‖∫ t in Iic (y - H), pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * π :=
    norm_setIntegral_le_pi_at measurableSet_Iic hCg fun t ht => htail t (by
      rw [mem_Iic] at ht; rw [abs_of_nonpos (by linarith)]; linarith)
  have hBt : ‖∫ t in Ici (y + H), pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * π :=
    norm_setIntegral_le_pi_at measurableSet_Ici hCg fun t ht => htail t (by
      rw [mem_Ici] at ht; rw [abs_of_nonneg (by linarith)]; linarith)
  have hCl : 0 ≤ KL θ (θ + δ) * ℓ * B * X ^ (θ + δ) := by positivity
  have hV0 : ‖VIntegral (pw χ w X) (θ + δ) (y - H) (y + H)‖ ≤ KL θ (θ + δ) * ℓ * B * X ^ (θ + δ) * π := by
    rw [VIntegral, norm_smul, norm_I, one_mul, intervalIntegral.integral_of_le (by linarith)]
    refine norm_setIntegral_le_pi_at (y := y) measurableSet_Ioc hCl fun t ht => ?_
    have ht' : |t - y| ≤ H := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine (norm_pw_le hχ hθ (by linarith) (by linarith) le_rfl hX0 (zeroFree_ball_at hθ ht' hloc)
      (hMb (θ + δ) ⟨le_rfl, by linarith⟩ t)).trans ?_
    have hE' := inv_pow_le_inv_one_add_sq (abs_nonneg (t - y)) K
    rw [sq_abs] at hE'
    gcongr
  have hH' : ∀ v : ℝ, |v - y| = H → ‖HIntegral (pw χ w X) (θ + δ) (11 / 12 + δ) v‖ ≤
      KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E := by
    intro v hv
    have hC : 0 ≤ KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E := by positivity
    have hb : ∀ σ ∈ Ι (θ + δ) (11 / 12 + δ), ‖pw χ w X (σ + v * I)‖ ≤
        KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E := by
      intro σ hσ
      rw [uIoc_of_le (by linarith)] at hσ
      refine (norm_pw_le hχ hθ (by linarith) (by linarith) hσ.1.le hX0 (zeroFree_ball_at hθ hv.le hloc)
        (hMb σ ⟨hσ.1.le, by linarith [hσ.2]⟩ v)).trans ?_
      have hXσ : X ^ σ ≤ X ^ (11 / 12 + δ) := Real.rpow_le_rpow_of_exponent_le hX hσ.2
      have hEv : ((1 + |v - y|) ^ (K + 2))⁻¹ ≤ E := by
        rw [hv, hE]
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ (by linarith) (by omega)
      have : 0 ≤ ((1 + |v - y|) ^ (K + 2))⁻¹ := by positivity
      have : 0 ≤ X ^ σ := Real.rpow_nonneg hX0.le _
      gcongr
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [HIntegral]
    refine hI.trans ?_
    have hlen : |11 / 12 + δ - (θ + δ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * |11 / 12 + δ - (θ + δ)|
        ≤ KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * 1 := by gcongr
      _ = KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E := mul_one _
  have hHp := hH' (y + H) (by rw [add_sub_cancel_left, abs_of_nonneg hH])
  have hHm := hH' (y - H) (by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hH])
  -- assembly
  have hVI : ‖∫ t : ℝ, pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ ≤
      KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * π +
        (KL θ (θ + δ) * ℓ * B * X ^ (θ + δ) * π + KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E +
          KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E) +
        KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E * π := by
    have e : ‖∫ t : ℝ, pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ =
        ‖VerticalIntegral (pw χ w X) (11 / 12 + δ)‖ := by
      rw [VerticalIntegral, norm_smul, norm_I, one_mul]
    rw [e, hsplit, hV1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, norm_I, one_mul]; exact hA
    · refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hV0 hHp)) hHm)
    · rw [norm_smul, norm_I, one_mul]; exact hBt
  have hpi : 0 < π := Real.pi_pos
  have hSn : ‖Sw χ w X‖ = (1 / (2 * π)) * ‖∫ t : ℝ, pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖ := by
    rw [hS, norm_mul]
    congr 1
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  rw [hSn]
  set a : ℝ := KL (11 / 12) (11 / 12 + δ) * ℓ * B * X ^ (11 / 12 + δ) * E with ha
  set b : ℝ := KL θ (θ + δ) * ℓ * B * X ^ (θ + δ) with hb
  set c : ℝ := KL θ (θ + δ) * ℓ * B * X ^ (11 / 12 + δ) * E with hc
  have ha0 : 0 ≤ a := hCg
  have hb0 : 0 ≤ b := hCl
  have hc0 : 0 ≤ c := by positivity
  have hstep : 1 / (2 * π) * (a * π + (b * π + c + c) + a * π) = a + b / 2 + c / π := by
    field_simp; ring
  have hcpi : c / π ≤ c := div_le_self hc0 (by linarith [Real.pi_gt_three])
  have hgoal : a + b / 2 + c / π ≤ (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B *
      (X ^ (θ + δ) + X ^ (11 / 12 + δ) * E) := by
    have e1 : b ≤ (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B * X ^ (θ + δ) := by
      rw [hb]; gcongr; linarith
    have e2 : a + c = (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B * (X ^ (11 / 12 + δ) * E) := by
      rw [ha, hc]; ring
    have e3 : (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B * (X ^ (θ + δ) + X ^ (11 / 12 + δ) * E) =
        (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B * X ^ (θ + δ) +
          (KL θ (θ + δ) + KL (11 / 12) (11 / 12 + δ)) * ℓ * B * (X ^ (11 / 12 + δ) * E) := by ring
    rw [e3]
    linarith
  calc 1 / (2 * π) * ‖∫ t : ℝ, pw χ w X (((11 / 12 + δ : ℝ) : ℂ) + t * I)‖
      ≤ 1 / (2 * π) * (a * π + (b * π + c + c) + a * π) := by gcongr
    _ = a + b / 2 + c / π := hstep
    _ ≤ _ := hgoal

end SieveLemma1

#print axioms SieveLemma1.perron_weight
#print axioms SieveLemma1.Sw_eq_integral
#print axioms SieveLemma1.norm_pw_le
#print axioms SieveLemma1.integral_pw_shift
#print axioms SieveLemma1.norm_Sw_le
