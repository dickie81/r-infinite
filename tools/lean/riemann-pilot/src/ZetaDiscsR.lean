import Mathlib
import ZetaDiscs

/-! # Zeros of ζ in discs of radius 2 − σ₀ about 2 + it (round 402)

Round 401's `ZetaDiscs` with the radius `4/3` replaced by `2 − σ₀`, so that the discs reach `Re s = σ₀` for any
`σ₀ ∈ (0, 2)`. For `|t₀| ≥ 4` the closed disc of radius `2 − σ₀` about `2 + it₀` avoids the pole, and
`|ζ(2 + it₀)| ≥ 2 − π²/6` (`ZetaDiscs.norm_zeta_two_ge`).

* **`cell_bound_R`**: for `0 < σ₀ < σ₁ < 1`, `λ ≥ 1`, a window `[u, v]` with `4 ≤ u` or `v ≤ −4`, and every `t₀` in
  both the window and `[a, a + h]`, `h = σ₁ − σ₀`, the zeros with `β ≥ σ₁` and `γ ∈ [a, a + h)`, counted with
  multiplicity, number at most `(½ log λ + A(t₀)/(2λ) + C₀)/L`. Here `A(t₀)` is the average of `|ζ|²` on the circle of
  radius `2 − σ₀` about `2 + it₀` (`avgOnCircleR`), `L = log((2 − σ₀)/r)` with `r² = (2 − σ₁)² + h²` (`logRadii`,
  `innerR`), and `C₀ = −log(2 − π²/6)` (`ZetaDiscs.CZ`).
* **`integral_avgOnCircleR_le`**: for `0 < σ₀ < 2` and a window `[u, v]` with `4 ≤ u` or `v ≤ −4`, `∫_u^v A ≤ B`
  whenever `∫|ζ(σ+it)|² dt ≤ B` over `t ∈ [u − (2 − σ₀), v + (2 − σ₀)]` for every `σ ∈ [σ₀, 4 − σ₀]`.
-/

open Real Complex Metric Set Filter MeromorphicOn MeasureTheory
open scoped Topology

noncomputable section

namespace ZetaDiscsR

open Pilot1bt Pilot1ca ZetaDiscs

/-- The cell height `h = σ₁ − σ₀`. -/
def cellH (σ₀ σ₁ : ℝ) : ℝ := σ₁ - σ₀

/-- The inner radius `r = √((2 − σ₁)² + h²)`. -/
def innerR (σ₀ σ₁ : ℝ) : ℝ := Real.sqrt ((2 - σ₁) ^ 2 + cellH σ₀ σ₁ ^ 2)

/-- `L = log((2 − σ₀)/r)`. -/
def logRadii (σ₀ σ₁ : ℝ) : ℝ := Real.log ((2 - σ₀) / innerR σ₀ σ₁)

lemma cellH_pos {σ₀ σ₁ : ℝ} (h : σ₀ < σ₁) : 0 < cellH σ₀ σ₁ := by unfold cellH; linarith

lemma innerR_pos {σ₀ σ₁ : ℝ} (h : σ₁ < 2) : 0 < innerR σ₀ σ₁ :=
  Real.sqrt_pos.2 (by have : 0 < 2 - σ₁ := by linarith
                      positivity)

/-- `r < 2 − σ₀`: `(2 − σ₀)² − r² = 2(σ₁ − σ₀)(2 − σ₁) > 0`. -/
lemma innerR_lt {σ₀ σ₁ : ℝ} (h1 : σ₀ < σ₁) (h2 : σ₁ < 2) : innerR σ₀ σ₁ < 2 - σ₀ := by
  rw [innerR, cellH, Real.sqrt_lt' (by linarith)]
  nlinarith [mul_pos (show (0 : ℝ) < σ₁ - σ₀ by linarith) (show (0 : ℝ) < 2 - σ₁ by linarith)]

lemma logRadii_pos {σ₀ σ₁ : ℝ} (h1 : σ₀ < σ₁) (h2 : σ₁ < 2) : 0 < logRadii σ₀ σ₁ := by
  apply Real.log_pos
  rw [lt_div_iff₀ (innerR_pos h2)]
  linarith [innerR_lt h1 h2]

lemma circleMap_ne_one_R {σ₀ u v t θ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀2 : σ₀ < 2) (huv : u ≤ v)
    (hwin : 4 ≤ u ∨ v ≤ -4) :
    circleMap (2 + (clampT u v t : ℂ) * I) (2 - σ₀) θ ≠ 1 := by
  intro h
  rw [circleMap_eq] at h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im, add_zero] at him
  have hc := abs_ge_of_win hwin (clampT_mem huv t)
  have hs := Real.abs_sin_le_one θ
  have hR : 0 < 2 - σ₀ := by linarith
  have : |clampT u v t| ≤ (2 - σ₀) * |Real.sin θ| := by
    have e : clampT u v t = -((2 - σ₀) * Real.sin θ) := by linarith
    rw [e, abs_neg, abs_mul, abs_of_pos hR]
  have h1 : (2 - σ₀) * |Real.sin θ| ≤ (2 - σ₀) * 1 := mul_le_mul_of_nonneg_left hs hR.le
  linarith

/-- `|ζ|²` on the circle of radius `2 − σ₀` about `2 + i·clamp(t)`. -/
def sqOnCircleR (σ₀ u v t θ : ℝ) : ℝ :=
  ‖riemannZeta (circleMap (2 + (clampT u v t : ℂ) * I) (2 - σ₀) θ)‖ ^ 2

/-- Its circle average. -/
def avgOnCircleR (σ₀ u v t : ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, sqOnCircleR σ₀ u v t θ

lemma continuous_sqOnCircleR {σ₀ u v : ℝ} (hσ₀ : 0 < σ₀) (hσ₀2 : σ₀ < 2) (huv : u ≤ v)
    (hwin : 4 ≤ u ∨ v ≤ -4) :
    Continuous (Function.uncurry (sqOnCircleR σ₀ u v)) := by
  have hin : Continuous fun p : ℝ × ℝ => circleMap (2 + (clampT u v p.1 : ℂ) * I) (2 - σ₀) p.2 := by
    have hc := continuous_clampT u v
    simp only [circleMap]
    fun_prop
  have hz : Continuous fun p : ℝ × ℝ =>
      riemannZeta (circleMap (2 + (clampT u v p.1 : ℂ) * I) (2 - σ₀) p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ContinuousAt.comp (g := riemannZeta)
      (differentiableAt_riemannZeta (circleMap_ne_one_R hσ₀ hσ₀2 huv hwin)).continuousAt hin.continuousAt
  exact hz.norm.pow 2

lemma continuous_avgOnCircleR {σ₀ u v : ℝ} (hσ₀ : 0 < σ₀) (hσ₀2 : σ₀ < 2) (huv : u ≤ v)
    (hwin : 4 ≤ u ∨ v ≤ -4) : Continuous (avgOnCircleR σ₀ u v) :=
  continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_sqOnCircleR hσ₀ hσ₀2 huv hwin) _ _)

lemma avgOnCircleR_eq {σ₀ u v t : ℝ} (ht : t ∈ Icc u v) :
    avgOnCircleR σ₀ u v t = circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) (2 - σ₀) := by
  rw [circleAverage_def, smul_eq_mul, avgOnCircleR]
  simp only [sqOnCircleR, clampT_of_mem ht]

/-- **One cell, radius `2 − σ₀`.** For `t₀` in the window and in a cell `[a, a + h]`, `h = σ₁ − σ₀`, the zeros with
`β ≥ σ₁` and `γ ∈ [a, a + h)`, counted with multiplicity, number at most `(½ log λ + avgOnCircleR(t₀)/(2λ) + C₀)/L`. -/
theorem cell_bound_R {σ₀ σ₁ lam u v t₀ a : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1)
    (hlam : 1 ≤ lam) (hwin : 4 ≤ u ∨ v ≤ -4) (ht₀ : t₀ ∈ Icc u v)
    (hat : t₀ ∈ Icc a (a + cellH σ₀ σ₁)) :
    (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        (zetaZeroFamily p).im ∈ Ico a (a + cellH σ₀ σ₁)} : ℝ) * logRadii σ₀ σ₁
      ≤ Real.log lam / 2 + avgOnCircleR σ₀ u v t₀ / (2 * lam) + CZ := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have ht0 : 4 ≤ |t₀| := abs_ge_of_win hwin ht₀
  have h1R : (1 : ℂ) ∉ closedBall c (2 - σ₀) := by
    intro h
    rw [mem_closedBall, Complex.dist_eq] at h
    have him : (1 - c).im = -t₀ := by simp [hc]
    have := Complex.abs_im_le_norm (1 - c)
    rw [him, abs_neg] at this
    linarith
  have hr0 := innerR_pos (σ₀ := σ₀) (show σ₁ < 2 by linarith)
  have hrR := innerR_lt hσ (show σ₁ < 2 by linarith)
  have h1r : (1 : ℂ) ∉ closedBall c (innerR σ₀ σ₁) := fun h =>
    h1R (closedBall_subset_closedBall hrR.le h)
  obtain ⟨hfin, hcount⟩ := ncard_zeros_ball_le h1r
  have hsub : {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ (zetaZeroFamily p).im ∈ Ico a (a + cellH σ₀ σ₁)}
      ⊆ {p : ZIdx | zetaZeroFamily p ∈ closedBall c (innerR σ₀ σ₁)} := by
    rintro p ⟨hre, him⟩
    have hlt : (zetaZeroFamily p).re < 1 := p.1.2.re_lt_one
    simp only [Set.mem_ofPred_eq, mem_closedBall, Complex.dist_eq]
    rw [innerR, Real.le_sqrt (norm_nonneg _) (by positivity), Complex.sq_norm, Complex.normSq_apply]
    simp only [hc, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, Complex.re_ofNat,
      Complex.im_ofNat]
    have h1 : ((zetaZeroFamily p).re - 2) * ((zetaZeroFamily p).re - 2) ≤ (2 - σ₁) ^ 2 := by
      nlinarith
    have h2 : ((zetaZeroFamily p).im - t₀) * ((zetaZeroFamily p).im - t₀) ≤ cellH σ₀ σ₁ ^ 2 := by
      have := him.1; have := him.2; have := hat.1; have := hat.2
      nlinarith
    linarith
  have hle : (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
      (zetaZeroFamily p).im ∈ Ico a (a + cellH σ₀ σ₁)} : ℝ)
        ≤ ∑ᶠ u, (divisor riemannZeta (closedBall c (innerR σ₀ σ₁)) u : ℝ) :=
    (Nat.cast_le.2 (Set.ncard_le_ncard hsub hfin)).trans hcount
  have hc0 : riemannZeta c ≠ 0 := by
    intro h0
    have := norm_zeta_two_ge t₀
    rw [← hc, h0, norm_zero] at this
    linarith [two_sub_pi_sq_pos]
  have hJ := JensenAvg.sum_divisor_mul_log_le hr0 hrR hlam (analyticOnNhd_zeta h1R) hc0
  have hz := norm_zeta_two_ge t₀
  have hlogz : -Real.log ‖riemannZeta c‖ ≤ CZ := by
    unfold CZ
    have := Real.log_le_log two_sub_pi_sq_pos hz
    linarith
  rw [avgOnCircleR_eq ht₀]
  have hL := logRadii_pos hσ (show σ₁ < 2 by linarith)
  calc (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        (zetaZeroFamily p).im ∈ Ico a (a + cellH σ₀ σ₁)} : ℝ) * logRadii σ₀ σ₁
      ≤ (∑ᶠ u, (divisor riemannZeta (closedBall c (innerR σ₀ σ₁)) u : ℝ)) * logRadii σ₀ σ₁ :=
        mul_le_mul_of_nonneg_right hle hL.le
    _ ≤ Real.log lam / 2 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) c (2 - σ₀) / (2 * lam)
          - Real.log ‖riemannZeta c‖ := hJ
    _ ≤ _ := by rw [hc]; linarith

/-- **Fubini, radius `2 − σ₀`**: the integral of `avgOnCircleR` over the window is at most any bound `B` on the mean
squares of `ζ` over the vertical segments `σ ∈ [σ₀, 4 − σ₀]`, `t ∈ [u − (2 − σ₀), v + (2 − σ₀)]`. -/
theorem integral_avgOnCircleR_le {σ₀ u v B : ℝ} (hσ₀ : 0 < σ₀) (hσ₀2 : σ₀ < 2) (huv : u ≤ v)
    (hwin : 4 ≤ u ∨ v ≤ -4)
    (hMS : ∀ σ ∈ Icc σ₀ (4 - σ₀),
      ∫ t in (u - (2 - σ₀))..(v + (2 - σ₀)), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B) :
    ∫ t in u..v, avgOnCircleR σ₀ u v t ≤ B := by
  have hG := continuous_sqOnCircleR hσ₀ hσ₀2 huv hwin
  have h2π : (0 : ℝ) ≤ 2 * π := two_pi_pos.le
  have hR : 0 < 2 - σ₀ := by linarith
  have hswap : ∫ t in u..v, ∫ θ in (0 : ℝ)..2 * π, sqOnCircleR σ₀ u v t θ
      = ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircleR σ₀ u v t θ := intervalIntegral_swap hG huv h2π
  have hne : ∀ σ : ℝ, ∀ t ∈ Icc (u - (2 - σ₀)) (v + (2 - σ₀)), (σ : ℂ) + t * I ≠ 1 := by
    intro σ t ht h
    have := congrArg Complex.im h
    simp at this
    rcases hwin with hw | hw
    · linarith [ht.1]
    · linarith [ht.2]
  have hinner : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∫ t in u..v, sqOnCircleR σ₀ u v t θ ≤ B := by
    intro θ _
    set σθ : ℝ := 2 + (2 - σ₀) * Real.cos θ with hσθ
    set d : ℝ := (2 - σ₀) * Real.sin θ with hd
    set f : ℝ → ℝ := fun s => ‖riemannZeta ((σθ : ℂ) + (s : ℂ) * I)‖ ^ 2 with hf
    have hcongr : ∫ t in u..v, sqOnCircleR σ₀ u v t θ = ∫ t in u..v, f (t + d) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le huv] at ht
      simp only [sqOnCircleR, clampT_of_mem ht, hf, circleMap_eq, hσθ, hd]
    rw [hcongr, intervalIntegral.integral_comp_add_right f d]
    have hcos1 := Real.neg_one_le_cos θ
    have hcos2 := Real.cos_le_one θ
    have hc1 : (2 - σ₀) * (-1) ≤ (2 - σ₀) * Real.cos θ := mul_le_mul_of_nonneg_left hcos1 hR.le
    have hc2 : (2 - σ₀) * Real.cos θ ≤ (2 - σ₀) * 1 := mul_le_mul_of_nonneg_left hcos2 hR.le
    have hσ : σθ ∈ Icc σ₀ (4 - σ₀) := ⟨by rw [hσθ]; linarith, by rw [hσθ]; linarith⟩
    have hd1 : |d| ≤ 2 - σ₀ := by
      rw [hd, abs_mul, abs_of_pos hR]
      have := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hR.le
      linarith
    have hfcont : ContinuousOn f (Icc (u - (2 - σ₀)) (v + (2 - σ₀))) := by
      intro t ht
      have hin : Continuous fun s : ℝ => (σθ : ℂ) + (s : ℂ) * I := by fun_prop
      exact ((ContinuousAt.comp (g := riemannZeta) (f := fun s : ℝ => (σθ : ℂ) + (s : ℂ) * I)
        (differentiableAt_riemannZeta (hne σθ t ht)).continuousAt hin.continuousAt).norm.pow
          2).continuousWithinAt
    have hle1 : u - (2 - σ₀) ≤ u + d := by linarith [neg_abs_le d]
    have hle2 : v + d ≤ v + (2 - σ₀) := by linarith [le_abs_self d]
    have hmono : ∫ t in (u + d)..(v + d), f t ≤ ∫ t in (u - (2 - σ₀))..(v + (2 - σ₀)), f t := by
      refine intervalIntegral.integral_mono_interval hle1 (by linarith) hle2
        (Eventually.of_forall fun t => by simp only [hf]; positivity) ?_
      exact (uIcc_of_le (by linarith : u - (2 - σ₀) ≤ v + (2 - σ₀)) ▸ hfcont).intervalIntegrable
    exact hmono.trans (hMS σθ hσ)
  have hint : IntervalIntegrable (fun θ => ∫ t in u..v, sqOnCircleR σ₀ u v t θ) volume 0 (2 * π) := by
    have hG' : Continuous (Function.uncurry fun θ t => sqOnCircleR σ₀ u v t θ) := by
      have h := hG.comp continuous_swap
      exact h
    have : Continuous fun θ => ∫ t in u..v, sqOnCircleR σ₀ u v t θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG' _ _
    exact this.intervalIntegrable _ _
  have hbound : ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircleR σ₀ u v t θ
      ≤ ∫ θ in (0 : ℝ)..2 * π, B :=
    intervalIntegral.integral_mono_on h2π hint intervalIntegrable_const hinner
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hbound
  have e : ∫ t in u..v, avgOnCircleR σ₀ u v t
      = (2 * π)⁻¹ * ∫ t in u..v, ∫ θ in (0 : ℝ)..2 * π, sqOnCircleR σ₀ u v t θ := by
    simp only [avgOnCircleR]
    exact intervalIntegral.integral_const_mul _ _
  rw [e, hswap]
  have hπ : 0 < 2 * π := two_pi_pos
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircleR σ₀ u v t θ
      ≤ (2 * π)⁻¹ * (2 * π * B) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hπ.le)
    _ = B := by field_simp

end ZetaDiscsR

#print axioms ZetaDiscsR.innerR_lt
#print axioms ZetaDiscsR.logRadii_pos
#print axioms ZetaDiscsR.circleMap_ne_one_R
#print axioms ZetaDiscsR.continuous_sqOnCircleR
#print axioms ZetaDiscsR.continuous_avgOnCircleR
#print axioms ZetaDiscsR.avgOnCircleR_eq
#print axioms ZetaDiscsR.cell_bound_R
#print axioms ZetaDiscsR.integral_avgOnCircleR_le
