import Mathlib
import JensenAvg
import ZetaInputs

/-! # Zeros of ζ in discs about 2 + it, by Jensen's formula (round 401)

For `|t₀| ≥ 4` the closed disc of radius `4/3` about `c = 2 + it₀` avoids the pole and reaches `Re s = 2/3`, and
`|ζ(c)| ≥ 2 − π²/6`. Jensen's formula with an averaged majorant (`JensenAvg`) bounds the number of zeros with
`β ≥ σ₁` in a cell of height `h = σ₁ − 2/3` near `t₀` through the average of `|ζ|²` on the circle of radius `4/3`;
Fubini turns these circle averages, integrated over the centres, into mean squares on vertical segments.

* **`norm_zeta_two_ge`**: `|ζ(2 + it)| ≥ 2 − π²/6`.
* **`ncard_zeros_ball_le`**: the zeros of `ζ` in a closed disc avoiding `1`, counted with multiplicity, are finitely
  many, and their number is at most the divisor sum of Jensen's formula.
* **`cell_bound`**: for `σ₁ ∈ (2/3, 1)`, `λ ≥ 1`, a window `[u, v]` with `4 ≤ u` or `v ≤ −4`, and every `t₀` in both
  the window and `[a, a + h]`, the zeros with `β ≥ σ₁` and `γ ∈ [a, a + h)`, counted with multiplicity, number at
  most `(½ log λ + A(t₀)/(2λ) + C₀)/L`. Here `A(t₀)` is the average of `|ζ|²` on the circle of radius `4/3` about
  `2 + it₀` (`avgOnCircle`), `L = log((4/3)/r)` with `r² = (2 − σ₁)² + h²`, and `C₀ = −log(2 − π²/6)` (`CZ`).
* **`integral_avgOnCircle_le`**: for a window `[u, v]` with `4 ≤ u` or `v ≤ −4`, `∫_u^v A ≤ B` whenever
  `∫_{u−4/3}^{v+4/3} |ζ(σ+it)|² dt ≤ B` for every `σ ∈ [2/3, 10/3]`.
-/

open Real Complex Metric Set Filter MeromorphicOn MeasureTheory
open scoped Topology

noncomputable section

namespace ZetaDiscs

open Pilot1bt Pilot1ca

/-- `ζ` has finite order at every point other than `1`. -/
theorem analyticOrderAt_zeta_ne_top {z : ℂ} (h1 : z ≠ 1) : analyticOrderAt riemannZeta z ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [ne_eq, analyticOrderAt_eq_zero.2 (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected h2 h1 hord2

/-- `ζ` is analytic on every closed disc that avoids `1`. -/
theorem analyticOnNhd_zeta {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r) :
    AnalyticOnNhd ℂ riemannZeta (closedBall c r) :=
  analyticOn_riemannZeta.mono fun z hz => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact h1 hz

/-- `2 − π²/6 > 0`. -/
theorem two_sub_pi_sq_pos : 0 < 2 - π ^ 2 / 6 := by
  have := Real.pi_lt_d2; nlinarith [Real.pi_pos]

/-- **`|ζ(2 + it)| ≥ 2 − π²/6`**: `|ζ(s) − 1| ≤ Σ_{n≥2} n^{−2} = π²/6 − 1` on `Re s = 2`. -/
theorem norm_zeta_two_ge (t : ℝ) : 2 - π ^ 2 / 6 ≤ ‖riemannZeta (2 + t * I)‖ := by
  set s : ℂ := 2 + t * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; norm_num
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ = ((n : ℝ) + 1)⁻¹ ^ 2 := by
    intro n
    have h := Complex.norm_natCast_cpow_of_pos (n := n + 1) (by omega) s
    push_cast at h
    rw [norm_div, norm_one, h, hsre, inv_pow, one_div]
    norm_num
  have hR : HasSum (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2) (π ^ 2 / 6) := by
    have h := hasSum_zeta_two
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [Finset.sum_range_one, one_div, inv_pow] using h
  have hR1 : HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2) (π ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 hR
    simpa [Finset.sum_range_one] using h
  have hsumC : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) :=
    Summable.of_norm (by simpa only [hnorm] using hR.summable)
  rw [hsumC.tsum_eq_zero_add]
  have h0 : 1 / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by simp
  rw [h0]
  set X := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s with hX
  have hXn : ‖X‖ ≤ π ^ 2 / 6 - 1 := by
    have hs' : Summable (fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖) := by
      simpa only [hnorm] using hR1.summable
    refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq ?_)
    rw [← hR1.tsum_eq]
    exact tsum_congr fun n => hnorm (n + 1)
  have := norm_sub_le (1 + X) X
  rw [add_sub_cancel_right, norm_one] at this
  linarith

/-- **The zeros of `ζ` in a closed disc avoiding `1`, counted with multiplicity**, are finitely many and
their number is at most the divisor sum of Jensen's formula. -/
theorem ncard_zeros_ball_le {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r) :
    {p : ZIdx | zetaZeroFamily p ∈ closedBall c r}.Finite ∧
      (Set.ncard {p : ZIdx | zetaZeroFamily p ∈ closedBall c r} : ℝ)
        ≤ ∑ᶠ u, (divisor riemannZeta (closedBall c r) u : ℝ) := by
  set B := closedBall c r with hB
  have han : AnalyticOnNhd ℂ riemannZeta B := analyticOnNhd_zeta h1
  set D := divisor riemannZeta B with hDdef
  have hfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall c r)
  have hD : ∀ z : NontrivialZero, z.1 ∈ B → D z.1 = (zeroMult z : ℤ) := by
    intro z hz
    rw [hDdef, AnalyticOnNhd.divisor_apply han hz]
    have hz1 : z.1 ≠ 1 := fun h => h1 (h ▸ hz)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_zeta_ne_top hz1)
    unfold zeroMult
    rw [← hm]
    simp
  set ZN : Set NontrivialZero := {z | z.1 ∈ B} with hZNdef
  have hZN : ZN.Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun z hz => ?_
    simp only [Set.mem_preimage, Function.mem_support]
    rw [hD z hz]
    exact_mod_cast (zeroMult_pos z).ne'
  set F := hZN.toFinset with hF
  have hset : {p : ZIdx | zetaZeroFamily p ∈ B}
      = ↑(F.sigma fun z => (Finset.univ : Finset (Fin (zeroMult z)))) := by
    ext p
    simp [hF, hZNdef, zetaZeroFamily]
  refine ⟨by rw [hset]; exact Finset.finite_toSet _, ?_⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  have hsupp : Function.support (fun u => (D u : ℝ)) ⊆ (hfin.toFinset : Set ℂ) := by
    intro u hu
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu
    simpa using hu
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  let emb : NontrivialZero ↪ ℂ :=
    ⟨fun z => (z : {s : ℂ // IsNontrivialZero s}).1, fun a b h => Subtype.ext h⟩
  have hmap : ∑ z ∈ F, (zeroMult z : ℝ) = ∑ u ∈ F.map emb, (D u : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzB : z.1 ∈ B := by simpa [hF, hZNdef] using hz
    show (zeroMult z : ℝ) = (D z.1 : ℝ)
    rw [hD z hzB]
    push_cast; rfl
  rw [hmap]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => ?_
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.1 hu
    have hzB : z.1 ∈ B := by simpa [hF, hZNdef] using hz
    simp only [Set.Finite.mem_toFinset, Function.mem_support]
    show D z.1 ≠ 0
    rw [hD z hzB]
    exact_mod_cast (zeroMult_pos z).ne'
  · exact_mod_cast han.divisor_nonneg u



/-- The cell width `h = σ₁ − 2/3`. -/
def hS (σ₁ : ℝ) : ℝ := σ₁ - 2 / 3

/-- The inner radius `r = √((2 − σ₁)² + h²)`. -/
def rS (σ₁ : ℝ) : ℝ := Real.sqrt ((2 - σ₁) ^ 2 + hS σ₁ ^ 2)

/-- `L = log((4/3)/r)`. -/
def LS (σ₁ : ℝ) : ℝ := Real.log ((4 / 3) / rS σ₁)

/-- `C₀ = −log(2 − π²/6)`, so that `−log|ζ(2 + it)| ≤ C₀`. -/
def CZ : ℝ := -Real.log (2 - π ^ 2 / 6)

lemma hS_pos {σ₁ : ℝ} (h : 2 / 3 < σ₁) : 0 < hS σ₁ := by unfold hS; linarith

lemma rS_pos {σ₁ : ℝ} (h : σ₁ < 2) : 0 < rS σ₁ :=
  Real.sqrt_pos.2 (by have : 0 < 2 - σ₁ := by linarith
                      positivity)

lemma rS_lt {σ₁ : ℝ} (h1 : 2 / 3 < σ₁) (h2 : σ₁ < 1) : rS σ₁ < 4 / 3 := by
  rw [rS, hS, Real.sqrt_lt' (by norm_num)]
  nlinarith [mul_pos (show (0 : ℝ) < σ₁ - 2 / 3 by linarith) (show (0 : ℝ) < 2 - σ₁ by linarith)]

lemma LS_pos {σ₁ : ℝ} (h1 : 2 / 3 < σ₁) (h2 : σ₁ < 1) : 0 < LS σ₁ := by
  apply Real.log_pos
  rw [lt_div_iff₀ (rS_pos (by linarith))]
  linarith [rS_lt h1 h2]

/-- Clamp into `[u, v]`. -/
def clampT (u v t : ℝ) : ℝ := max u (min t v)

lemma clampT_mem {u v : ℝ} (huv : u ≤ v) (t : ℝ) : clampT u v t ∈ Icc u v :=
  ⟨le_max_left _ _, max_le huv (min_le_right _ _)⟩

lemma clampT_of_mem {u v t : ℝ} (ht : t ∈ Icc u v) : clampT u v t = t := by
  unfold clampT
  rw [min_eq_left ht.2, max_eq_right ht.1]

lemma continuous_clampT (u v : ℝ) : Continuous (clampT u v) := by
  unfold clampT; fun_prop

lemma abs_ge_of_win {u v t : ℝ} (hwin : 4 ≤ u ∨ v ≤ -4) (ht : t ∈ Icc u v) : 4 ≤ |t| := by
  rcases hwin with h | h
  · rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
  · rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]

/-- The circle about `2 + it` in coordinates. -/
lemma circleMap_eq (t R θ : ℝ) :
    circleMap (2 + (t : ℂ) * I) R θ
      = ((2 + R * Real.cos θ : ℝ) : ℂ) + ((t + R * Real.sin θ : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.cos_ofReal_re]
  · simp [circleMap, Complex.exp_ofReal_mul_I_im, Complex.sin_ofReal_re]

lemma circleMap_ne_one {u v t θ : ℝ} (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4) :
    circleMap (2 + (clampT u v t : ℂ) * I) (4 / 3) θ ≠ 1 := by
  intro h
  rw [circleMap_eq] at h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im, add_zero] at him
  have hc := abs_ge_of_win hwin (clampT_mem huv t)
  have hs := Real.abs_sin_le_one θ
  have : |clampT u v t| ≤ 4 / 3 * |Real.sin θ| := by
    have e : clampT u v t = -(4 / 3 * Real.sin θ) := by linarith
    rw [e, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  nlinarith

/-- `|ζ|²` on the circle of radius `4/3` about `2 + i·clamp(t)`. -/
def sqOnCircle (u v t θ : ℝ) : ℝ := ‖riemannZeta (circleMap (2 + (clampT u v t : ℂ) * I) (4 / 3) θ)‖ ^ 2

/-- Its circle average. -/
def avgOnCircle (u v t : ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, sqOnCircle u v t θ

lemma continuous_sqOnCircle {u v : ℝ} (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4) :
    Continuous (Function.uncurry (sqOnCircle u v)) := by
  have hin : Continuous fun p : ℝ × ℝ => circleMap (2 + (clampT u v p.1 : ℂ) * I) (4 / 3) p.2 := by
    have hc := continuous_clampT u v
    simp only [circleMap]
    fun_prop
  have hz : Continuous fun p : ℝ × ℝ =>
      riemannZeta (circleMap (2 + (clampT u v p.1 : ℂ) * I) (4 / 3) p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ContinuousAt.comp (g := riemannZeta)
      (differentiableAt_riemannZeta (circleMap_ne_one huv hwin)).continuousAt hin.continuousAt
  exact hz.norm.pow 2

lemma continuous_avgOnCircle {u v : ℝ} (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4) : Continuous (avgOnCircle u v) :=
  continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (continuous_sqOnCircle huv hwin) _ _)

lemma avgOnCircle_eq {u v t : ℝ} (ht : t ∈ Icc u v) :
    avgOnCircle u v t = circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) (4 / 3) := by
  rw [circleAverage_def, smul_eq_mul, avgOnCircle]
  simp only [sqOnCircle, clampT_of_mem ht]

/-- **One cell.** For `t₀` in the window and in a cell `[a, a + h]`, the zeros with `β ≥ σ₁` and
`γ ∈ [a, a + h)`, counted with multiplicity, number at most `(½ log λ + avgOnCircle(t₀)/(2λ) + C₀)/L`. -/
theorem cell_bound {σ₁ lam u v t₀ a : ℝ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)
    (hwin : 4 ≤ u ∨ v ≤ -4) (ht₀ : t₀ ∈ Icc u v) (hat : t₀ ∈ Icc a (a + hS σ₁)) :
    (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        (zetaZeroFamily p).im ∈ Ico a (a + hS σ₁)} : ℝ) * LS σ₁
      ≤ Real.log lam / 2 + avgOnCircle u v t₀ / (2 * lam) + CZ := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have ht0 : 4 ≤ |t₀| := abs_ge_of_win hwin ht₀
  have h1R : (1 : ℂ) ∉ closedBall c (4 / 3) := by
    intro h
    rw [mem_closedBall, Complex.dist_eq] at h
    have him : (1 - c).im = -t₀ := by simp [hc]
    have := Complex.abs_im_le_norm (1 - c)
    rw [him, abs_neg] at this
    linarith
  have hr0 := rS_pos (show σ₁ < 2 by linarith)
  have hrR := rS_lt hσ hσ'
  have h1r : (1 : ℂ) ∉ closedBall c (rS σ₁) := fun h =>
    h1R (closedBall_subset_closedBall hrR.le h)
  obtain ⟨hfin, hcount⟩ := ncard_zeros_ball_le h1r
  have hsub : {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ (zetaZeroFamily p).im ∈ Ico a (a + hS σ₁)}
      ⊆ {p : ZIdx | zetaZeroFamily p ∈ closedBall c (rS σ₁)} := by
    rintro p ⟨hre, him⟩
    have hlt : (zetaZeroFamily p).re < 1 := p.1.2.re_lt_one
    simp only [Set.mem_ofPred_eq, mem_closedBall, Complex.dist_eq]
    rw [rS, Real.le_sqrt (norm_nonneg _) (by positivity), Complex.sq_norm, Complex.normSq_apply]
    simp only [hc, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, Complex.re_ofNat,
      Complex.im_ofNat]
    have h1 : ((zetaZeroFamily p).re - 2) * ((zetaZeroFamily p).re - 2) ≤ (2 - σ₁) ^ 2 := by
      nlinarith
    have h2 : ((zetaZeroFamily p).im - t₀) * ((zetaZeroFamily p).im - t₀) ≤ hS σ₁ ^ 2 := by
      have := him.1; have := him.2; have := hat.1; have := hat.2
      nlinarith
    linarith
  have hle : (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
      (zetaZeroFamily p).im ∈ Ico a (a + hS σ₁)} : ℝ)
        ≤ ∑ᶠ u, (divisor riemannZeta (closedBall c (rS σ₁)) u : ℝ) :=
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
  rw [avgOnCircle_eq ht₀]
  have hL := LS_pos hσ hσ'
  calc (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        (zetaZeroFamily p).im ∈ Ico a (a + hS σ₁)} : ℝ) * LS σ₁
      ≤ (∑ᶠ u, (divisor riemannZeta (closedBall c (rS σ₁)) u : ℝ)) * LS σ₁ :=
        mul_le_mul_of_nonneg_right hle hL.le
    _ ≤ Real.log lam / 2 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) c (4 / 3) / (2 * lam)
          - Real.log ‖riemannZeta c‖ := hJ
    _ ≤ _ := by rw [hc]; linarith

/-- Interval integrals of a continuous function of two variables commute. -/
lemma intervalIntegral_swap {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine MeasureTheory.integral_integral_swap ?_
  have hon : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hon.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- **Fubini**: the integral of `avgOnCircle` over the window is at most any bound `B` on the mean squares of `ζ`
over the vertical segments `σ ∈ [2/3, 10/3]`, `t ∈ [u − 4/3, v + 4/3]`. -/
theorem integral_avgOnCircle_le {u v B : ℝ} (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4)
    (hMS : ∀ σ ∈ Icc (2 / 3 : ℝ) (10 / 3),
      ∫ t in (u - 4 / 3)..(v + 4 / 3), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B) :
    ∫ t in u..v, avgOnCircle u v t ≤ B := by
  have hG := continuous_sqOnCircle huv hwin
  have h2π : (0 : ℝ) ≤ 2 * π := two_pi_pos.le
  have hswap : ∫ t in u..v, ∫ θ in (0 : ℝ)..2 * π, sqOnCircle u v t θ
      = ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircle u v t θ := intervalIntegral_swap hG huv h2π
  have hne : ∀ σ : ℝ, ∀ t ∈ Icc (u - 4 / 3) (v + 4 / 3), (σ : ℂ) + t * I ≠ 1 := by
    intro σ t ht h
    have := congrArg Complex.im h
    simp at this
    rcases hwin with hw | hw
    · linarith [ht.1]
    · linarith [ht.2]
  have hinner : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∫ t in u..v, sqOnCircle u v t θ ≤ B := by
    intro θ _
    set σθ : ℝ := 2 + 4 / 3 * Real.cos θ with hσθ
    set d : ℝ := 4 / 3 * Real.sin θ with hd
    set f : ℝ → ℝ := fun s => ‖riemannZeta ((σθ : ℂ) + (s : ℂ) * I)‖ ^ 2 with hf
    have hcongr : ∫ t in u..v, sqOnCircle u v t θ = ∫ t in u..v, f (t + d) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le huv] at ht
      simp only [sqOnCircle, clampT_of_mem ht, hf, circleMap_eq, hσθ, hd]
    rw [hcongr, intervalIntegral.integral_comp_add_right f d]
    have hσ : σθ ∈ Icc (2 / 3 : ℝ) (10 / 3) := by
      have := Real.neg_one_le_cos θ; have := Real.cos_le_one θ
      constructor <;> simp only [hσθ] <;> linarith
    have hd1 : |d| ≤ 4 / 3 := by
      rw [hd, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
      have := Real.abs_sin_le_one θ
      nlinarith
    have hfcont : ContinuousOn f (Icc (u - 4 / 3) (v + 4 / 3)) := by
      intro t ht
      have hin : Continuous fun s : ℝ => (σθ : ℂ) + (s : ℂ) * I := by fun_prop
      exact ((ContinuousAt.comp (g := riemannZeta) (f := fun s : ℝ => (σθ : ℂ) + (s : ℂ) * I)
        (differentiableAt_riemannZeta (hne σθ t ht)).continuousAt hin.continuousAt).norm.pow
          2).continuousWithinAt
    have hle1 : u - 4 / 3 ≤ u + d := by linarith [neg_abs_le d]
    have hle2 : v + d ≤ v + 4 / 3 := by linarith [le_abs_self d]
    have hmono : ∫ t in (u + d)..(v + d), f t ≤ ∫ t in (u - 4 / 3)..(v + 4 / 3), f t := by
      refine intervalIntegral.integral_mono_interval hle1 (by linarith) hle2
        (Eventually.of_forall fun t => by simp only [hf]; positivity) ?_
      exact (uIcc_of_le (by linarith : u - 4 / 3 ≤ v + 4 / 3) ▸ hfcont).intervalIntegrable
    exact hmono.trans (hMS σθ hσ)
  have hint : IntervalIntegrable (fun θ => ∫ t in u..v, sqOnCircle u v t θ) volume 0 (2 * π) := by
    have hG' : Continuous (Function.uncurry fun θ t => sqOnCircle u v t θ) := by
      have h := hG.comp continuous_swap
      exact h
    have : Continuous fun θ => ∫ t in u..v, sqOnCircle u v t θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG' _ _
    exact this.intervalIntegrable _ _
  have hbound : ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircle u v t θ ≤ ∫ θ in (0 : ℝ)..2 * π, B :=
    intervalIntegral.integral_mono_on h2π hint intervalIntegrable_const hinner
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hbound
  have e : ∫ t in u..v, avgOnCircle u v t = (2 * π)⁻¹ * ∫ t in u..v, ∫ θ in (0 : ℝ)..2 * π, sqOnCircle u v t θ := by
    simp only [avgOnCircle]
    exact intervalIntegral.integral_const_mul _ _
  rw [e, hswap]
  have hπ : 0 < 2 * π := two_pi_pos
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ∫ t in u..v, sqOnCircle u v t θ ≤ (2 * π)⁻¹ * (2 * π * B) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hπ.le)
    _ = B := by field_simp

end ZetaDiscs

#print axioms ZetaDiscs.analyticOrderAt_zeta_ne_top
#print axioms ZetaDiscs.analyticOnNhd_zeta
#print axioms ZetaDiscs.two_sub_pi_sq_pos
#print axioms ZetaDiscs.norm_zeta_two_ge
#print axioms ZetaDiscs.ncard_zeros_ball_le
#print axioms ZetaDiscs.rS_lt
#print axioms ZetaDiscs.LS_pos
#print axioms ZetaDiscs.circleMap_eq
#print axioms ZetaDiscs.circleMap_ne_one
#print axioms ZetaDiscs.continuous_sqOnCircle
#print axioms ZetaDiscs.continuous_avgOnCircle
#print axioms ZetaDiscs.avgOnCircle_eq
#print axioms ZetaDiscs.cell_bound
#print axioms ZetaDiscs.intervalIntegral_swap
#print axioms ZetaDiscs.integral_avgOnCircle_le
