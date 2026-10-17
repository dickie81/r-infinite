import Mathlib
import MeanSquareHigh
import ZetaDiscsR
import ShellSixthCore

/-! # For every w > 0, almost every zero lies within w of the critical line (round 402)

Round 401's count, with discs of radius `2 − σ₀` (`ZetaDiscsR`) and the mean square of `MeanSquareHigh` in place of
the radius `4/3` and the mean square on `Re s ≥ 2/3`.

* **`window_zero_count_R`**: for `0 < σ₀ < σ₁ < 1`, `λ ≥ 1` and a window `[u, u + Kh)` with `4 ≤ u` or
  `u + Kh ≤ −4`, `h = σ₁ − σ₀`, the zeros with `β ≥ σ₁` and `γ` in the window, counted with multiplicity, are
  finitely many and number at most `(Kh(½ log λ + C₀) + B/(2λ))/(Lh)` when `B` bounds the mean square of `ζ` over
  `[u − (2 − σ₀), u + Kh + (2 − σ₀)]` for every `σ ∈ [σ₀, 4 − σ₀]`.
* **`count_bound_ms`**: from `MSPoly σ₀`, for `0 < σ₀ < σ₁ < 1`, some `C ≥ 0` has, for every `T ≥ 16`, the zeros with
  `β ≥ σ₁` and `|γ| ≤ T`, counted with multiplicity, at most `(3 T log log T + C T)/(Lh)`.
* **`tendsto_NX_div_of_msPoly`**: from `MSPoly σ₀` and a lower bound `c·T log T` for `NX 0 T`, `NX w T / NX 0 T → 0`
  for every `w > σ₀ − ½`.
* **`tendsto_NX_div_of_lower`**: from the lower bound alone, `NX w T / NX 0 T → 0` for every `w > 0`: with
  `K > 1/w`, `MeanSquareHigh.msPoly_of_order` gives `MSPoly σ₀` at `σ₀ = (2K+1)/(4K+1)`, and
  `σ₀ − ½ = 1/(2(4K+1)) < w`.

A proportion statement, for any `w`, allows a set of off-shell zeros of smaller order than the set of all zeros, so it
does not bear on RH.
-/

open Real Complex Metric Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace BohrLandauCore

open Pilot1bt Pilot1ca ShortWeil ZetaDiscs ZetaDiscsR ShellSixthCore MeanSquareHigh

/-- One cell of radius `2 − σ₀`, integrated over its centres. -/
theorem cell_int_R {σ₀ σ₁ lam u v a : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)
    (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4) (hua : u ≤ a) (hav : a + cellH σ₀ σ₁ ≤ v) :
    (ZW σ₁ a (a + cellH σ₀ σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ a (a + cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁ * cellH σ₀ σ₁
        ≤ cellH σ₀ σ₁ * (Real.log lam / 2 + CZ)
          + (2 * lam)⁻¹ * ∫ t in a..(a + cellH σ₀ σ₁), avgOnCircleR σ₀ u v t := by
  have hh := cellH_pos hσ
  have hσ₀2 : σ₀ < 2 := by linarith
  have hAc := continuous_avgOnCircleR hσ₀ hσ₀2 huv hwin
  have hfin : (ZW σ₁ a (a + cellH σ₀ σ₁)).Finite := by
    have ha : a ∈ Icc u v := ⟨hua, by linarith⟩
    have hrR := innerR_lt hσ (show σ₁ < 2 by linarith)
    have ht0 : 4 ≤ |a| := abs_ge_of_win hwin ha
    set c : ℂ := 2 + (a : ℂ) * I with hc
    have h1 : (1 : ℂ) ∉ closedBall c (innerR σ₀ σ₁) := by
      intro h
      rw [mem_closedBall, Complex.dist_eq] at h
      have him : (1 - c).im = -a := by simp [hc]
      have := Complex.abs_im_le_norm (1 - c)
      rw [him, abs_neg] at this
      linarith
    refine (ncard_zeros_ball_le h1).1.subset ?_
    rintro p ⟨hre, him⟩
    have hlt : (zetaZeroFamily p).re < 1 := p.1.2.re_lt_one
    simp only [Set.mem_ofPred_eq, mem_closedBall, Complex.dist_eq]
    rw [innerR, Real.le_sqrt (norm_nonneg _) (by positivity), Complex.sq_norm, Complex.normSq_apply]
    simp only [hc, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.re_ofNat, Complex.im_ofNat]
    have h1 : ((zetaZeroFamily p).re - 2) * ((zetaZeroFamily p).re - 2) ≤ (2 - σ₁) ^ 2 := by
      nlinarith
    have h2 : ((zetaZeroFamily p).im - a) * ((zetaZeroFamily p).im - a) ≤ cellH σ₀ σ₁ ^ 2 := by
      have := him.1; have := him.2
      nlinarith
    linarith
  refine ⟨hfin, ?_⟩
  have hpt : ∀ t ∈ Icc a (a + cellH σ₀ σ₁), (Set.ncard (ZW σ₁ a (a + cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁
      ≤ Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircleR σ₀ u v t := by
    intro t ht
    have := cell_bound_R hσ₀ hσ hσ' hlam hwin
      (show t ∈ Icc u v from ⟨hua.trans ht.1, ht.2.trans hav⟩) ht
    have e : avgOnCircleR σ₀ u v t / (2 * lam) = (2 * lam)⁻¹ * avgOnCircleR σ₀ u v t := by ring
    simp only [ZW] at this ⊢
    linarith
  have hi1 : IntervalIntegrable (fun _ : ℝ => (Set.ncard (ZW σ₁ a (a + cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁)
      volume a (a + cellH σ₀ σ₁) := intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun t => Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircleR σ₀ u v t)
      volume a (a + cellH σ₀ σ₁) := intervalIntegrable_const.add ((hAc.intervalIntegrable _ _).const_mul _)
  have hint := intervalIntegral.integral_mono_on (le_of_lt (by linarith : a < a + cellH σ₀ σ₁)) hi1 hi2 hpt
  have e1 : ∫ _ in a..(a + cellH σ₀ σ₁), (Set.ncard (ZW σ₁ a (a + cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁
      = cellH σ₀ σ₁ * ((Set.ncard (ZW σ₁ a (a + cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have e2 : ∫ t in a..(a + cellH σ₀ σ₁), (Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircleR σ₀ u v t)
      = cellH σ₀ σ₁ * (Real.log lam / 2 + CZ)
        + (2 * lam)⁻¹ * ∫ t in a..(a + cellH σ₀ σ₁), avgOnCircleR σ₀ u v t := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hAc.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul]
    ring
  rw [e1, e2] at hint
  linarith

/-- **A window `[u, u + Kh)` of radius-`(2 − σ₀)` cells**, by induction over the `K` cells. -/
theorem window_bound_R {σ₀ σ₁ lam u : ℝ} {K : ℕ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1)
    (hlam : 1 ≤ lam) (hwin : 4 ≤ u ∨ u + K * cellH σ₀ σ₁ ≤ -4) :
    (ZW σ₁ u (u + K * cellH σ₀ σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + K * cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁ * cellH σ₀ σ₁
        ≤ K * cellH σ₀ σ₁ * (Real.log lam / 2 + CZ)
          + (2 * lam)⁻¹ * ∫ t in u..(u + K * cellH σ₀ σ₁), avgOnCircleR σ₀ u (u + K * cellH σ₀ σ₁) t := by
  set h := cellH σ₀ σ₁ with hhdef
  set v := u + K * h with hv
  have hh0 : 0 < h := cellH_pos hσ
  have hσ₀2 : σ₀ < 2 := by linarith
  have huv : u ≤ v := by
    have : (0 : ℝ) ≤ K * h := by positivity
    linarith
  have hAc := continuous_avgOnCircleR hσ₀ hσ₀2 huv hwin
  have key : ∀ k : ℕ, k ≤ K → (ZW σ₁ u (u + k * h)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + k * h)) : ℝ) * logRadii σ₀ σ₁ * h
        ≤ k * h * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * ∫ t in u..(u + k * h), avgOnCircleR σ₀ u v t := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, add_zero, ZW_empty, Set.ncard_empty,
        intervalIntegral.integral_same, mul_zero]
      exact ⟨Set.finite_empty, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨hfin, hb⟩ := ih (by omega)
      have hk' : ((k : ℝ) + 1) * h + u ≤ v := by
        have : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hk
        rw [hv]; nlinarith
      have hstep : u + ((k + 1 : ℕ) : ℝ) * h = (u + k * h) + h := by push_cast; ring
      have hle1 : u ≤ u + k * h := by have : (0 : ℝ) ≤ k * h := by positivity
                                      linarith
      obtain ⟨hcf, hcb⟩ := cell_int_R hσ₀ hσ hσ' hlam huv hwin hle1 (by linarith)
      rw [hstep, ZW_union σ₁ u (u + k * h) (u + k * h + h) hle1 (by linarith)]
      refine ⟨hfin.union hcf, ?_⟩
      have hunion := Set.ncard_union_le (ZW σ₁ u (u + k * h)) (ZW σ₁ (u + k * h) (u + k * h + h))
      have hL := logRadii_pos hσ (show σ₁ < 2 by linarith)
      have hcast : (Set.ncard (ZW σ₁ u (u + k * h) ∪ ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ)
          ≤ Set.ncard (ZW σ₁ u (u + k * h)) + Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)) := by
        exact_mod_cast hunion
      have hadd : ∫ t in u..(u + k * h + h), avgOnCircleR σ₀ u v t
          = (∫ t in u..(u + k * h), avgOnCircleR σ₀ u v t)
            + ∫ t in (u + k * h)..(u + k * h + h), avgOnCircleR σ₀ u v t :=
        (intervalIntegral.integral_add_adjacent_intervals (hAc.intervalIntegrable _ _)
          (hAc.intervalIntegrable _ _)).symm
      rw [hadd]
      have hLh : 0 ≤ logRadii σ₀ σ₁ * h := by positivity
      calc (Set.ncard (ZW σ₁ u (u + k * h) ∪ ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ) * logRadii σ₀ σ₁ * h
          ≤ (Set.ncard (ZW σ₁ u (u + k * h)) + Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)))
              * logRadii σ₀ σ₁ * h := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hcast hLh
        _ = (Set.ncard (ZW σ₁ u (u + k * h)) : ℝ) * logRadii σ₀ σ₁ * h
              + (Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ) * logRadii σ₀ σ₁ * h := by ring
        _ ≤ _ := by push_cast; linarith
  exact key K le_rfl

/-- **The window count from a mean-square bound**, radius `2 − σ₀`. -/
theorem window_zero_count_R {σ₀ σ₁ lam u B : ℝ} {K : ℕ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1)
    (hlam : 1 ≤ lam) (hwin : 4 ≤ u ∨ u + K * cellH σ₀ σ₁ ≤ -4)
    (hMS : ∀ σ ∈ Icc σ₀ (4 - σ₀),
      ∫ t in (u - (2 - σ₀))..(u + K * cellH σ₀ σ₁ + (2 - σ₀)), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B) :
    (ZW σ₁ u (u + K * cellH σ₀ σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + K * cellH σ₀ σ₁)) : ℝ) * logRadii σ₀ σ₁ * cellH σ₀ σ₁
        ≤ K * cellH σ₀ σ₁ * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * B := by
  obtain ⟨hfin, hb⟩ := window_bound_R (K := K) hσ₀ hσ hσ' hlam hwin
  refine ⟨hfin, hb.trans ?_⟩
  have huv : u ≤ u + K * cellH σ₀ σ₁ := by
    have : (0 : ℝ) ≤ K * cellH σ₀ σ₁ := by have := cellH_pos hσ; positivity
    linarith
  have hA := integral_avgOnCircleR_le hσ₀ (by linarith) huv hwin hMS
  have hl : 0 ≤ (2 * lam)⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_left hA hl]

/-- **The zeros with `β ≥ σ₁` up to height `T`, from a polylogarithmic mean square on `Re s ≥ σ₀`**: for
`0 < σ₀ < σ₁ < 1` and `MSPoly σ₀`, some `C ≥ 0` has, for every `T ≥ 16`, that these zeros, counted with
multiplicity, are finitely many and number at most `(3 T log log T + C T)/(L h)`. -/
theorem count_bound_ms {σ₀ σ₁ : ℝ} (hσ₀ : 0 < σ₀) (hσ : σ₀ < σ₁) (hσ' : σ₁ < 1) (hMS : MSPoly σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 16 ≤ T →
      {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T}.Finite ∧
        (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T} : ℝ)
          * (logRadii σ₀ σ₁ * cellH σ₀ σ₁) ≤ 3 * T * Real.log (Real.log T) + C * T := by
  obtain ⟨A, hA0, hA⟩ := hMS
  have hC0 := CZ_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 * Real.log 2 + 2 * CZ + 4 * A, by positivity, ?_⟩
  intro T hT
  set h := cellH σ₀ σ₁ with hhdef
  have hh0 : 0 < h := cellH_pos hσ
  have hh1 : h < 1 := by simp only [hhdef, cellH]; linarith
  have hR1 : 1 < 2 - σ₀ := by linarith
  have hR2 : 2 - σ₀ < 2 := by linarith
  set K : ℕ := ⌈(T - 4) / h⌉₊ + 1 with hK
  have hKcast : (K : ℝ) = ⌈(T - 4) / h⌉₊ + 1 := by rw [hK]; push_cast; ring
  have hKlo : T - 4 + h ≤ K * h := by
    have h1 : (T - 4) / h ≤ ⌈(T - 4) / h⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hh0] at h1
    rw [hKcast]; nlinarith
  have hKhi : (K : ℝ) * h ≤ T := by
    have h1 : (⌈(T - 4) / h⌉₊ : ℝ) < (T - 4) / h + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by linarith) hh0.le)
    have h2 : ((T - 4) / h) * h = T - 4 := by field_simp
    rw [hKcast]; nlinarith
  have hKh0 : (0 : ℝ) ≤ K * h := by positivity
  set M : ℝ := K * h + 4 + (2 - σ₀) with hM
  have hM2 : 2 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hMT : M ≤ 2 * T := by linarith
  set D : ℝ := K * h + 2 * (2 - σ₀) with hD
  have hlogM1 : 1 ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]
    have := Real.exp_one_lt_d9
    linarith
  set lam : ℝ := Real.log M ^ 3 with hlam
  have hlam1 : 1 ≤ lam := one_le_pow₀ hlogM1
  have hlam0 : 0 < lam := by linarith
  set B : ℝ := A * Real.log M ^ 3 * (D + M) with hB
  have hMSpos : ∀ σ ∈ Icc σ₀ (4 - σ₀),
      ∫ t in ((4 : ℝ) - (2 - σ₀))..((4 : ℝ) + K * h + (2 - σ₀)), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B := by
    intro σ hσr
    have hms := hA σ M (4 - (2 - σ₀)) (4 + K * h + (2 - σ₀)) hσr.1 (by linarith [hσr.2]) hM2
      (by linarith) (Or.inl (by linarith))
      (fun t ht => by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.2])
    have e : (4 + K * h + (2 - σ₀)) - (4 - (2 - σ₀)) = D := by rw [hD]; ring
    rw [e] at hms
    exact hms
  have hMSneg : ∀ σ ∈ Icc σ₀ (4 - σ₀),
      ∫ t in ((-4 - K * h) - (2 - σ₀))..((-4 - K * h) + K * h + (2 - σ₀)),
        ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B := by
    intro σ hσr
    have hms := hA σ M (-4 - K * h - (2 - σ₀)) (-4 - K * h + K * h + (2 - σ₀)) hσr.1
      (by linarith [hσr.2]) hM2 (by linarith) (Or.inr (by linarith))
      (fun t ht => by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
    have e : (-4 - K * h + K * h + (2 - σ₀)) - (-4 - K * h - (2 - σ₀)) = D := by rw [hD]; ring
    rw [e] at hms
    exact hms
  obtain ⟨hfp, hbp⟩ := window_zero_count_R (K := K) (u := 4) hσ₀ hσ hσ' hlam1 (Or.inl le_rfl) hMSpos
  obtain ⟨hfn, hbn⟩ := window_zero_count_R (K := K) (u := -4 - K * h) hσ₀ hσ hσ' hlam1
    (Or.inr (by linarith)) hMSneg
  have hsub : {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T}
      ⊆ ZW σ₁ 4 (4 + K * h) ∪ ZW σ₁ (-4 - K * h) (-4 - K * h + K * h) := by
    rintro p ⟨hre, him⟩
    have h4 := four_lt_abs_im_zero p
    by_cases hpos : 0 ≤ (zetaZeroFamily p).im
    · left
      rw [abs_of_nonneg hpos] at h4 him
      exact ⟨hre, by linarith, by linarith⟩
    · right
      push Not at hpos
      rw [abs_of_neg hpos] at h4 him
      exact ⟨hre, by linarith, by linarith⟩
  have hfin := (hfp.union hfn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard := Set.ncard_le_ncard hsub (hfp.union hfn)
  have hu := Set.ncard_union_le (ZW σ₁ 4 (4 + K * h)) (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h))
  have hcardR : (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
      |(zetaZeroFamily p).im| ≤ T} : ℝ)
        ≤ Set.ncard (ZW σ₁ 4 (4 + K * h)) + Set.ncard (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h)) := by
    exact_mod_cast hcard.trans hu
  clear hMSpos hMSneg hsub hcard hu hfp hfn hfin
  have hLh : 0 < logRadii σ₀ σ₁ * h := mul_pos (logRadii_pos hσ (by linarith)) hh0
  -- the mean-square term
  have hBl : (2 * lam)⁻¹ * B = A * (D + M) / 2 := by
    rw [hB, hlam]; field_simp
  have hBT : (2 * lam)⁻¹ * B ≤ 2 * A * T := by
    rw [hBl]
    have hDM : D + M ≤ 4 * T := by rw [hD, hM]; linarith
    have := mul_le_mul_of_nonneg_left hDM hA0
    linarith
  -- the logarithmic term
  have hlogT : 2 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlogM : Real.log M ≤ 2 * Real.log T := by
    have h1 : Real.log M ≤ Real.log (2 * T) := Real.log_le_log hM0 hMT
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hloglogM : Real.log (Real.log M) ≤ Real.log 2 + Real.log (Real.log T) := by
    have h1 : Real.log (Real.log M) ≤ Real.log (2 * Real.log T) :=
      Real.log_le_log (by linarith) hlogM
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    exact h1
  have hloglam : Real.log lam / 2 ≤ 3 / 2 * (Real.log 2 + Real.log (Real.log T)) := by
    rw [hlam, Real.log_pow]
    push_cast
    linarith
  have hloglam0 : 0 ≤ Real.log lam / 2 + CZ := by
    have := Real.log_nonneg hlam1
    linarith
  have hterm : (K : ℝ) * h * (Real.log lam / 2 + CZ)
      ≤ T * (3 / 2 * (Real.log 2 + Real.log (Real.log T)) + CZ) :=
    mul_le_mul hKhi (by linarith) hloglam0 (by linarith)
  calc (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T} : ℝ)
        * (logRadii σ₀ σ₁ * h)
      ≤ (Set.ncard (ZW σ₁ 4 (4 + K * h)) + Set.ncard (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h)))
          * (logRadii σ₀ σ₁ * h) := mul_le_mul_of_nonneg_right hcardR hLh.le
    _ = (Set.ncard (ZW σ₁ 4 (4 + K * h)) : ℝ) * logRadii σ₀ σ₁ * h
          + (Set.ncard (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h)) : ℝ) * logRadii σ₀ σ₁ * h := by ring
    _ ≤ 2 * ((K : ℝ) * h * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * B) := by
        linarith only [hbp, hbn]
    _ ≤ 3 * T * Real.log (Real.log T) + (3 * Real.log 2 + 2 * CZ + 4 * A) * T := by
        linarith only [hterm, hBT]

/-- **From a polylogarithmic mean square on `Re s ≥ σ₀`, almost every zero lies within `w` of the critical line for
every `w > σ₀ − ½`**, given a lower bound `c·T log T` for the number of pairs up to height `T`. -/
theorem tendsto_NX_div_of_msPoly {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hMS : MSPoly σ₀) {c : ℝ}
    (hc : 0 < c) (hN : ∀ᶠ T in atTop, c * (T * Real.log T) ≤ NX 0 T) {w : ℝ} (hw : σ₀ - 1 / 2 < w) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  rcases le_or_gt (1 / 2) w with hw1 | hw1
  · simp only [ShellCount.NX_eq_zero hw1, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  set σ₁ : ℝ := 1 / 2 + w with hσ₁
  have hσ : σ₀ < σ₁ := by rw [hσ₁]; linarith
  have hσ' : σ₁ < 1 := by rw [hσ₁]; linarith
  obtain ⟨C, hC0, hcount⟩ := count_bound_ms hσ₀ hσ hσ' hMS
  set Lh : ℝ := logRadii σ₀ σ₁ * cellH σ₀ σ₁ with hLhdef
  have hLh : 0 < Lh := mul_pos (logRadii_pos hσ (by linarith)) (cellH_pos hσ)
  set g : ℝ → ℝ := fun T =>
    (3 * (Real.log (Real.log T) / Real.log T) + C * (Real.log T)⁻¹) / (Lh * c) with hg
  have hglim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => Real.log (Real.log T) / Real.log T) atTop (𝓝 0) := by
      have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp Real.tendsto_log_atTop
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun T => (Real.log T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have := ((h1.const_mul 3).add (h2.const_mul C)).div_const (Lh * c)
    simpa [hg] using this
  refine squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hglim
  filter_upwards [hN, eventually_ge_atTop (16 : ℝ)] with T hT hT16
  obtain ⟨hfin, hb⟩ := hcount T hT16
  have hNX := NX_le_ncard w T (by simpa only [hσ₁] using hfin)
  have hlogT : 2 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
  have hden : 0 < c * (T * Real.log T) := by
    have : (0 : ℝ) < T := by linarith
    have : (0 : ℝ) < Real.log T := by linarith
    positivity
  have hN0 : 0 < (NX 0 T : ℝ) := hden.trans_le hT
  rw [div_le_iff₀ hN0]
  have hg0 : 0 ≤ g T := by
    have hL0 : 0 < Real.log T := by linarith
    simp only [hg]; positivity
  have hkey : g T * (c * (T * Real.log T)) = (3 * T * Real.log (Real.log T) + C * T) / Lh := by
    have hlog0 : Real.log T ≠ 0 := by linarith
    have hc0 : c ≠ 0 := hc.ne'
    have hLh0 : Lh ≠ 0 := hLh.ne'
    simp only [hg]
    field_simp
  have hNXr : (NX w T : ℝ) ≤ Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
      |(zetaZeroFamily p).im| ≤ T} := by exact_mod_cast hNX
  calc (NX w T : ℝ) ≤ Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        |(zetaZeroFamily p).im| ≤ T} := hNXr
    _ ≤ (3 * T * Real.log (Real.log T) + C * T) / Lh := by
        rw [le_div_iff₀ hLh]; exact hb
    _ = g T * (c * (T * Real.log T)) := hkey.symm
    _ ≤ g T * NX 0 T := mul_le_mul_of_nonneg_left hT hg0

/-- **For every `w > 0`, almost every zero lies within `w` of the critical line**, given a lower bound `c·T log T`
for the number of pairs up to height `T`: the order-`2K` Euler–Maclaurin formula with `K > 1/w` gives `MSPoly σ₀`
at `σ₀ = (2K+1)/(4K+1)`, and `σ₀ − ½ = 1/(2(4K+1)) < w`. -/
theorem tendsto_NX_div_of_lower {c : ℝ} (hc : 0 < c) (hN : ∀ᶠ T in atTop, c * (T * Real.log T) ≤ NX 0 T)
    {w : ℝ} (hw : 0 < w) : Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  set K : ℕ := ⌈1 / w⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; omega
  have hKr : (K : ℝ) = ⌈1 / w⌉₊ + 1 := by rw [hK]; push_cast; ring
  have hKw : 1 / w < K := by
    have := Nat.le_ceil (1 / w)
    rw [hKr]; linarith
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have h41 : (0 : ℝ) < 4 * K + 1 := by linarith
  set σ₀ : ℝ := (2 * K + 1) / (4 * K + 1) with hσ₀
  have hσ₀0 : 0 < σ₀ := by rw [hσ₀]; positivity
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀, div_lt_one h41]; linarith
  have hMS := msPoly_of_order hK1 (le_refl σ₀) hσ₀1.le
  refine tendsto_NX_div_of_msPoly hσ₀0 hMS hc hN ?_
  have e : σ₀ - 1 / 2 = 1 / (2 * (4 * K + 1)) := by rw [hσ₀]; field_simp; ring
  rw [e, div_lt_iff₀ (by positivity)]
  have : 1 < w * K := by rwa [div_lt_iff₀ hw, mul_comm] at hKw
  nlinarith

end BohrLandauCore

#print axioms BohrLandauCore.cell_int_R
#print axioms BohrLandauCore.window_bound_R
#print axioms BohrLandauCore.window_zero_count_R
#print axioms BohrLandauCore.count_bound_ms
#print axioms BohrLandauCore.tendsto_NX_div_of_msPoly
#print axioms BohrLandauCore.tendsto_NX_div_of_lower
