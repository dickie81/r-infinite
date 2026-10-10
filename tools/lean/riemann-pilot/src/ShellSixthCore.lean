import Mathlib
import ZetaDiscs
import MeanSquareZeta
import ShellCount
import WeilZeta

/-! # Zeros with β ≥ σ₁ > 2/3, and almost every zero within w > 1/6 of the line (round 401)

Summing `ZetaDiscs.cell_bound` over the cells of a window, with the mean square of `MeanSquareZeta`, bounds the number
of zeros with `β ≥ σ₁ > 2/3` up to height `T`, counted with multiplicity, by `O(T √(log T))`. With a lower bound
`c·T log T` for the number of pairs (supplied in the zeta23 layer by `ShellDensity.NX_zero_ge`, round 400) the
proportion of pairs with `β ≥ ½ + w` tends to `0` for every `w > 1/6`.

* **`window_zero_count`**: for `σ₁ ∈ (2/3, 1)`, `λ ≥ 1` and a window `[u, u + Kh)` with `4 ≤ u` or `u + Kh ≤ −4`, the
  zeros with `β ≥ σ₁` and `γ` in the window, counted with multiplicity, are finitely many and number at most
  `(Kh(½ log λ + C₀) + B/(2λ))/(Lh)` when `B` bounds the mean square of `ζ` over `[u − 4/3, u + Kh + 4/3]` for every
  `σ ∈ [2/3, 10/3]`.
* **`count_bound`**: given `EMApprox`, for `σ₁ ∈ (2/3, 1)` and `T ≥ max(e⁵, 200)`, the zeros with `β ≥ σ₁` and
  `|γ| ≤ T`, counted with multiplicity, number at most `(12 T √(log T) + 2(C₀ + 38) T)/(Lh)`. Every nontrivial zero has
  `|γ| > 4` (`Pilot1ca.four_lt_abs_im_zero`), so the windows `[4, 4 + Kh)` and `[−4 − Kh, −4)` with `Kh > T − 4` cover
  those with `|γ| ≤ T`.
* **`NX_le_ncard`**: `NX w T` is at most the number of zeros with `β ≥ ½ + w` and `|γ| ≤ T`, given that this set is
  finite.
* **`tendsto_NX_div_of_EMApprox`**: given `EMApprox` and `NX 0 T ≥ c·T log T` for large `T`, `NX w T / NX 0 T → 0` for
  every `w > 1/6`.

Not proved here: `w ≤ 1/6`, because `MeanSquareZeta.mean_square_zeta_le` is proved for `σ ≥ 2/3` only. Round 402's
`BohrLandauCore` proves every `w > 0` from the order-`2K` mean square of `MeanSquareHigh`.
-/

open Real Complex Metric Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShellSixthCore

open Pilot1bt Pilot1ca ShortWeil MeanSquareZeta ZetaDiscs


/-- The zeros with `β ≥ σ₁` and `γ ∈ [a, b)`, with multiplicity. -/
def ZW (σ₁ a b : ℝ) : Set ZIdx :=
  {p | σ₁ ≤ (zetaZeroFamily p).re ∧ (zetaZeroFamily p).im ∈ Ico a b}

lemma ZW_union (σ₁ a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    ZW σ₁ a c = ZW σ₁ a b ∪ ZW σ₁ b c := by
  ext p
  simp only [ZW, Set.mem_ofPred_eq, Set.mem_union, ← Set.Ico_union_Ico_eq_Ico hab hbc]
  tauto

lemma ZW_empty (σ₁ a : ℝ) : ZW σ₁ a a = ∅ := by
  ext p; simp [ZW]

/-- One cell, integrated over its centres: `n·L·h ≤ h(½ log λ + C₀) + (2λ)⁻¹ ∫_cell avgOnCircle`, where `n` counts the
cell's zeros with `β ≥ σ₁`, a finite set. -/
theorem cell_int {σ₁ lam u v a : ℝ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)
    (huv : u ≤ v) (hwin : 4 ≤ u ∨ v ≤ -4) (hua : u ≤ a) (hav : a + hS σ₁ ≤ v) :
    (ZW σ₁ a (a + hS σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ a (a + hS σ₁)) : ℝ) * LS σ₁ * hS σ₁
        ≤ hS σ₁ * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * ∫ t in a..(a + hS σ₁), avgOnCircle u v t := by
  have hh := hS_pos hσ
  have hAc := continuous_avgOnCircle huv hwin
  -- finiteness, from the disc about the left end
  have hfin : (ZW σ₁ a (a + hS σ₁)).Finite := by
    have ha : a ∈ Icc u v := ⟨hua, by linarith⟩
    have hrR := rS_lt hσ hσ'
    have ht0 : 4 ≤ |a| := abs_ge_of_win hwin ha
    set c : ℂ := 2 + (a : ℂ) * I with hc
    have h1 : (1 : ℂ) ∉ closedBall c (rS σ₁) := by
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
    rw [rS, Real.le_sqrt (norm_nonneg _) (by positivity), Complex.sq_norm, Complex.normSq_apply]
    simp only [hc, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.re_ofNat, Complex.im_ofNat]
    have h1 : ((zetaZeroFamily p).re - 2) * ((zetaZeroFamily p).re - 2) ≤ (2 - σ₁) ^ 2 := by
      nlinarith
    have h2 : ((zetaZeroFamily p).im - a) * ((zetaZeroFamily p).im - a) ≤ hS σ₁ ^ 2 := by
      have := him.1; have := him.2
      nlinarith
    linarith
  refine ⟨hfin, ?_⟩
  have hpt : ∀ t ∈ Icc a (a + hS σ₁), (Set.ncard (ZW σ₁ a (a + hS σ₁)) : ℝ) * LS σ₁
      ≤ Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircle u v t := by
    intro t ht
    have := cell_bound hσ hσ' hlam hwin (show t ∈ Icc u v from ⟨hua.trans ht.1, ht.2.trans hav⟩) ht
    have e : avgOnCircle u v t / (2 * lam) = (2 * lam)⁻¹ * avgOnCircle u v t := by ring
    simp only [ZW] at this ⊢
    linarith
  have hi1 : IntervalIntegrable (fun _ : ℝ => (Set.ncard (ZW σ₁ a (a + hS σ₁)) : ℝ) * LS σ₁)
      volume a (a + hS σ₁) := intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun t => Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircle u v t)
      volume a (a + hS σ₁) := intervalIntegrable_const.add ((hAc.intervalIntegrable _ _).const_mul _)
  have hint := intervalIntegral.integral_mono_on (le_of_lt (by linarith : a < a + hS σ₁)) hi1 hi2 hpt
  have e1 : ∫ _ in a..(a + hS σ₁), (Set.ncard (ZW σ₁ a (a + hS σ₁)) : ℝ) * LS σ₁
      = hS σ₁ * ((Set.ncard (ZW σ₁ a (a + hS σ₁)) : ℝ) * LS σ₁) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have e2 : ∫ t in a..(a + hS σ₁), (Real.log lam / 2 + CZ + (2 * lam)⁻¹ * avgOnCircle u v t)
      = hS σ₁ * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * ∫ t in a..(a + hS σ₁), avgOnCircle u v t := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hAc.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul]
    ring
  rw [e1, e2] at hint
  linarith

/-- **The window `[u, u + Kh)`**, by induction over its `K` cells: its zeros with `β ≥ σ₁` are finitely many, and
`n·L·h ≤ Kh(½ log λ + C₀) + (2λ)⁻¹ ∫_u^{u+Kh} avgOnCircle`. -/
theorem window_bound {σ₁ lam u : ℝ} {K : ℕ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)
    (hwin : 4 ≤ u ∨ u + K * hS σ₁ ≤ -4) :
    (ZW σ₁ u (u + K * hS σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + K * hS σ₁)) : ℝ) * LS σ₁ * hS σ₁
        ≤ K * hS σ₁ * (Real.log lam / 2 + CZ)
          + (2 * lam)⁻¹ * ∫ t in u..(u + K * hS σ₁), avgOnCircle u (u + K * hS σ₁) t := by
  set h := hS σ₁ with hhdef
  set v := u + K * h with hv
  have hh0 : 0 < h := hS_pos hσ
  have huv : u ≤ v := by
    have : (0 : ℝ) ≤ K * h := by positivity
    linarith
  have hAc := continuous_avgOnCircle huv hwin
  have key : ∀ k : ℕ, k ≤ K → (ZW σ₁ u (u + k * h)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + k * h)) : ℝ) * LS σ₁ * h
        ≤ k * h * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * ∫ t in u..(u + k * h), avgOnCircle u v t := by
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
      obtain ⟨hcf, hcb⟩ := cell_int hσ hσ' hlam huv hwin hle1 (by linarith)
      rw [hstep, ZW_union σ₁ u (u + k * h) (u + k * h + h) hle1 (by linarith)]
      refine ⟨hfin.union hcf, ?_⟩
      have hunion := Set.ncard_union_le (ZW σ₁ u (u + k * h)) (ZW σ₁ (u + k * h) (u + k * h + h))
      have hL := LS_pos hσ hσ'
      have hcast : (Set.ncard (ZW σ₁ u (u + k * h) ∪ ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ)
          ≤ Set.ncard (ZW σ₁ u (u + k * h)) + Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)) := by
        exact_mod_cast hunion
      have hadd : ∫ t in u..(u + k * h + h), avgOnCircle u v t
          = (∫ t in u..(u + k * h), avgOnCircle u v t) + ∫ t in (u + k * h)..(u + k * h + h), avgOnCircle u v t :=
        (intervalIntegral.integral_add_adjacent_intervals (hAc.intervalIntegrable _ _)
          (hAc.intervalIntegrable _ _)).symm
      rw [hadd]
      have hLh : 0 ≤ LS σ₁ * h := by positivity
      calc (Set.ncard (ZW σ₁ u (u + k * h) ∪ ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ) * LS σ₁ * h
          ≤ (Set.ncard (ZW σ₁ u (u + k * h)) + Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)))
              * LS σ₁ * h := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hcast hLh
        _ = (Set.ncard (ZW σ₁ u (u + k * h)) : ℝ) * LS σ₁ * h
              + (Set.ncard (ZW σ₁ (u + k * h) (u + k * h + h)) : ℝ) * LS σ₁ * h := by ring
        _ ≤ _ := by push_cast; linarith
  exact key K le_rfl

/-- **The window count from a mean-square bound**: if `∫|ζ(σ+it)|² ≤ B` over `t ∈ [u − 4/3, u + Kh + 4/3]`
for every `σ ∈ [2/3, 10/3]`, the zeros with `β ≥ σ₁` and `γ ∈ [u, u + Kh)` are finitely many and
`n·L·h ≤ Kh(½ log λ + C₀) + B/(2λ)`. -/
theorem window_zero_count {σ₁ lam u B : ℝ} {K : ℕ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (hlam : 1 ≤ lam)
    (hwin : 4 ≤ u ∨ u + K * hS σ₁ ≤ -4)
    (hMS : ∀ σ ∈ Icc (2 / 3 : ℝ) (10 / 3),
      ∫ t in (u - 4 / 3)..(u + K * hS σ₁ + 4 / 3), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B) :
    (ZW σ₁ u (u + K * hS σ₁)).Finite ∧
      (Set.ncard (ZW σ₁ u (u + K * hS σ₁)) : ℝ) * LS σ₁ * hS σ₁
        ≤ K * hS σ₁ * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * B := by
  obtain ⟨hfin, hb⟩ := window_bound (K := K) hσ hσ' hlam hwin
  refine ⟨hfin, hb.trans ?_⟩
  have huv : u ≤ u + K * hS σ₁ := by
    have : (0 : ℝ) ≤ K * hS σ₁ := by have := hS_pos hσ; positivity
    linarith
  have hA := integral_avgOnCircle_le huv hwin hMS
  have hl : 0 ≤ (2 * lam)⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_left hA hl]

/-- The zero of the pair `i` with `β ≥ ½`, as an element of the zero family. -/
def pairZero (i : ZeroIdx (sqF Xi)) : ZIdx := zetaEquiv.symm (decide ((tau i).im ≤ 0), i)

lemma pairZero_spec (i : ZeroIdx (sqF Xi)) :
    (zetaZeroFamily (pairZero i)).re = 1 / 2 + |(tau i).im| ∧
      |(zetaZeroFamily (pairZero i)).im| = |(tau i).re| := by
  have h : zetaZeroFamily (pairZero i) = rhoXi (decide ((tau i).im ≤ 0), i) := by
    rw [← rhoXi_zetaEquiv (pairZero i)]
    simp only [pairZero, Equiv.apply_symm_apply]
  rw [h]
  by_cases hi : (tau i).im ≤ 0
  · simp only [rhoXi, hi, decide_true, ↓reduceIte, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
    refine ⟨?_, by simp⟩
    rw [abs_of_nonpos hi]
    norm_num
  · push Not at hi
    simp only [rhoXi, not_le.2 hi, decide_false, Bool.false_eq_true, ↓reduceIte,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, zero_mul, one_mul, zero_sub, zero_add, neg_neg]
    refine ⟨?_, by simp⟩
    rw [abs_of_pos hi]
    norm_num

/-- **`NX w T` is at most the number of zeros with `β ≥ ½ + w` and `|γ| ≤ T`**, given that this set is finite. -/
lemma NX_le_ncard (w T : ℝ)
    (hfin : {p : ZIdx | 1 / 2 + w ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T}.Finite) :
    NX w T ≤ Set.ncard {p : ZIdx | 1 / 2 + w ≤ (zetaZeroFamily p).re ∧
      |(zetaZeroFamily p).im| ≤ T} := by
  unfold NX
  refine Set.ncard_le_ncard_of_injOn pairZero ?_ ?_ hfin
  · rintro i ⟨hT, hw⟩
    obtain ⟨hre, him⟩ := pairZero_spec i
    exact ⟨by rw [hre]; linarith, by rw [him]; exact hT⟩
  · intro i _ j _ hij
    have := congrArg zetaEquiv hij
    simp only [pairZero, Equiv.apply_symm_apply] at this
    exact (Prod.ext_iff.1 this).2

lemma CZ_pos : 0 < CZ := by
  unfold CZ
  have h1 := two_sub_pi_sq_pos
  have h2 : 2 - π ^ 2 / 6 < 1 := by
    have := Real.pi_gt_three; nlinarith
  linarith [Real.log_neg h1 h2]

/-- **The zeros with `β ≥ σ₁ > 2/3` up to height `T`**, counted with multiplicity, number at most
`(12 T √(log T) + 2(C₀ + 38) T)/(L h)` for `T ≥ max(e⁵, 200)`, given the Euler–Maclaurin approximation. -/
theorem count_bound (hEM : EMApprox) {σ₁ : ℝ} (hσ : 2 / 3 < σ₁) (hσ' : σ₁ < 1) (T : ℝ)
    (hT : max (Real.exp 5) 200 ≤ T) :
    {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T}.Finite ∧
      (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T} : ℝ)
          * (LS σ₁ * hS σ₁)
        ≤ 12 * T * Real.sqrt (Real.log T) + 2 * (CZ + 38) * T := by
  have hT200 : 200 ≤ T := (le_max_right _ _).trans hT
  have hlogT : 5 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_max_left _ _).trans hT
  set h := hS σ₁ with hhdef
  have hh0 : 0 < h := hS_pos hσ
  have hh1 : h < 1 / 3 := by simp only [hhdef, hS]; linarith
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
  set M : ℝ := K * h + 16 / 3 with hM
  have hM2 : 2 ≤ M := by linarith
  have hMT : M ≤ 2 * T := by linarith
  have hM0 : 0 < M := by linarith
  set J : ℕ := ⌈(3 / 2) * Real.logb 2 M⌉₊ with hJ
  set Q : ℝ := ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) with hQ
  have hQrpow : Q = (2 : ℝ) ^ ((2 : ℝ) / 3 * J) := by
    rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  have hlogb0 : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) (by linarith)
  have hMQ : M ≤ Q := by
    rw [hQrpow]
    have hJ1 : (3 / 2) * Real.logb 2 M ≤ J := Nat.le_ceil _
    calc M = (2 : ℝ) ^ (Real.logb 2 M) := (Real.rpow_logb (by norm_num) (by norm_num) hM0).symm
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) / 3 * J) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hJhi : (J : ℝ) < (3 / 2) * Real.logb 2 M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hQM : Q ≤ 2 * M := by
    rw [hQrpow]
    calc (2 : ℝ) ^ ((2 : ℝ) / 3 * J) ≤ (2 : ℝ) ^ (Real.logb 2 M + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * M := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hM0,
            Real.rpow_one]; ring
  have hQ0 : 0 ≤ Q := by positivity
  set x : ℝ := (J : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by have := J.cast_nonneg (α := ℝ); linarith
  set lam : ℝ := x ^ 3 with hlam
  have hlam1 : 1 ≤ lam := one_le_pow₀ hx1
  set D : ℝ := K * h + 8 / 3 with hD
  set B : ℝ := 2 * (x ^ 2 * (D + 8 * x * Q)) + 2 * Q + 36 * D with hB
  have hMSpos : ∀ σ ∈ Icc (2 / 3 : ℝ) (10 / 3),
      ∫ t in ((4 : ℝ) - 4 / 3)..((4 : ℝ) + K * h + 4 / 3), ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B := by
    intro σ hσr
    have hms := mean_square_zeta_le hEM (σ := σ) (M := M) (a := 4 - 4 / 3) (b := 4 + K * h + 4 / 3)
      (J := J) hσr.1 hM2 hMQ (by linarith) (Or.inl (by norm_num))
      (fun t ht => by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.2])
    have e : (4 + K * h + 4 / 3) - (4 - 4 / 3 : ℝ) = D := by rw [hD]; ring
    rw [e] at hms
    exact hms
  have hMSneg : ∀ σ ∈ Icc (2 / 3 : ℝ) (10 / 3),
      ∫ t in ((-4 - K * h) - 4 / 3)..((-4 - K * h) + K * h + 4 / 3),
        ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ B := by
    intro σ hσr
    have hms := mean_square_zeta_le hEM (σ := σ) (M := M) (a := -4 - K * h - 4 / 3)
      (b := -4 - K * h + K * h + 4 / 3) (J := J) hσr.1 hM2 hMQ (by linarith)
      (Or.inr (by linarith))
      (fun t ht => by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
    have e : (-4 - K * h + K * h + 4 / 3) - (-4 - K * h - 4 / 3 : ℝ) = D := by rw [hD]; ring
    rw [e] at hms
    exact hms
  obtain ⟨hfp, hbp⟩ := window_zero_count (K := K) (u := 4) hσ hσ' hlam1 (Or.inl le_rfl) hMSpos
  obtain ⟨hfn, hbn⟩ := window_zero_count (K := K) (u := -4 - K * h) hσ hσ' hlam1
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
  have hLh : 0 < LS σ₁ * h := mul_pos (LS_pos hσ hσ') hh0
  -- the mean-square term
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hBl : (2 * lam)⁻¹ * B ≤ 19 * D + 9 * Q := by
    have hlam0 : 0 < 2 * lam := by positivity
    rw [inv_mul_le_iff₀ hlam0]
    have hx2 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
    have e1 := mul_le_mul_of_nonneg_right hx2 hD0
    have e2 := mul_le_mul_of_nonneg_right hx3 hD0
    have e3 := mul_le_mul_of_nonneg_right hx3 hQ0
    rw [hlam, hB]
    nlinarith only [e1, e2, e3, hD0, hQ0, hx1]
  have hMT' : M ≤ T + 16 / 3 := by rw [hM]; linarith only [hKhi]
  have hBT : (2 * lam)⁻¹ * B ≤ 38 * T := by
    have hDT : D ≤ T + 8 / 3 := by rw [hD]; linarith only [hKhi]
    linarith only [hBl, hDT, hQM, hMT', hT200]
  -- the logarithmic term
  have hxlog : x ≤ 4 * Real.log T := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith only [this]
    have hlM0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith only [hM2])
    have hlb : Real.logb 2 M ≤ 2 * Real.log M := by
      rw [Real.logb, div_le_iff₀ (by linarith only [hlog2])]
      nlinarith only [hlog2, hlM0]
    have hlM : Real.log M ≤ 1 + Real.log T := by
      have h1 : Real.log M ≤ Real.log (2 * T) := Real.log_le_log hM0 hMT
      rw [Real.log_mul (by norm_num) (by linarith only [hT200])] at h1
      have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith only [this]
      linarith only [h1, h2]
    rw [hx]
    linarith only [hJhi, hlb, hlM, hlogT]
  have hsqrt : Real.sqrt x ≤ 2 * Real.sqrt (Real.log T) := by
    calc Real.sqrt x ≤ Real.sqrt (4 * Real.log T) := Real.sqrt_le_sqrt hxlog
      _ = 2 * Real.sqrt (Real.log T) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hloglam : Real.log lam / 2 ≤ 6 * Real.sqrt (Real.log T) := by
    rw [hlam, Real.log_pow]
    have h1 := Real.log_le_rpow_div (x := x) (ε := 1 / 2) (by linarith only [hx1]) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    push_cast
    linarith only [h1, hsqrt]
  have hC0 := CZ_pos
  have hloglam0 : 0 ≤ Real.log lam / 2 + CZ := by
    have := Real.log_nonneg hlam1
    linarith only [this, hC0]
  have hterm : (K : ℝ) * h * (Real.log lam / 2 + CZ) ≤ T * (6 * Real.sqrt (Real.log T) + CZ) :=
    mul_le_mul hKhi (by linarith only [hloglam]) hloglam0 (by linarith only [hT200])
  calc (Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧ |(zetaZeroFamily p).im| ≤ T} : ℝ)
        * (LS σ₁ * h)
      ≤ (Set.ncard (ZW σ₁ 4 (4 + K * h)) + Set.ncard (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h)))
          * (LS σ₁ * h) := mul_le_mul_of_nonneg_right hcardR hLh.le
    _ = (Set.ncard (ZW σ₁ 4 (4 + K * h)) : ℝ) * LS σ₁ * h
          + (Set.ncard (ZW σ₁ (-4 - K * h) (-4 - K * h + K * h)) : ℝ) * LS σ₁ * h := by ring
    _ ≤ 2 * ((K : ℝ) * h * (Real.log lam / 2 + CZ) + (2 * lam)⁻¹ * B) := by
        linarith only [hbp, hbn]
    _ ≤ 12 * T * Real.sqrt (Real.log T) + 2 * (CZ + 38) * T := by
        linarith only [hterm, hBT]

/-- **For every `w > 1/6`, almost every zero lies within `w` of the critical line**, given the
Euler–Maclaurin approximation and a lower bound `c·T log T` for the number of pairs up to height `T`. -/
theorem tendsto_NX_div_of_EMApprox (hEM : EMApprox) {c : ℝ} (hc : 0 < c)
    (hN : ∀ᶠ T in atTop, c * (T * Real.log T) ≤ NX 0 T) {w : ℝ} (hw : 1 / 6 < w) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  rcases le_or_gt (1 / 2) w with hw1 | hw1
  · simp only [ShellCount.NX_eq_zero hw1, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  set σ₁ : ℝ := 1 / 2 + w with hσ₁
  have hσ : 2 / 3 < σ₁ := by rw [hσ₁]; linarith
  have hσ' : σ₁ < 1 := by rw [hσ₁]; linarith
  set Lh : ℝ := LS σ₁ * hS σ₁ with hLhdef
  have hLh : 0 < Lh := mul_pos (LS_pos hσ hσ') (hS_pos hσ)
  set g : ℝ → ℝ := fun T =>
    (12 * (Real.sqrt (Real.log T))⁻¹ + 2 * (CZ + 38) * (Real.log T)⁻¹) / (Lh * c) with hg
  have hglim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => (Real.sqrt (Real.log T))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    have h2 : Tendsto (fun T => (Real.log T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have := ((h1.const_mul 12).add (h2.const_mul (2 * (CZ + 38)))).div_const (Lh * c)
    simpa [hg] using this
  refine squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hglim
  filter_upwards [hN, eventually_ge_atTop (max (Real.exp 5) 200)] with T hT hT0
  obtain ⟨hfin, hb⟩ := count_bound hEM hσ hσ' T hT0
  have hNX := NX_le_ncard w T (by simpa only [hσ₁] using hfin)
  have hT200 : 200 ≤ T := (le_max_right _ _).trans hT0
  have hlogT : 5 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_max_left _ _).trans hT0
  have hden : 0 < c * (T * Real.log T) := by positivity
  have hN0 : 0 < (NX 0 T : ℝ) := hden.trans_le hT
  rw [div_le_iff₀ hN0]
  have hsq : 0 < Real.sqrt (Real.log T) := Real.sqrt_pos.2 (by linarith)
  have hg0 : 0 ≤ g T := by
    have hC0 := CZ_pos
    have hL0 : 0 < Real.log T := by linarith
    simp only [hg]; positivity
  have hkey : g T * (c * (T * Real.log T))
      = (12 * T * Real.sqrt (Real.log T) + 2 * (CZ + 38) * T) / Lh := by
    have hlog0 : Real.log T ≠ 0 := by linarith
    have e1 : Real.log T * (Real.sqrt (Real.log T))⁻¹ = Real.sqrt (Real.log T) := by
      rw [← div_eq_mul_inv, Real.div_sqrt]
    have hc0 : c ≠ 0 := hc.ne'
    have hLh0 : Lh ≠ 0 := hLh.ne'
    simp only [hg]
    calc (12 * (Real.sqrt (Real.log T))⁻¹ + 2 * (CZ + 38) * (Real.log T)⁻¹) / (Lh * c)
          * (c * (T * Real.log T))
        = (12 * T * (Real.log T * (Real.sqrt (Real.log T))⁻¹)
            + 2 * (CZ + 38) * T * (Real.log T * (Real.log T)⁻¹)) / Lh := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hLh0 hc0) hLh0]
          ring
      _ = _ := by rw [e1, mul_inv_cancel₀ hlog0]; ring
  have hNXr : (NX w T : ℝ) ≤ Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
      |(zetaZeroFamily p).im| ≤ T} := by exact_mod_cast hNX
  calc (NX w T : ℝ) ≤ Set.ncard {p : ZIdx | σ₁ ≤ (zetaZeroFamily p).re ∧
        |(zetaZeroFamily p).im| ≤ T} := hNXr
    _ ≤ (12 * T * Real.sqrt (Real.log T) + 2 * (CZ + 38) * T) / Lh := by
        rw [le_div_iff₀ hLh]; exact hb
    _ = g T * (c * (T * Real.log T)) := hkey.symm
    _ ≤ g T * NX 0 T := mul_le_mul_of_nonneg_left hT hg0

end ShellSixthCore

#print axioms ShellSixthCore.ZW_union
#print axioms ShellSixthCore.cell_int
#print axioms ShellSixthCore.window_bound
#print axioms ShellSixthCore.window_zero_count
#print axioms ShellSixthCore.pairZero_spec
#print axioms ShellSixthCore.NX_le_ncard
#print axioms ShellSixthCore.CZ_pos
#print axioms ShellSixthCore.count_bound
#print axioms ShellSixthCore.tendsto_NX_div_of_EMApprox
