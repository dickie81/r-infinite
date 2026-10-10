import Mathlib
import KaiserMoment

/-! # The bulk of the Kaiser probe and the doubled rate (round 163, part 11)

At `η = 1/L`, `α = m₄/m₂ ≤ 3/4`, every term `H((n+1)x)` with `x² ≥ 4/5` is `≥ −5P/(n+1)²`, and the
`n = 0` term is `≥ M/12800` with `M = e^{βL − 8}` when `x² ≤ 5/4`. So `KF(e^u) ≥ M/51200` on
`|u| ≤ 1/10`, `‖g‖² ≥ M²/(5·51200²)`, and with the zero side `Q(g) ≤ 720 P²(1+D₀)² S`:

  `λ₁(a) ≤ K e^{20a − 4π e^{2a}}`  for `a ≥ 4`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

variable {L η α : ℝ}

theorem re_Hr (y : ℝ) : (Hr L η α y).re = y ^ 2 * (y ^ 2 - α) * Kr L η y * Sr η y ^ 8 := by
  rw [Hr_eq, ofReal_re]

/-- Every term with `α ≤ y²` is `≥ −4P/(1+y²)`. -/
theorem re_Hr_ge_neg (hp : Par L η) (hL1 : 1 ≤ L) (hα : |α| ≤ 1) {y : ℝ} (hαy : α ≤ y ^ 2) :
    -(4 * kP η * (1 + y ^ 2)⁻¹) ≤ (Hr L η α y).re := by
  rw [re_Hr]
  have hP := (kP_pos hp.pos).le
  have hinv : 0 ≤ (1 + y ^ 2)⁻¹ := by positivity
  have hy2 := sq_nonneg y
  rcases le_total (y ^ 2) (L ^ 2) with hy | hy
  · have := mul_nonneg (mul_nonneg (mul_nonneg hy2 (sub_nonneg.2 hαy)) (Kr_nonneg (η := η) hy))
      (Sr8_nonneg (η := η) y)
    have : 0 ≤ 4 * kP η * (1 + y ^ 2)⁻¹ := by positivity
    linarith
  · have hy1 : 1 ≤ y ^ 2 := by nlinarith
    have hab : |y ^ 2 * (y ^ 2 - α)| ≤ 2 * y ^ 4 := by
      rw [abs_mul, abs_of_nonneg hy2]
      have : |y ^ 2 - α| ≤ 2 * y ^ 2 := by rw [abs_le]; constructor <;> linarith [abs_le.1 hα]
      nlinarith
    have hw := w4_tail hp hL1 hy
    have key : |y ^ 2 * (y ^ 2 - α) * Kr L η y * Sr η y ^ 8| ≤ 2 * |y ^ 4 * Kr L η y * Sr η y ^ 8| := by
      have e1 : y ^ 2 * (y ^ 2 - α) * Kr L η y * Sr η y ^ 8 = (y ^ 2 * (y ^ 2 - α)) * (Kr L η y * Sr η y ^ 8) := by ring
      have e2 : y ^ 4 * Kr L η y * Sr η y ^ 8 = y ^ 4 * (Kr L η y * Sr η y ^ 8) := by ring
      rw [e1, e2, abs_mul (y ^ 2 * (y ^ 2 - α)), abs_mul (y ^ 4), abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 4)]
      nlinarith [mul_le_mul_of_nonneg_right hab (abs_nonneg (Kr L η y * Sr η y ^ 8))]
    have := neg_abs_le (y ^ 2 * (y ^ 2 - α) * Kr L η y * Sr η y ^ 8)
    linarith

/-- The peak: `M = e^{βL − 8}`. -/
def kM (L : ℝ) : ℝ := Real.exp (bt L (1 / L) * L - 8)

/-- The `n = 0` term near `x = 1`. -/
theorem re_Hr_peak (hL : 50 ≤ L) {y : ℝ} (h1 : 4 / 5 ≤ y ^ 2) (h2 : y ^ 2 ≤ 5 / 4) :
    kM L / 12800 ≤ (Hr L (1 / L) (kα L) y).re := by
  have hp := par_inv hL
  have hL0 : 0 < L := by linarith
  obtain ⟨-, hα, -⟩ := alpha_ok hL
  have hb := gb_inv_bounds hL
  have hpi := Real.pi_lt_d2
  have hpi0 := pi_pos
  rw [re_Hr]
  have hyL : y ^ 2 ≤ L ^ 2 := by nlinarith
  have hK := Kr_lower hp hyL
  -- the exponential loss is at most 8
  have hq1 : gb L (1 / L) * y ^ 2 ≤ 4 := by nlinarith
  have hq2 : gb L (1 / L) * y ^ 4 / L ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : y ^ 4 ≤ 2 := by nlinarith
    nlinarith
  have hK' : kM L / 2 ≤ Kr L (1 / L) y := by
    refine le_trans ?_ hK
    rw [kM, kE, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    gcongr
    linarith
  -- the sinc factor is at least 1/2
  have hS : 1 / 2 ≤ Sr (1 / L) y := by
    refine le_trans ?_ (Sr_ge y)
    have : (π * (1 / L) * y) ^ 2 ≤ 3 := by
      have e : (π * (1 / L) * y) ^ 2 = π ^ 2 * y ^ 2 / L ^ 2 := by field_simp
      rw [e, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hS8 : (1 / 2 : ℝ) ^ 8 ≤ Sr (1 / L) y ^ 8 := pow_le_pow_left₀ (by norm_num) hS 8
  have hA : 1 / 25 ≤ y ^ 2 * (y ^ 2 - kα L) := by nlinarith
  have hM : 0 ≤ kM L := (Real.exp_pos _).le
  calc kM L / 12800 = 1 / 25 * (kM L / 2) * (1 / 2) ^ 8 := by ring
    _ ≤ y ^ 2 * (y ^ 2 - kα L) * Kr L (1 / L) y * Sr (1 / L) y ^ 8 := by
        have hA0 : 0 ≤ y ^ 2 * (y ^ 2 - kα L) := by linarith
        refine mul_le_mul (mul_le_mul hA hK' (by positivity) hA0) hS8 (by positivity)
          (mul_nonneg hA0 (Kr_nonneg hyL))

/-- **The Connes sum near `x = 1`.** -/
theorem re_EHr_ge (hL : 50 ≤ L) {x : ℝ} (hx : 0 < x) (h1 : 4 / 5 ≤ x ^ 2) (h2 : x ^ 2 ≤ 5 / 4) :
    Real.sqrt x * (kM L / 12800 - 10 * kP (1 / L)) ≤ (E (Hr L (1 / L) (kα L)) x).re := by
  have hp := par_inv hL
  obtain ⟨-, hα34, hα⟩ := alpha_ok hL
  have hP := (kP_pos hp.pos).le
  set P := kP (1 / L)
  set f : ℕ → ℂ := fun n => Hr L (1 / L) (kα L) ((n + 1) * x)
  have hs : Summable f := summable_Hr_nat' hp hx
  set h : ℕ → ℝ := fun n => -(5 * P) * ((n : ℝ) + 1)⁻¹ ^ 2 + if n = 0 then kM L / 12800 else 0
  have hh : HasSum h (-(5 * P) * ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 + kM L / 12800) :=
    (summable_inv_sq_succ.hasSum.mul_left _).add (hasSum_ite_eq 0 _)
  have hfh : ∀ n, h n ≤ (f n).re := by
    intro n
    set y := ((n : ℝ) + 1) * x
    have hn1 : 1 ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have hy2 : y ^ 2 = ((n : ℝ) + 1) ^ 2 * x ^ 2 := by simp only [y]; ring
    have hyx : x ^ 2 ≤ y ^ 2 := by
      rw [hy2]; have := one_le_pow₀ (n := 2) hn1
      nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg x)]
    have hfy : (f n).re = (Hr L (1 / L) (kα L) y).re := rfl
    have hneg := re_Hr_ge_neg hp (by linarith) hα (y := y) (by linarith)
    have hinv : 4 * P * (1 + y ^ 2)⁻¹ ≤ 5 * P * ((n : ℝ) + 1)⁻¹ ^ 2 := by
      have hy0 : 0 < y ^ 2 := by linarith
      have e1 : (1 + y ^ 2)⁻¹ ≤ (y ^ 2)⁻¹ := inv_anti₀ hy0 (by linarith)
      have e2 : 4 * (y ^ 2)⁻¹ ≤ 5 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
        rw [hy2, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [sq_nonneg ((n : ℝ) + 1)]
      nlinarith [mul_le_mul_of_nonneg_left e1 hP]
    rcases eq_or_ne n 0 with rfl | hn
    · have hpk := re_Hr_peak hL (y := x) h1 h2
      have hf0 : (f 0).re = (Hr L (1 / L) (kα L) x).re := by simp only [f, Nat.cast_zero, zero_add, one_mul]
      have h0 : h 0 = -(5 * P) * ((0 : ℝ) + 1)⁻¹ ^ 2 + kM L / 12800 := by simp [h]
      rw [h0, hf0]
      have : 0 ≤ 5 * P * ((0 : ℝ) + 1)⁻¹ ^ 2 := by positivity
      linarith
    · have hn' : h n = -(5 * P) * ((n : ℝ) + 1)⁻¹ ^ 2 := by simp [h, hn]
      rw [hn', hfy]
      linarith
  have hle := hasSum_le hfh hh (Complex.hasSum_re hs.hasSum)
  have hS := tsum_inv_sq_succ_le
  unfold E
  rw [re_ofReal_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  nlinarith

theorem bt_inv_mul (hL : 50 ≤ L) : bt L (1 / L) * L = 2 * π * (L ^ 2 - 4) := by
  have hL0 : L ≠ 0 := by positivity
  unfold bt; field_simp

theorem kM_big (hL : 50 ≤ L) : 256000 * kP (1 / L) ≤ kM L := by
  have hL0 : 0 < L := by linarith
  have hpi := Real.pi_gt_d2
  have hP : kP (1 / L) ≤ 2 * L ^ 8 := (kV_ge (par_inv hL)).trans (kV_inv_le hL)
  have hL2 : 2500 ≤ L ^ 2 := by nlinarith
  have h6 : 6 * L ^ 2 ≤ bt L (1 / L) * L - 8 := by
    rw [bt_inv_mul hL]
    have := mul_le_mul_of_nonneg_right hpi.le (by linarith : (0:ℝ) ≤ L ^ 2 - 4)
    linarith
  have hf := Real.pow_div_factorial_le_exp (x := 6 * L ^ 2) (by positivity) 7
  have h7 : (6 * L ^ 2) ^ 7 / (Nat.factorial 7 : ℝ) = 279936 / 5040 * L ^ 14 := by
    norm_num [Nat.factorial]; ring
  rw [h7] at hf
  have hL8 : 0 ≤ L ^ 8 := by positivity
  have hL6 : 2500 ^ 3 ≤ L ^ 6 := by
    have e : L ^ 6 = (L ^ 2) ^ 3 := by ring
    rw [e]; exact pow_le_pow_left₀ (by norm_num) hL2 3
  have : 512000 * L ^ 8 ≤ 279936 / 5040 * L ^ 14 := by
    have e : L ^ 14 = L ^ 6 * L ^ 8 := by ring
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right hL6 hL8]
  have := Real.exp_le_exp.2 h6
  unfold kM; linarith

theorem exp_fifth : 4 / 5 ≤ Real.exp (-(1 / 5)) ∧ Real.exp (1 / 5) ≤ 5 / 4 := by
  have h1 : 4 / 5 ≤ Real.exp (-(1 / 5)) := by linarith [Real.add_one_le_exp (-(1 / 5))]
  refine ⟨h1, ?_⟩
  have e : Real.exp (1 / 5) * Real.exp (-(1 / 5)) = 1 := by rw [← Real.exp_add]; simp
  have := Real.exp_pos (1 / 5)
  nlinarith

/-- **The bulk.** On `|u| ≤ 1/10`, `g(u) ≥ M/51200`. -/
theorem gK_bulk (hL : 50 ≤ L) {a u : ℝ} (ha : 1 / 10 ≤ a) (hu : u ∈ Icc (-(1 / 10)) (1 / 10)) :
    kM L / 51200 ≤ gK L (1 / L) (kα L) a u := by
  have hp := par_inv hL
  obtain ⟨hint, -, -⟩ := alpha_ok hL
  have hua : u ∈ Icc (-a) a := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simp only [gK, indicator_of_mem hua]
  set x := Real.exp u
  have hx : 0 < x := Real.exp_pos u
  rw [KF_eq hp hint hx, add_re]
  have hf := exp_fifth
  have hsq : ∀ v : ℝ, v ∈ Icc (-(1 / 10)) (1 / 10) → 4 / 5 ≤ Real.exp v ^ 2 ∧ Real.exp v ^ 2 ≤ 5 / 4 := by
    intro v hv
    have e : Real.exp v ^ 2 = Real.exp (2 * v) := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact ⟨hf.1.trans (Real.exp_le_exp.2 (by linarith [hv.1])),
      (Real.exp_le_exp.2 (by linarith [hv.2])).trans hf.2⟩
  have hu' : -u ∈ Icc (-(1 / 10)) (1 / 10) := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h1 := hsq u hu
  have h2 := hsq (-u) hu'
  have hinv : 1 / x = Real.exp (-u) := by rw [one_div, Real.exp_neg]
  have A := re_EHr_ge hL hx h1.1 h1.2
  have B := re_EHr_ge hL (by positivity : 0 < 1 / x) (by rw [hinv]; exact h2.1) (by rw [hinv]; exact h2.2)
  have hD : kM L / 25600 ≤ kM L / 12800 - 10 * kP (1 / L) := by linarith [kM_big hL]
  have hM : 0 ≤ kM L := (Real.exp_pos _).le
  have hs1 : 1 / 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs2 := Real.sqrt_nonneg (1 / x)
  have hD0 : 0 ≤ kM L / 12800 - 10 * kP (1 / L) := by linarith [div_nonneg hM (by norm_num : (0:ℝ) ≤ 25600)]
  have := mul_le_mul hs1 hD (by positivity) (Real.sqrt_nonneg _)
  have := mul_nonneg hs2 hD0
  linarith

/-- **The norm.** `‖g‖² ≥ (M/51200)²/5`. -/
theorem normSq_gK_ge (hL : 50 ≤ L) {a : ℝ} (ha : 1 / 10 ≤ a) :
    (kM L / 51200) ^ 2 / 5 ≤ Pilot1ca.normSq (gK L (1 / L) (kα L) a) := by
  have hp := par_inv hL
  obtain ⟨hint, -, -⟩ := alpha_ok hL
  have hpr := probe_gK hp hint (by linarith : 0 ≤ a) (α := kα L)
  have hi := hpr.memL2.integrable_sq
  have hM : 0 ≤ kM L := (Real.exp_pos _).le
  unfold Pilot1ca.normSq
  set s := Icc (-(1 / 10) : ℝ) (1 / 10)
  have h1 : ∫ t in s, gK L (1 / L) (kα L) a t ^ 2 ≤ ∫ t, gK L (1 / L) (kα L) a t ^ 2 :=
    setIntegral_le_integral hi (ae_of_all _ fun t => sq_nonneg _)
  have h2 : ∫ t in s, (kM L / 51200) ^ 2 ≤ ∫ t in s, gK L (1 / L) (kα L) a t ^ 2 := by
    refine setIntegral_mono_on (integrableOn_const (by simp [s])) hi.integrableOn measurableSet_Icc
      fun t ht => ?_
    have := gK_bulk hL ha ht
    exact pow_le_pow_left₀ (by positivity) this 2
  have h3 : ∫ t in s, (kM L / 51200) ^ 2 = (kM L / 51200) ^ 2 / 5 := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by norm_num)]; ring
  linarith

theorem exp_four_ge : 50 ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  norm_num at this; linarith

theorem kD0_inv_le (hL : 50 ≤ L) : 1 + kD0 L (1 / L) ≤ 80 * L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := pi_pos
  unfold kD0
  have h1 : (L - 4 * (1 / L)) ^ 2 ≤ L ^ 2 := by
    have : 0 ≤ 4 * (1 / L) := by positivity
    have : 4 * (1 / L) ≤ L := by rw [mul_one_div, div_le_iff₀ hL0]; nlinarith
    nlinarith
  have h2 : 32 * π * (1 / L) ≤ 3 := by
    rw [mul_one_div, div_le_iff₀ hL0]; nlinarith
  have h3 : 2 * (2 * π * (L - 4 * (1 / L))) ^ 2 ≤ 79.5 * L ^ 2 := by
    have e : 2 * (2 * π * (L - 4 * (1 / L))) ^ 2 = 8 * π ^ 2 * (L - 4 * (1 / L)) ^ 2 := by ring
    rw [e]
    have : π ^ 2 ≤ 9.9225 := by nlinarith
    have := mul_le_mul this h1 (sq_nonneg _) (by norm_num)
    nlinarith
  nlinarith

/-- **Rung 0, doubled rate**: `λ₁(a) ≤ K e^{20a − 4π e^{2a}}` for `a ≥ 4`, over the zeros of `Ξ`
(no RH input, no named input). Twice the exponent of `lam_dexp`. -/
theorem lam_kaiser :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * Real.exp (20 * a - 4 * π * Real.exp (2 * a)) := by
  set S := ∑' p : Bool × ZeroIdx (sqF Xi), ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set C := 720 * 25600 * 5 * 51200 ^ 2 * S * Real.exp (16 * π + 16)
  refine ⟨C, by positivity, fun a ha => ?_⟩
  set L := Real.exp a with hLdef
  have hL : 50 ≤ L := exp_four_ge.trans (Real.exp_le_exp.2 ha)
  have hL0 : 0 < L := Real.exp_pos a
  have ha0 : 0 < a := by linarith
  have hp := par_inv hL
  obtain ⟨hint, -, hα⟩ := alpha_ok hL
  have ht : Tail L (1 / L) (kα L) := ⟨hp, hα, by linarith⟩
  have hQ := weilQ_gK_le ht hint ha0 hLdef.symm
  have hN := normSq_gK_ge hL (a := a) (by linarith)
  have hlam := lam_mul_le (probe_gK hp hint ha0.le (α := kα L))
  have hM : 0 < kM L := Real.exp_pos _
  have hNb : 0 < (kM L / 51200) ^ 2 / 5 := by positivity
  have hE : 0 ≤ Real.exp (20 * a - 4 * π * Real.exp (2 * a)) := (Real.exp_pos _).le
  rcases le_or_gt (lam a) 0 with hl | hl
  · exact hl.trans (by positivity)
  -- the zero side is polynomial in `L`
  have hP := (kP_pos hp.pos).le
  have hP2 : kP (1 / L) ≤ 2 * L ^ 8 := (kV_ge hp).trans (kV_inv_le hL)
  have hD := kD0_inv_le hL
  have hD0 : 0 ≤ 1 + kD0 L (1 / L) := by linarith [kD0_nonneg (L := L) hp.pos]
  have hpoly : kP (1 / L) ^ 2 * (1 + kD0 L (1 / L)) ^ 2 ≤ 25600 * L ^ 20 := by
    have a1 : kP (1 / L) ^ 2 ≤ (2 * L ^ 8) ^ 2 := pow_le_pow_left₀ hP hP2 2
    have a2 : (1 + kD0 L (1 / L)) ^ 2 ≤ (80 * L ^ 2) ^ 2 := pow_le_pow_left₀ hD0 hD 2
    calc _ ≤ (2 * L ^ 8) ^ 2 * (80 * L ^ 2) ^ 2 := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = 25600 * L ^ 20 := by ring
  have hQb : weilQ a (gK L (1 / L) (kα L) a) ≤ 720 * (25600 * L ^ 20) * S := by
    refine hQ.trans ?_
    have := mul_le_mul_of_nonneg_right hpoly hS0
    nlinarith
  -- `λ₁ ≤ Q/‖g‖²`
  have hNpos : 0 < Pilot1ca.normSq (gK L (1 / L) (kα L) a) := hNb.trans_le hN
  have h1 : lam a ≤ weilQ a (gK L (1 / L) (kα L) a) / Pilot1ca.normSq (gK L (1 / L) (kα L) a) := by
    rw [le_div_iff₀ hNpos]; exact hlam
  have hQ0 : 0 ≤ weilQ a (gK L (1 / L) (kα L) a) :=
    (mul_pos hl hNpos).le.trans hlam
  have h2 := div_le_div₀ (by positivity) hQb hNb hN
  -- closed form
  have e1 : kM L ^ 2 = Real.exp (4 * π * L ^ 2) / Real.exp (16 * π + 16) := by
    rw [kM, ← Real.exp_nat_mul, bt_inv_mul hL, ← Real.exp_sub]; congr 1; push_cast; ring
  have e2 : Real.exp (20 * a - 4 * π * Real.exp (2 * a)) = L ^ 20 / Real.exp (4 * π * L ^ 2) := by
    have f1 : Real.exp (20 * a) = L ^ 20 := by rw [hLdef, ← Real.exp_nat_mul]; norm_num
    have f2 : Real.exp (2 * a) = L ^ 2 := by rw [hLdef, ← Real.exp_nat_mul]; norm_num
    rw [Real.exp_sub, f1, f2]
  have e3 : 720 * (25600 * L ^ 20) * S / ((kM L / 51200) ^ 2 / 5) =
      C * Real.exp (20 * a - 4 * π * Real.exp (2 * a)) := by
    rw [div_pow, e1, e2]
    have := Real.exp_pos (4 * π * L ^ 2); have := Real.exp_pos (16 * π + 16)
    simp only [C]; field_simp
  linarith

end Kaiser

#print axioms Kaiser.re_Hr_peak
#print axioms Kaiser.re_EHr_ge
#print axioms Kaiser.normSq_gK_ge
#print axioms Kaiser.lam_kaiser
