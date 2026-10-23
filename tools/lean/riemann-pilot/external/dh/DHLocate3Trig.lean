import DHLocate3Exp

/-! # Generated (`gen_locate_zero.py 3`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 16647931 / 100000`, `n ∈ NS` (part 1 of 2: `2 ≤ n ≤ 104`)

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate.Z3

theorem thL_2_r_bounds : (145306495004327759169 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 ≤ (145306501795672240831 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_2
  have hl : (28848666082762273 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 2 ∧ 16647931 / 100000 * Real.log 2 ≤ (23078932872868991 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_2_eq : (16647931 / 100000 * Real.log 2) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 + π / 2) + ((18 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_2_cos_r : (186870569160653 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) ≤ (747482310644493 / 1000000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (181633123 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) (181633123 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 - (181633123 / 250000000 : ℝ)| ≤ (3395672240831 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 - (181633123 / 250000000 : ℝ))]

theorem thL_2_sin_r : (83035214489061 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) ≤ (83035218733967 / 125000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (181633123 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73) (181633123 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 - (181633123 / 250000000 : ℝ)| ≤ (3395672240831 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 2) 73 - (181633123 / 250000000 : ℝ))]

theorem thL_2_cos : (-83035218733967 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 2) ∧ Real.cos (16647931 / 100000 * Real.log 2) ≤ (-83035214489061 / 125000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_2_sin : (186870569160653 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 2) ∧ Real.sin (16647931 / 100000 * Real.log 2) ≤ (747482310644493 / 1000000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_2 : (-83035218733967 / 125000000000000 : ℝ) ≤ cCG cZ 2 ∧ cCG cZ 2 ≤ (-83035214489061 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_cos

theorem sCB_2 : (186870569160653 / 250000000000000 : ℝ) ≤ sCG cZ 2 ∧ sCG cZ 2 ≤ (747482310644493 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_sin

theorem thL_3_r_bounds : (17096046208235945767 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 ≤ (17096047341764054233 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_3
  have hl : (182896215757217719 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 3 ∧ 16647931 / 100000 * Real.log 3 ≤ (18289621580187857 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_3_eq : (16647931 / 100000 * Real.log 3) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) + ((29 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_3_cos_r : (387575610924147 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) ≤ (775151267211253 / 1000000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (683841871 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) (683841871 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 - (683841871 / 1000000000 : ℝ)| ≤ (566764054233 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 - (683841871 / 1000000000 : ℝ))]

theorem thL_3_sin_r : (315887843799123 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) ≤ (631775732940519 / 1000000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (683841871 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116) (683841871 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 - (683841871 / 1000000000 : ℝ)| ≤ (566764054233 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 3) 116 - (683841871 / 1000000000 : ℝ))]

theorem thL_3_cos : (387575610924147 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 3) ∧ Real.cos (16647931 / 100000 * Real.log 3) ≤ (775151267211253 / 1000000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_3_sin : (315887843799123 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 3) ∧ Real.sin (16647931 / 100000 * Real.log 3) ≤ (631775732940519 / 1000000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_3 : (387575610924147 / 500000000000000 : ℝ) ≤ cCG cZ 3 ∧ cCG cZ 3 ≤ (775151267211253 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_cos

theorem sCB_3 : (315887843799123 / 500000000000000 : ℝ) ≤ sCG cZ 3 ∧ sCG cZ 3 ≤ (631775732940519 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_sin

theorem thL_4_r_bounds : (-11773136141024597319 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 ≤ (-11773131258975402681 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_4
  have hl : (230789328678091109 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 4 ∧ 16647931 / 100000 * Real.log 4 ≤ (230789328726260049 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_4_eq : (16647931 / 100000 * Real.log 4) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 + π + π / 2) + ((36 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_4_cos_r : (993077642957539 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) ≤ (62067355736127 / 62500000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(117731337 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) (-(117731337 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 - (-(117731337 / 1000000000 : ℝ))| ≤ (2441024597319 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 - (-(117731337 / 1000000000 : ℝ)))]

theorem thL_4_sin_r : (-117459577343833 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) ≤ (-117459528523341 / 1000000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (117731337 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((429995931379275224252756357971029602059390945970374641627993102300008213125186496372818114706501018118188083003352586929397 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(117731337 / 1000000000 : ℝ)) ∧ Real.sin (-(117731337 / 1000000000 : ℝ)) ≤ -((57884067685671664803189596149378441722959782188284199593282669613953825540049000335203520527853631020727 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147) (-(117731337 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 - (-(117731337 / 1000000000 : ℝ))| ≤ (2441024597319 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 4) 147 - (-(117731337 / 1000000000 : ℝ)))]

theorem thL_4_cos : (-117459577343833 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 4) ∧ Real.cos (16647931 / 100000 * Real.log 4) ≤ (-117459528523341 / 1000000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_4_sin : (-62067355736127 / 62500000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 4) ∧ Real.sin (16647931 / 100000 * Real.log 4) ≤ (-993077642957539 / 1000000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_4 : (-117459577343833 / 1000000000000000 : ℝ) ≤ cCG cZ 4 ∧ cCG cZ 4 ≤ (-117459528523341 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_cos

theorem sCB_4 : (-62067355736127 / 62500000000000 : ℝ) ≤ sCG cZ 4 ∧ sCG cZ 4 ≤ (-993077642957539 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_sin

theorem thL_6_r_bounds : (-3208439741964433093 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 ≤ (-3208438538035566907 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_6
  have hl : (37286360012991517 / 125000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 6 ∧ 16647931 / 100000 * Real.log 6 ≤ (59658176032804121 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_6_eq : (16647931 / 100000 * Real.log 6) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 + π) + ((47 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_6_cos_r : (493579969980057 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) ≤ (987160000156559 / 1000000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(160421957 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) (-(160421957 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 - (-(160421957 / 1000000000 : ℝ))| ≤ (601964433093 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 - (-(160421957 / 1000000000 : ℝ)))]

theorem thL_6_sin_r : (-159734789979797 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) ≤ (-159734729783353 / 1000000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (160421957 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((142095953180796249857628798466834349792876573355899490866252896069507227332175933995679395603253779337854118380353713380157251 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(160421957 / 1000000000 : ℝ)) ∧ Real.sin (-(160421957 / 1000000000 : ℝ)) ≤ -((6376100463240857365107672495284126499843392170075239883711939103137052213395370336369622344565060407364707 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190) (-(160421957 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 - (-(160421957 / 1000000000 : ℝ))| ≤ (601964433093 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 6) 190 - (-(160421957 / 1000000000 : ℝ)))]

theorem thL_6_cos : (-987160000156559 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 6) ∧ Real.cos (16647931 / 100000 * Real.log 6) ≤ (-493579969980057 / 500000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_6_sin : (159734729783353 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 6) ∧ Real.sin (16647931 / 100000 * Real.log 6) ≤ (159734789979797 / 1000000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_6 : (-987160000156559 / 1000000000000000 : ℝ) ≤ cCG cZ 6 ∧ cCG cZ 6 ≤ (-493579969980057 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_cos

theorem sCB_6 : (159734729783353 / 1000000000000000 : ℝ) ≤ sCG cZ 6 ∧ sCG cZ 6 ≤ (159734789979797 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_sin

theorem thL_7_r_bounds : (36973559783933943759 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 ≤ (36973565816066056241 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_7
  have hl : (323953778917588043 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 7 ∧ 16647931 / 100000 * Real.log 7 ≤ (80988444744465851 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_7_eq : (16647931 / 100000 * Real.log 7) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 + π) + ((51 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_7_cos_r : (14569107560279 / 15625000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) ≤ (116552868022399 / 125000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (92433907 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) (92433907 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 - (92433907 / 250000000 : ℝ)| ≤ (3016066056241 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 - (92433907 / 250000000 : ℝ))]

theorem thL_7_sin_r : (180684453962523 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) ≤ (361368968246369 / 1000000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (92433907 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206) (92433907 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 - (92433907 / 250000000 : ℝ)| ≤ (3016066056241 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 7) 206 - (92433907 / 250000000 : ℝ))]

theorem thL_7_cos : (-116552868022399 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 7) ∧ Real.cos (16647931 / 100000 * Real.log 7) ≤ (-14569107560279 / 15625000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_7_sin : (-361368968246369 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 7) ∧ Real.sin (16647931 / 100000 * Real.log 7) ≤ (-180684453962523 / 500000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_7 : (-116552868022399 / 125000000000000 : ℝ) ≤ cCG cZ 7 ∧ cCG cZ 7 ≤ (-14569107560279 / 15625000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_cos

theorem sCB_7 : (-361368968246369 / 1000000000000000 : ℝ) ≤ sCG cZ 7 ∧ sCG cZ 7 ≤ (-180684453962523 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_sin

theorem thL_8_r_bounds : (6088011292145547683 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 ≤ (6088011987854452317 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_8
  have hl : (346183993024091811 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 8 ∧ 16647931 / 100000 * Real.log 8 ≤ (69236798618613371 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_8_eq : (16647931 / 100000 * Real.log 8) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_8_cos_r : (16406683360447 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) ≤ (410167118799327 / 500000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (152200291 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) (152200291 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 - (152200291 / 250000000 : ℝ)| ≤ (347854452317 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 - (152200291 / 250000000 : ℝ))]

theorem thL_8_sin_r : (17871387197947 / 31250000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) ≤ (571884459905449 / 1000000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (152200291 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220) (152200291 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 - (152200291 / 250000000 : ℝ)| ≤ (347854452317 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 8) 220 - (152200291 / 250000000 : ℝ))]

theorem thL_8_cos : (16406683360447 / 20000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 8) ∧ Real.cos (16647931 / 100000 * Real.log 8) ≤ (410167118799327 / 500000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_8_sin : (17871387197947 / 31250000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 8) ∧ Real.sin (16647931 / 100000 * Real.log 8) ≤ (571884459905449 / 1000000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_8 : (16406683360447 / 20000000000000 : ℝ) ≤ cCG cZ 8 ∧ cCG cZ 8 ≤ (410167118799327 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_cos

theorem sCB_8 : (17871387197947 / 31250000000000 : ℝ) ≤ sCG cZ 8 ∧ sCG cZ 8 ≤ (571884459905449 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_sin

theorem thL_9_r_bounds : (-20311261414064971941 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 ≤ (-20311254185935028059 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_9
  have hl : (365792431529559073 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 9 ∧ 16647931 / 100000 * Real.log 9 ≤ (182896215800675781 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_9_eq : (16647931 / 100000 * Real.log 9) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 + π / 2) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_9_cos_r : (489721710701303 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) ≤ (489721746841953 / 500000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(101556289 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) (-(101556289 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 - (-(101556289 / 500000000 : ℝ))| ≤ (3614064971941 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 - (-(101556289 / 500000000 : ℝ)))]

theorem thL_9_sin_r : (-201718933311223 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) ≤ (-201718861029923 / 1000000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (101556289 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((21904781118063225644638742735757881749431291596833688319661559889013438554196658378637291033428648785244468789724860776567 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(101556289 / 500000000 : ℝ)) ∧ Real.sin (-(101556289 / 500000000 : ℝ)) ≤ -((3931627380165194343339439376384255084157605172730175172291872802508041377869141340523764252371803221311 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233) (-(101556289 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 - (-(101556289 / 500000000 : ℝ))| ≤ (3614064971941 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 9) 233 - (-(101556289 / 500000000 : ℝ)))]

theorem thL_9_cos : (201718861029923 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 9) ∧ Real.cos (16647931 / 100000 * Real.log 9) ≤ (201718933311223 / 1000000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_9_sin : (489721710701303 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 9) ∧ Real.sin (16647931 / 100000 * Real.log 9) ≤ (489721746841953 / 500000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_9 : (201718861029923 / 1000000000000000 : ℝ) ≤ cCG cZ 9 ∧ cCG cZ 9 ≤ (201718933311223 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_cos

theorem sCB_9 : (489721710701303 / 500000000000000 : ℝ) ≤ sCG cZ 9 ∧ sCG cZ 9 ≤ (489721746841953 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_sin

theorem thL_11_r_bounds : (21768344125281671431 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 ≤ (21768351474718328569 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_11
  have hl : (199599975223578279 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 11 ∧ 16647931 / 100000 * Real.log 11 ≤ (39919995052040389 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_11_eq : (16647931 / 100000 * Real.log 11) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 + π) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_11_cos_r : (244100081847183 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) ≤ (9764004008831 / 10000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (108841739 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) (108841739 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 - (108841739 / 500000000 : ℝ)| ≤ (3674718328569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 - (108841739 / 500000000 : ℝ))]

theorem thL_11_sin_r : (43193662980949 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) ≤ (215968388399113 / 1000000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (108841739 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254) (108841739 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 - (108841739 / 500000000 : ℝ)| ≤ (3674718328569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 11) 254 - (108841739 / 500000000 : ℝ))]

theorem thL_11_cos : (-9764004008831 / 10000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 11) ∧ Real.cos (16647931 / 100000 * Real.log 11) ≤ (-244100081847183 / 250000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_11_sin : (-215968388399113 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 11) ∧ Real.sin (16647931 / 100000 * Real.log 11) ≤ (-43193662980949 / 200000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_11 : (-9764004008831 / 10000000000000 : ℝ) ≤ cCG cZ 11 ∧ cCG cZ 11 ≤ (-244100081847183 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_cos

theorem sCB_11 : (-215968388399113 / 1000000000000000 : ℝ) ≤ sCG cZ 11 ∧ sCG cZ 11 ≤ (-43193662980949 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_sin

theorem thL_12_r_bounds : (56611050310584385749 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 ≤ (56611057689415614251 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_12
  have hl : (413685544450519427 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 12 ∧ 16647931 / 100000 * Real.log 12 ≤ (413685544523951967 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_12_eq : (16647931 / 100000 * Real.log 12) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 + π + π / 2) + ((65 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_12_cos_r : (421996721076861 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) ≤ (421996757972149 / 500000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (28305527 / 50000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) (28305527 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 - (28305527 / 50000000 : ℝ)| ≤ (3689415614251 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 - (28305527 / 50000000 : ℝ))]

theorem thL_12_sin_r : (536353398184561 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) ≤ (536353471972973 / 1000000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (28305527 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263) (28305527 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 - (28305527 / 50000000 : ℝ)| ≤ (3689415614251 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 12) 263 - (28305527 / 50000000 : ℝ))]

theorem thL_12_cos : (536353398184561 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 12) ∧ Real.cos (16647931 / 100000 * Real.log 12) ≤ (536353471972973 / 1000000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_12_sin : (-421996757972149 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 12) ∧ Real.sin (16647931 / 100000 * Real.log 12) ≤ (-421996721076861 / 500000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_12 : (536353398184561 / 1000000000000000 : ℝ) ≤ cCG cZ 12 ∧ cCG cZ 12 ≤ (536353471972973 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_cos

theorem sCB_12 : (-421996757972149 / 500000000000000 : ℝ) ≤ sCG cZ 12 ∧ sCG cZ 12 ≤ (-421996721076861 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_sin

theorem thL_13_r_bounds : (-1535010586499053559 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 ≤ (-1535010126000946441 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_13
  have hl : (85402199838906353 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 13 ∧ 16647931 / 100000 * Real.log 13 ≤ (427010999268051729 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_13_eq : (16647931 / 100000 * Real.log 13) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) + ((68 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_13_cos_r : (242497794210083 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) ≤ (96999125052003 / 100000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(245601657 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) (-(245601657 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 - (-(245601657 / 1000000000 : ℝ))| ≤ (230249053559 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 - (-(245601657 / 1000000000 : ℝ)))]

theorem thL_13_sin_r : (-243140007604117 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) ≤ (-243139933924419 / 1000000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (245601657 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((890086804973833730489112557288677449446964547607456333568295815681901790764166869156976350429587624115344871867714053609957 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(245601657 / 1000000000 : ℝ)) ∧ Real.sin (-(245601657 / 1000000000 : ℝ)) ≤ -((17117053941804494683346669221981192881103076052256922844336786773382024990250335317834939753020093663521 / 70400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272) (-(245601657 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 - (-(245601657 / 1000000000 : ℝ))| ≤ (230249053559 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 13) 272 - (-(245601657 / 1000000000 : ℝ)))]

theorem thL_13_cos : (242497794210083 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 13) ∧ Real.cos (16647931 / 100000 * Real.log 13) ≤ (96999125052003 / 100000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_13_sin : (-243140007604117 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 13) ∧ Real.sin (16647931 / 100000 * Real.log 13) ≤ (-243139933924419 / 1000000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_13 : (242497794210083 / 250000000000000 : ℝ) ≤ cCG cZ 13 ∧ cCG cZ 13 ≤ (96999125052003 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_cos

theorem sCB_13 : (-243140007604117 / 1000000000000000 : ℝ) ≤ sCG cZ 13 ∧ sCG cZ 13 ≤ (-243139933924419 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_sin

theorem thL_14_r_bounds : (-1186320597925936539 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 ≤ (-1186320412074063461 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_14
  have hl : (439348443264177741 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 14 ∧ 16647931 / 100000 * Real.log 14 ≤ (109837110834435357 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_14_eq : (16647931 / 100000 * Real.log 14) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) + ((70 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_14_cos_r : (111188544604237 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) ≤ (444754215587459 / 500000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(237264101 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) (-(237264101 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 - (-(237264101 / 500000000 : ℝ))| ≤ (92925936539 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 - (-(237264101 / 500000000 : ℝ)))]

theorem thL_14_sin_r : (-456918866937171 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) ≤ (-456918792596411 / 1000000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (237264101 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((347319709090515146857781038373632514096603923086766874610658549410209154345035732214486780969565176499725312609356397613301 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(237264101 / 500000000 : ℝ)) ∧ Real.sin (-(237264101 / 500000000 : ℝ)) ≤ -((8905633566423271683331269850248466685641516130103596228197088768056592085853106681255445953972240544899 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280) (-(237264101 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 - (-(237264101 / 500000000 : ℝ))| ≤ (92925936539 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 14) 280 - (-(237264101 / 500000000 : ℝ)))]

theorem thL_14_cos : (111188544604237 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 14) ∧ Real.cos (16647931 / 100000 * Real.log 14) ≤ (444754215587459 / 500000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_14_sin : (-456918866937171 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 14) ∧ Real.sin (16647931 / 100000 * Real.log 14) ≤ (-456918792596411 / 1000000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_14 : (111188544604237 / 125000000000000 : ℝ) ≤ cCG cZ 14 ∧ cCG cZ 14 ≤ (444754215587459 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_cos

theorem sCB_14 : (-456918866937171 / 1000000000000000 : ℝ) ≤ sCG cZ 14 ∧ sCG cZ 14 ≤ (-456918792596411 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_sin

theorem thL_16_r_bounds : (-11773135395812097319 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 ≤ (-11773131104187902681 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_16
  have hl : (461578657369914541 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 16 ∧ 16647931 / 100000 * Real.log 16 ≤ (57697332181951981 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_16_eq : (16647931 / 100000 * Real.log 16) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 + π) + ((73 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_16_cos_r : (972406466032677 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) ≤ (486203275932581 / 500000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(47092533 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) (-(47092533 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 - (-(47092533 / 200000000 : ℝ))| ≤ (2145812097319 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 - (-(47092533 / 200000000 : ℝ)))]

theorem thL_16_sin_r : (-233292951839283 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) ≤ (-116646433003399 / 500000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (47092533 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((699628487463293945087287167296876865612100608796912101208851356834837396223556170082463265918636779603162228614113 / 2998927360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(47092533 / 200000000 : ℝ)) ∧ Real.sin (-(47092533 / 200000000 : ℝ)) ≤ -((2354518948193777688728716796362025096794305340469585820539233390796412656556360715199932488366243 / 10092544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294) (-(47092533 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 - (-(47092533 / 200000000 : ℝ))| ≤ (2145812097319 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 16) 294 - (-(47092533 / 200000000 : ℝ)))]

theorem thL_16_cos : (-486203275932581 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 16) ∧ Real.cos (16647931 / 100000 * Real.log 16) ≤ (-972406466032677 / 1000000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_16_sin : (116646433003399 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 16) ∧ Real.sin (16647931 / 100000 * Real.log 16) ≤ (233292951839283 / 1000000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_16 : (-486203275932581 / 500000000000000 : ℝ) ≤ cCG cZ 16 ∧ cCG cZ 16 ≤ (-972406466032677 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_cos

theorem sCB_16 : (116646433003399 / 500000000000000 : ℝ) ≤ sCG cZ 16 ∧ sCG cZ 16 ≤ (233292951839283 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_sin

theorem thL_17_r_bounds : (432504539139266769 / 1000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 ≤ (432504632860733231 / 1000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_17
  have hl : (117917850644452171 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 17 ∧ 16647931 / 100000 * Real.log 17 ≤ (471671402671329719 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_17_eq : (16647931 / 100000 * Real.log 17) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) + ((75 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_17_cos_r : (907918764182747 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) ≤ (56744928619019 / 62500000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (216252293 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) (216252293 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 - (216252293 / 500000000 : ℝ)| ≤ (46860733231 / 1000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 - (216252293 / 500000000 : ℝ))]

theorem thL_17_sin_r : (20957301428753 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) ≤ (41914612229653 / 100000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (216252293 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300) (216252293 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 - (216252293 / 500000000 : ℝ)| ≤ (46860733231 / 1000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 17) 300 - (216252293 / 500000000 : ℝ))]

theorem thL_17_cos : (907918764182747 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 17) ∧ Real.cos (16647931 / 100000 * Real.log 17) ≤ (56744928619019 / 62500000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_17_sin : (20957301428753 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 17) ∧ Real.sin (16647931 / 100000 * Real.log 17) ≤ (41914612229653 / 100000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_17 : (907918764182747 / 1000000000000000 : ℝ) ≤ cCG cZ 17 ∧ cCG cZ 17 ≤ (56744928619019 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_cos

theorem sCB_17 : (20957301428753 / 50000000000000 : ℝ) ≤ sCG cZ 17 ∧ sCG cZ 17 ≤ (41914612229653 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_sin

theorem thL_18_r_bounds : (52341987459965251409 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 ≤ (52341997340034748591 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_18
  have hl : (240593547936919009 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 18 ∧ 16647931 / 100000 * Real.log 18 ≤ (120296773993134581 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_18_eq : (16647931 / 100000 * Real.log 18) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 + π) + ((76 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_18_cos_r : (866114766330717 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) ≤ (108264358141537 / 125000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (130854981 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) (130854981 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 - (130854981 / 250000000 : ℝ)| ≤ (4940034748591 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 - (130854981 / 250000000 : ℝ))]

theorem thL_18_sin_r : (249922526287917 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) ≤ (249922575688283 / 500000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (130854981 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306) (130854981 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 - (130854981 / 250000000 : ℝ)| ≤ (4940034748591 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 18) 306 - (130854981 / 250000000 : ℝ))]

theorem thL_18_cos : (-108264358141537 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 18) ∧ Real.cos (16647931 / 100000 * Real.log 18) ≤ (-866114766330717 / 1000000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_18_sin : (-249922575688283 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 18) ∧ Real.sin (16647931 / 100000 * Real.log 18) ≤ (-249922526287917 / 500000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_18 : (-108264358141537 / 125000000000000 : ℝ) ≤ cCG cZ 18 ∧ cCG cZ 18 ≤ (-866114766330717 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_cos

theorem sCB_18 : (-249922575688283 / 500000000000000 : ℝ) ≤ sCG cZ 18 ∧ sCG cZ 18 ≤ (-249922526287917 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_sin

theorem thL_19_r_bounds : (1246445047100189997 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 ≤ (1246446327899810003 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_19
  have hl : (490188169564029517 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 19 ∧ 16647931 / 100000 * Real.log 19 ≤ (49018816966623973 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_19_eq : (16647931 / 100000 * Real.log 19) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) + ((78 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_19_cos_r : (995032460954437 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) ≤ (124379070427301 / 125000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (19943131 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) (19943131 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 - (19943131 / 200000000 : ℝ)| ≤ (640399810003 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 - (19943131 / 200000000 : ℝ))]

theorem thL_19_sin_r : (9955043692341 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) ≤ (4977526969369 / 50000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (19943131 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312) (19943131 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 - (19943131 / 200000000 : ℝ)| ≤ (640399810003 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 19) 312 - (19943131 / 200000000 : ℝ))]

theorem thL_19_cos : (995032460954437 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 19) ∧ Real.cos (16647931 / 100000 * Real.log 19) ≤ (124379070427301 / 125000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_19_sin : (9955043692341 / 100000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 19) ∧ Real.sin (16647931 / 100000 * Real.log 19) ≤ (4977526969369 / 50000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_19 : (995032460954437 / 1000000000000000 : ℝ) ≤ cCG cZ 19 ∧ cCG cZ 19 ≤ (124379070427301 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_cos

theorem sCB_19 : (9955043692341 / 100000000000000 : ℝ) ≤ sCG cZ 19 ∧ sCG cZ 19 ≤ (4977526969369 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_sin

theorem thL_21_r_bounds : (-103443773666635002581 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 ≤ (-103443752333364997419 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_21
  have hl : (506849994686418433 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 21 ∧ 16647931 / 100000 * Real.log 21 ≤ (253424997396383579 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_21_eq : (16647931 / 100000 * Real.log 21) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 + π + π / 2) + ((80 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_21_cos_r : (434598841932093 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) ≤ (434598895265651 / 500000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(103443763 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) (-(103443763 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 - (-(103443763 / 200000000 : ℝ))| ≤ (10666635002581 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 - (-(103443763 / 200000000 : ℝ)))]

theorem thL_21_sin_r : (-494464706922953 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) ≤ (-494464600256571 / 1000000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (103443763 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2522350946523821376688230395915981031343320951120044372574966491953782740278392180380397518940394924800385876149736003 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(103443763 / 200000000 : ℝ)) ∧ Real.sin (-(103443763 / 200000000 : ℝ)) ≤ -((404222908096741359327155649670241810429084530164326845277941320283805332744929303060518723920612213 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323) (-(103443763 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 - (-(103443763 / 200000000 : ℝ))| ≤ (10666635002581 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 21) 323 - (-(103443763 / 200000000 : ℝ)))]

theorem thL_21_cos : (-494464706922953 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 21) ∧ Real.cos (16647931 / 100000 * Real.log 21) ≤ (-494464600256571 / 1000000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_21_sin : (-434598895265651 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 21) ∧ Real.sin (16647931 / 100000 * Real.log 21) ≤ (-434598841932093 / 500000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_21 : (-494464706922953 / 1000000000000000 : ℝ) ≤ cCG cZ 21 ∧ cCG cZ 21 ≤ (-494464600256571 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_cos

theorem sCB_21 : (-434598895265651 / 500000000000000 : ℝ) ≤ sCG cZ 21 ∧ sCG cZ 21 ≤ (-434598841932093 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_sin

theorem thL_22_r_bounds : (-7832254989722123657 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 ≤ (-7832253635277876343 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_22
  have hl : (64324326848791193 / 125000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 22 ∧ 16647931 / 100000 * Real.log 22 ≤ (514594614897903861 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_22_eq : (16647931 / 100000 * Real.log 22) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_22_cos_r : (810037397468841 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) ≤ (810037505832027 / 1000000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(125316069 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) (-(125316069 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 - (-(125316069 / 200000000 : ℝ))| ≤ (677222123657 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 - (-(125316069 / 200000000 : ℝ)))]

theorem thL_22_sin_r : (-146594549364657 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) ≤ (-586378089102719 / 1000000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (125316069 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((12309538200336745138329851351774363508282092468908131534446476430830442333048123720025857043172573551020532228415863 / 20992491520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(125316069 / 200000000 : ℝ)) ∧ Real.sin (-(125316069 / 200000000 : ℝ)) ≤ -((5918047211696639306936753167452664883159560378022945531317658842517997741638863744777702926645651 / 10092544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328) (-(125316069 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 - (-(125316069 / 200000000 : ℝ))| ≤ (677222123657 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 22) 328 - (-(125316069 / 200000000 : ℝ)))]

theorem thL_22_cos : (810037397468841 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 22) ∧ Real.cos (16647931 / 100000 * Real.log 22) ≤ (810037505832027 / 1000000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_22_sin : (-146594549364657 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 22) ∧ Real.sin (16647931 / 100000 * Real.log 22) ≤ (-586378089102719 / 1000000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_22 : (810037397468841 / 1000000000000000 : ℝ) ≤ cCG cZ 22 ∧ cCG cZ 22 ≤ (810037505832027 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_cos

theorem sCB_22 : (-146594549364657 / 250000000000000 : ℝ) ≤ sCG cZ 22 ∧ sCG cZ 22 ≤ (-586378089102719 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_sin

theorem thL_23_r_bounds : (24526652768638370699 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 ≤ (24526658231361629301 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_23
  have hl : (104398982710255689 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 23 ∧ 16647931 / 100000 * Real.log 23 ≤ (260997456829872127 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_23_eq : (16647931 / 100000 * Real.log 23) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_23_cos_r : (441040891622431 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) ≤ (882081892499733 / 1000000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (49053311 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) (49053311 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 - (49053311 / 100000000 : ℝ)| ≤ (2731361629301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 - (49053311 / 100000000 : ℝ))]

theorem thL_23_sin_r : (471096147114469 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) ≤ (471096256368951 / 1000000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (49053311 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332) (49053311 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 - (49053311 / 100000000 : ℝ)| ≤ (2731361629301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 23) 332 - (49053311 / 100000000 : ℝ))]

theorem thL_23_cos : (441040891622431 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 23) ∧ Real.cos (16647931 / 100000 * Real.log 23) ≤ (882081892499733 / 1000000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_23_sin : (471096147114469 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 23) ∧ Real.sin (16647931 / 100000 * Real.log 23) ≤ (471096256368951 / 1000000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_23 : (441040891622431 / 500000000000000 : ℝ) ≤ cCG cZ 23 ∧ cCG cZ 23 ≤ (882081892499733 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_cos

theorem sCB_23 : (471096147114469 / 1000000000000000 : ℝ) ≤ sCG cZ 23 ∧ sCG cZ 23 ≤ (471096256368951 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_sin

theorem thL_24_r_bounds : (-27815333673487931949 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 ≤ (-27815322726512068051 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_24
  have hl : (264540104396745861 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 24 ∧ 16647931 / 100000 * Real.log 24 ≤ (25833994575323 / 48828125000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_24_eq : (16647931 / 100000 * Real.log 24) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 + π / 2) + ((84 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_24_cos_r : (480782047730413 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) ≤ (480782102465293 / 500000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(139076641 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) (-(139076641 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 - (-(139076641 / 500000000 : ℝ))| ≤ (5473487931949 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 - (-(139076641 / 500000000 : ℝ)))]

theorem thL_24_sin_r : (-274580434693843 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) ≤ (-68645081306021 / 250000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (139076641 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((18974362318851745571865912990163341311951169553086314445739766786590026638507403989262332176833995053455465501480973179011 / 69103125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(139076641 / 500000000 : ℝ)) ∧ Real.sin (-(139076641 / 500000000 : ℝ)) ≤ -((486522110739788331020098658246860767482325867551352265837764252157789251294820394425685192883619806269 / 1771875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337) (-(139076641 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 - (-(139076641 / 500000000 : ℝ))| ≤ (5473487931949 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 24) 337 - (-(139076641 / 500000000 : ℝ)))]

theorem thL_24_cos : (68645081306021 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 24) ∧ Real.cos (16647931 / 100000 * Real.log 24) ≤ (274580434693843 / 1000000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_24_sin : (480782047730413 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 24) ∧ Real.sin (16647931 / 100000 * Real.log 24) ≤ (480782102465293 / 500000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_24 : (68645081306021 / 250000000000000 : ℝ) ≤ cCG cZ 24 ∧ cCG cZ 24 ≤ (274580434693843 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_cos

theorem sCB_24 : (480782047730413 / 500000000000000 : ℝ) ≤ sCG cZ 24 ∧ sCG cZ 24 ≤ (480782102465293 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_sin

theorem thL_26_r_bounds : (9618615857262432687 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 ≤ (9618618062737567313 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_26
  have hl : (542405663537390597 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 26 ∧ 16647931 / 100000 * Real.log 26 ≤ (135601415911844053 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_26_eq : (16647931 / 100000 * Real.log 26) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 + π / 2) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_26_cos_r : (443282318600701 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) ≤ (886564747475479 / 1000000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (15029089 / 31250000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) (15029089 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 - (15029089 / 31250000 : ℝ)| ≤ (1102737567313 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 - (15029089 / 31250000 : ℝ))]

theorem thL_26_sin_r : (231302288837251 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) ≤ (28912792996767 / 62500000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (15029089 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345) (15029089 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 - (15029089 / 31250000 : ℝ)| ≤ (1102737567313 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 26) 345 - (15029089 / 31250000 : ℝ))]

theorem thL_26_cos : (-28912792996767 / 62500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 26) ∧ Real.cos (16647931 / 100000 * Real.log 26) ≤ (-231302288837251 / 500000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_26_sin : (443282318600701 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 26) ∧ Real.sin (16647931 / 100000 * Real.log 26) ≤ (886564747475479 / 1000000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_26 : (-28912792996767 / 62500000000000 : ℝ) ≤ cCG cZ 26 ∧ cCG cZ 26 ≤ (-231302288837251 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_cos

theorem sCB_26 : (443282318600701 / 500000000000000 : ℝ) ≤ sCG cZ 26 ∧ sCG cZ 26 ≤ (886564747475479 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_sin

theorem thL_27_r_bounds : (96145849537847977397 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 ≤ (96145871662152022603 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_27
  have hl : (1714652022809713 / 3125000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 27 ∧ 16647931 / 100000 * Real.log 27 ≤ (274344323704688657 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_27_eq : (16647931 / 100000 * Real.log 27) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 + π / 2) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_27_cos_r : (88665785467131 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) ≤ (886657965293149 / 1000000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (480729303 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) (480729303 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 - (480729303 / 1000000000 : ℝ)| ≤ (11062152022603 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 - (480729303 / 1000000000 : ℝ))]

theorem thL_27_sin_r : (462425885425323 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) ≤ (57803249505857 / 125000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (480729303 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349) (480729303 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 - (480729303 / 1000000000 : ℝ)| ≤ (11062152022603 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 27) 349 - (480729303 / 1000000000 : ℝ))]

theorem thL_27_cos : (-57803249505857 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 27) ∧ Real.cos (16647931 / 100000 * Real.log 27) ≤ (-462425885425323 / 1000000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_27_sin : (88665785467131 / 100000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 27) ∧ Real.sin (16647931 / 100000 * Real.log 27) ≤ (886657965293149 / 1000000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_27 : (-57803249505857 / 125000000000000 : ℝ) ≤ cCG cZ 27 ∧ cCG cZ 27 ≤ (-462425885425323 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_cos

theorem sCB_27 : (88665785467131 / 100000000000000 : ℝ) ≤ sCG cZ 27 ∧ sCG cZ 27 ≤ (886657965293149 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_sin

theorem thL_28_r_bounds : (50400849674233882009 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 ≤ (50400871925766117991 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_28
  have hl : (138685776901742419 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 28 ∧ 16647931 / 100000 * Real.log 28 ≤ (138685776929364401 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_28_eq : (16647931 / 100000 * Real.log 28) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_28_cos_r : (484207273747553 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) ≤ (3782869760753 / 3906250000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (15750269 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) (15750269 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 - (15750269 / 62500000 : ℝ)| ≤ (11125766117991 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 - (15750269 / 62500000 : ℝ))]

theorem thL_28_sin_r : (124672700214119 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) ≤ (2493455116859 / 10000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (15750269 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353) (15750269 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 - (15750269 / 62500000 : ℝ)| ≤ (11125766117991 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 28) 353 - (15750269 / 62500000 : ℝ))]

theorem thL_28_cos : (-2493455116859 / 10000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 28) ∧ Real.cos (16647931 / 100000 * Real.log 28) ≤ (-124672700214119 / 500000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_28_sin : (484207273747553 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 28) ∧ Real.sin (16647931 / 100000 * Real.log 28) ≤ (3782869760753 / 3906250000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_28 : (-2493455116859 / 10000000000000 : ℝ) ≤ cCG cZ 28 ∧ cCG cZ 28 ≤ (-124672700214119 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_cos

theorem sCB_28 : (484207273747553 / 500000000000000 : ℝ) ≤ sCG cZ 28 ∧ sCG cZ 28 ≤ (3782869760753 / 3906250000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_sin

theorem thL_29_r_bounds : (-37840469932635413379 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 ≤ (-37840447667364586621 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_29
  have hl : (140146271579028729 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 29 ∧ 16647931 / 100000 * Real.log 29 ≤ (17518283950836663 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_29_eq : (16647931 / 100000 * Real.log 29) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 + π / 2) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_29_cos_r : (982154520870043 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) ≤ (491077316098199 / 500000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(94601147 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) (-(94601147 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 - (-(94601147 / 500000000 : ℝ))| ≤ (11132635413379 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 - (-(94601147 / 500000000 : ℝ)))]

theorem thL_29_sin_r : (-11754721247727 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) ≤ (-188075428637277 / 1000000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (94601147 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((142962640711548458772514268430244446517749990832957678325934329673904307342291547006995682034215707929861230884490404963627 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(94601147 / 500000000 : ℝ)) ∧ Real.sin (-(94601147 / 500000000 : ℝ)) ≤ -((3665708736193550223690060787912075156272799687982213793686567546652065294007702622698385072320024144797 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357) (-(94601147 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 - (-(94601147 / 500000000 : ℝ))| ≤ (11132635413379 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 29) 357 - (-(94601147 / 500000000 : ℝ)))]

theorem thL_29_cos : (188075428637277 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 29) ∧ Real.cos (16647931 / 100000 * Real.log 29) ≤ (11754721247727 / 62500000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_29_sin : (982154520870043 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 29) ∧ Real.sin (16647931 / 100000 * Real.log 29) ≤ (491077316098199 / 500000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_29 : (188075428637277 / 1000000000000000 : ℝ) ≤ cCG cZ 29 ∧ cCG cZ 29 ≤ (11754721247727 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_cos

theorem sCB_29 : (982154520870043 / 1000000000000000 : ℝ) ≤ sCG cZ 29 ∧ sCG cZ 29 ≤ (491077316098199 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_sin

theorem thL_31_r_bounds : (-4102131388558120077 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 ≤ (-4102125811441879923 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_31
  have hl : (571687820325571207 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 31 ∧ 16647931 / 100000 * Real.log 31 ≤ (571687820436469311 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_31_eq : (16647931 / 100000 * Real.log 31) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) + ((91 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_31_cos_r : (498318169875503 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) ≤ (249159112823333 / 250000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(20510643 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) (-(20510643 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 - (-(20510643 / 250000000 : ℝ))| ≤ (2788558120077 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 - (-(20510643 / 250000000 : ℝ)))]

theorem thL_31_sin_r : (-81950620873417 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) ≤ (-20487627332773 / 250000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (20510643 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4470417331551512672229849509913514009858263313324041366514438093985606876280622963483019804835645249720223373999943 / 54550170898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(20510643 / 250000000 : ℝ)) ∧ Real.sin (-(20510643 / 250000000 : ℝ)) ≤ -((9628591175649411909417993446262805119098675723535190147996380462374930713461779865436298943511653 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364) (-(20510643 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 - (-(20510643 / 250000000 : ℝ))| ≤ (2788558120077 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 31) 364 - (-(20510643 / 250000000 : ℝ)))]

theorem thL_31_cos : (498318169875503 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 31) ∧ Real.cos (16647931 / 100000 * Real.log 31) ≤ (249159112823333 / 250000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_31_sin : (-81950620873417 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 31) ∧ Real.sin (16647931 / 100000 * Real.log 31) ≤ (-20487627332773 / 250000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_31 : (498318169875503 / 500000000000000 : ℝ) ≤ cCG cZ 31 ∧ cCG cZ 31 ≤ (249159112823333 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_cos

theorem sCB_31 : (-81950620873417 / 1000000000000000 : ℝ) ≤ sCG cZ 31 ∧ sCG cZ 31 ≤ (-20487627332773 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_sin

theorem thL_32_r_bounds : (49106978037578425741 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 ≤ (49106989162421574259 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_32
  have hl : (576973321714368621 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 32 ∧ 16647931 / 100000 * Real.log 32 ≤ (23078932873014051 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_32_eq : (16647931 / 100000 * Real.log 32) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 + π + π / 2) + ((91 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_32_cos_r : (440914402813633 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) ≤ (881828916876109 / 1000000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (122767459 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) (122767459 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 - (122767459 / 250000000 : ℝ)| ≤ (5562421574259 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 - (122767459 / 250000000 : ℝ))]

theorem thL_32_sin_r : (471569514495799 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) ≤ (471569625744247 / 1000000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (122767459 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367) (122767459 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 - (122767459 / 250000000 : ℝ)| ≤ (5562421574259 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 32) 367 - (122767459 / 250000000 : ℝ))]

theorem thL_32_cos : (471569514495799 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 32) ∧ Real.cos (16647931 / 100000 * Real.log 32) ≤ (471569625744247 / 1000000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_32_sin : (-881828916876109 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 32) ∧ Real.sin (16647931 / 100000 * Real.log 32) ≤ (-440914402813633 / 500000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_32 : (471569514495799 / 1000000000000000 : ℝ) ≤ cCG cZ 32 ∧ cCG cZ 32 ≤ (471569625744247 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_cos

theorem sCB_32 : (-881828916876109 / 1000000000000000 : ℝ) ≤ sCG cZ 32 ∧ sCG cZ 32 ≤ (-440914402813633 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_sin

theorem thL_33_r_bounds : (-66927102489953426567 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 ≤ (-66927091310046573433 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_33
  have hl : (58209616621675559 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 33 ∧ 16647931 / 100000 * Real.log 33 ≤ (29104808316390309 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_33_eq : (16647931 / 100000 * Real.log 33) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 + π + π / 2) + ((92 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_33_cos_r : (392137059832159 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) ≤ (784274231480249 / 1000000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(669270969 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) (-(669270969 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 - (-(669270969 / 1000000000 : ℝ))| ≤ (5589953426567 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 - (-(669270969 / 1000000000 : ℝ)))]

theorem thL_33_sin_r : (-310207223835541 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) ≤ (-77551791983893 / 125000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (669270969 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2271213005397279300332101345474039568850557021912822937861490783968908513498440965145931512191271070331326422511109774275109 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(669270969 / 1000000000 : ℝ)) ∧ Real.sin (-(669270969 / 1000000000 : ℝ)) ≤ -((305740212264590591550828533520125525872728287429913452952548420283423657400284187876497152698588736723751 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371) (-(669270969 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 - (-(669270969 / 1000000000 : ℝ))| ≤ (5589953426567 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 33) 371 - (-(669270969 / 1000000000 : ℝ)))]

theorem thL_33_cos : (-310207223835541 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 33) ∧ Real.cos (16647931 / 100000 * Real.log 33) ≤ (-77551791983893 / 125000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_33_sin : (-784274231480249 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 33) ∧ Real.sin (16647931 / 100000 * Real.log 33) ≤ (-392137059832159 / 500000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_33 : (-310207223835541 / 500000000000000 : ℝ) ≤ cCG cZ 33 ∧ cCG cZ 33 ≤ (-77551791983893 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_cos

theorem sCB_33 : (-784274231480249 / 1000000000000000 : ℝ) ≤ sCG cZ 33 ∧ sCG cZ 33 ≤ (-392137059832159 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_sin

theorem thL_34_r_bounds : (-41175929792924959389 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 ≤ (-41175918607075040611 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_34
  have hl : (293533033461681043 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 34 ∧ 16647931 / 100000 * Real.log 34 ≤ (4696528536275741 / 8000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_34_eq : (16647931 / 100000 * Real.log 34) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 + π) + ((93 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_34_cos_r : (916418097764529 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) ≤ (458209104811539 / 500000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(205879621 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) (-(205879621 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 - (-(205879621 / 500000000 : ℝ))| ≤ (5592924959389 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 - (-(205879621 / 500000000 : ℝ)))]

theorem thL_34_sin_r : (-200111101858847 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) ≤ (-50027761482399 / 125000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (205879621 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((304222612170326530663635941972609394763069637860792820209231157033369142651872906163178212363445450200063390578541828706261 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(205879621 / 500000000 : ℝ)) ∧ Real.sin (-(205879621 / 500000000 : ℝ)) ≤ -((7800579799239111198663754420179398163398833336018043982280582430865724759182560622978020336669130062179 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374) (-(205879621 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 - (-(205879621 / 500000000 : ℝ))| ≤ (5592924959389 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 34) 374 - (-(205879621 / 500000000 : ℝ)))]

theorem thL_34_cos : (-458209104811539 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 34) ∧ Real.cos (16647931 / 100000 * Real.log 34) ≤ (-916418097764529 / 1000000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_34_sin : (50027761482399 / 125000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 34) ∧ Real.sin (16647931 / 100000 * Real.log 34) ≤ (200111101858847 / 500000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_34 : (-458209104811539 / 500000000000000 : ℝ) ≤ cCG cZ 34 ∧ cCG cZ 34 ≤ (-916418097764529 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_cos

theorem sCB_34 : (50027761482399 / 125000000000000 : ℝ) ≤ sCG cZ 34 ∧ sCG cZ 34 ≤ (200111101858847 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_sin

theorem thL_36_r_bounds : (-3208439619411533093 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 ≤ (-3208438500588466907 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_36
  have hl : (298290880110059781 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 36 ∧ 16647931 / 100000 * Real.log 36 ≤ (596581760331306441 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_36_eq : (16647931 / 100000 * Real.log 36) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) + ((95 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_36_cos_r : (189793911910587 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) ≤ (189793934287049 / 200000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(160421953 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) (-(160421953 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 - (-(160421953 / 500000000 : ℝ))| ≤ (559411533093 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 - (-(160421953 / 500000000 : ℝ)))]

theorem thL_36_sin_r : (-315367569913339 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) ≤ (-39420932253879 / 125000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (160421953 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((239721688128551034011703432693648433153700727251907273788572546695581896130306332529488387280761297041578053821971670948673 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(160421953 / 500000000 : ℝ)) ∧ Real.sin (-(160421953 / 500000000 : ℝ)) ≤ -((6146709952014127882231757329637519057898997271347954481320800636985091192460917242589875897599296554303 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380) (-(160421953 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 - (-(160421953 / 500000000 : ℝ))| ≤ (559411533093 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 36) 380 - (-(160421953 / 500000000 : ℝ)))]

theorem thL_36_cos : (189793911910587 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 36) ∧ Real.cos (16647931 / 100000 * Real.log 36) ≤ (189793934287049 / 200000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_36_sin : (-315367569913339 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 36) ∧ Real.sin (16647931 / 100000 * Real.log 36) ≤ (-39420932253879 / 125000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_36 : (189793911910587 / 200000000000000 : ℝ) ≤ cCG cZ 36 ∧ cCG cZ 36 ≤ (189793934287049 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_cos

theorem sCB_36 : (-315367569913339 / 1000000000000000 : ℝ) ≤ sCG cZ 36 ∧ sCG cZ 36 ≤ (-39420932253879 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_sin

theorem thL_37_r_bounds : (-94374124957009433401 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 ≤ (-94374102642990566599 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_37
  have hl : (300571561268830179 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 37 ∧ 16647931 / 100000 * Real.log 37 ≤ (300571561324438691 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_37_eq : (16647931 / 100000 * Real.log 37) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 + π + π / 2) + ((95 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_37_cos_r : (89071951804719 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) ≤ (44535981480877 / 50000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(471870569 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) (-(471870569 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 - (-(471870569 / 1000000000 : ℝ))| ≤ (11157009433401 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 - (-(471870569 / 1000000000 : ℝ)))]

theorem thL_37_sin_r : (-454553287862067 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) ≤ (-227276588145981 / 500000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (471870569 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2830512430850823927530315658258969379195537933910492419254213461629024586212489157726217873200695461910700065833892838372523209 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(471870569 / 1000000000 : ℝ)) ∧ Real.sin (-(471870569 / 1000000000 : ℝ)) ≤ -((18144310454171579638417562621511408770097355652730689429032327941199674949738149531816934060987193942348231 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383) (-(471870569 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 - (-(471870569 / 1000000000 : ℝ))| ≤ (11157009433401 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 37) 383 - (-(471870569 / 1000000000 : ℝ)))]

theorem thL_37_cos : (-454553287862067 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 37) ∧ Real.cos (16647931 / 100000 * Real.log 37) ≤ (-227276588145981 / 500000000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_37_sin : (-44535981480877 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 37) ∧ Real.sin (16647931 / 100000 * Real.log 37) ≤ (-89071951804719 / 100000000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_37 : (-454553287862067 / 1000000000000000 : ℝ) ≤ cCG cZ 37 ∧ cCG cZ 37 ≤ (-227276588145981 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_cos

theorem sCB_37 : (-44535981480877 / 50000000000000 : ℝ) ≤ sCG cZ 37 ∧ sCG cZ 37 ≤ (-89071951804719 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_sin

theorem thL_38_r_bounds : (-74454823202557002471 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 ≤ (-74454811997442997529 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_38
  have hl : (24223313356432181 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 38 ∧ 16647931 / 100000 * Real.log 38 ≤ (605582834022046497 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_38_eq : (16647931 / 100000 * Real.log 38) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 + π) + ((96 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_38_cos_r : (735394095188001 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) ≤ (735394207299729 / 1000000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(46534261 / 62500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) (-(46534261 / 62500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 - (-(46534261 / 62500000 : ℝ))| ≤ (5602557002471 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 - (-(46534261 / 62500000 : ℝ)))]

theorem thL_38_sin_r : (-338819833466969 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) ≤ (-677639554879327 / 1000000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (46534261 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((936956279680225381048942938388213917415328490431381407847014270972576405173515077322408728932349447055416794181 / 1382676373395952396094799041748046875000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(46534261 / 62500000 : ℝ)) ∧ Real.sin (-(46534261 / 62500000 : ℝ)) ≤ -((1537569279467368255866849230163651194236425491971331033524932808452670094814699558929239965139 / 2269007381983101367950439453125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386) (-(46534261 / 62500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 - (-(46534261 / 62500000 : ℝ))| ≤ (5602557002471 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 38) 386 - (-(46534261 / 62500000 : ℝ)))]

theorem thL_38_cos : (-735394207299729 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 38) ∧ Real.cos (16647931 / 100000 * Real.log 38) ≤ (-735394095188001 / 1000000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_38_sin : (677639554879327 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 38) ∧ Real.sin (16647931 / 100000 * Real.log 38) ≤ (338819833466969 / 500000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_38 : (-735394207299729 / 1000000000000000 : ℝ) ≤ cCG cZ 38 ∧ cCG cZ 38 ≤ (-735394095188001 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_cos

theorem sCB_38 : (677639554879327 / 1000000000000000 : ℝ) ≤ sCG cZ 38 ∧ sCG cZ 38 ≤ (338819833466969 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_sin

theorem thL_39_r_bounds : (10956004175659731531 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 ≤ (10956006974340268469 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_39
  have hl : (609907214964130777 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 39 ∧ 16647931 / 100000 * Real.log 39 ≤ (609907215075393499 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_39_eq : (16647931 / 100000 * Real.log 39) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) + ((97 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_39_cos_r : (905499764409449 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) ≤ (113187484544597 / 125000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (438240223 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) (438240223 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 - (438240223 / 1000000000 : ℝ)| ≤ (1399340268469 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 - (438240223 / 1000000000 : ℝ))]

theorem thL_39_sin_r : (424346589218799 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) ≤ (16973868046641 / 40000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (438240223 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388) (438240223 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 - (438240223 / 1000000000 : ℝ)| ≤ (1399340268469 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 39) 388 - (438240223 / 1000000000 : ℝ))]

theorem thL_39_cos : (905499764409449 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 39) ∧ Real.cos (16647931 / 100000 * Real.log 39) ≤ (113187484544597 / 125000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_39_sin : (424346589218799 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 39) ∧ Real.sin (16647931 / 100000 * Real.log 39) ≤ (16973868046641 / 40000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_39 : (905499764409449 / 1000000000000000 : ℝ) ≤ cCG cZ 39 ∧ cCG cZ 39 ≤ (113187484544597 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_cos

theorem sCB_39 : (424346589218799 / 1000000000000000 : ℝ) ≤ sCG cZ 39 ∧ sCG cZ 39 ≤ (16973868046641 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_sin

theorem thL_41_r_bounds : (-66083748298361797859 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 ≤ (-66083737101638202141 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_41
  have hl : (12364658305484113 / 20000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 41 ∧ 16647931 / 100000 * Real.log 41 ≤ (618232915385500269 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_41_eq : (16647931 / 100000 * Real.log 41) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 + π) + ((98 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_41_cos_r : (394739228974441 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) ≤ (3947392849653 / 5000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(660837427 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) (-(660837427 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 - (-(660837427 / 1000000000 : ℝ))| ≤ (5598361797859 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 - (-(660837427 / 1000000000 : ℝ)))]

theorem thL_41_sin_r : (-153444563429919 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) ≤ (-613778141751703 / 1000000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (660837427 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3822009603888940969908097636894390661145462650201542315275925877880129841927182785037620758049124853205110825803646574541446467 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(660837427 / 1000000000 : ℝ)) ∧ Real.sin (-(660837427 / 1000000000 : ℝ)) ≤ -((24500061563361263601798839665845845183614377708200294406722522403930281851835334198184692178019360997045877 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394) (-(660837427 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 - (-(660837427 / 1000000000 : ℝ))| ≤ (5598361797859 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 41) 394 - (-(660837427 / 1000000000 : ℝ)))]

theorem thL_41_cos : (-3947392849653 / 5000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 41) ∧ Real.cos (16647931 / 100000 * Real.log 41) ≤ (-394739228974441 / 500000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_41_sin : (613778141751703 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 41) ∧ Real.sin (16647931 / 100000 * Real.log 41) ≤ (153444563429919 / 250000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_41 : (-3947392849653 / 5000000000000 : ℝ) ≤ cCG cZ 41 ∧ cCG cZ 41 ≤ (-394739228974441 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_cos

theorem sCB_41 : (613778141751703 / 1000000000000000 : ℝ) ≤ sCG cZ 41 ∧ sCG cZ 41 ≤ (153444563429919 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_sin

theorem thL_42_r_bounds : (10465681149811939147 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 ≤ (10465686750188060853 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_42
  have hl : (6222446590337753 / 10000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 42 ∧ 16647931 / 100000 * Real.log 42 ≤ (622244659145082191 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_42_eq : (16647931 / 100000 * Real.log 42) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) + ((99 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_42_cos_r : (978173698771949 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) ≤ (978173810779473 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (209313679 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) (209313679 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 - (209313679 / 1000000000 : ℝ)| ≤ (2800188060853 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 - (209313679 / 1000000000 : ℝ))]

theorem thL_42_sin_r : (415577103287 / 2000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) ≤ (207788663651023 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (209313679 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396) (209313679 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 - (209313679 / 1000000000 : ℝ)| ≤ (2800188060853 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 42) 396 - (209313679 / 1000000000 : ℝ))]

theorem thL_42_cos : (978173698771949 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 42) ∧ Real.cos (16647931 / 100000 * Real.log 42) ≤ (978173810779473 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_42_sin : (415577103287 / 2000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 42) ∧ Real.sin (16647931 / 100000 * Real.log 42) ≤ (207788663651023 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_42 : (978173698771949 / 1000000000000000 : ℝ) ≤ cCG cZ 42 ∧ cCG cZ 42 ≤ (978173810779473 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_cos

theorem sCB_42 : (415577103287 / 2000000000000 : ℝ) ≤ sCG cZ 42 ∧ sCG cZ 42 ≤ (207788663651023 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_sin

theorem thL_43_r_bounds : (-58573438473324692723 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 ≤ (-58573427326675307277 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_43
  have hl : (626162000006579719 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 43 ∧ 16647931 / 100000 * Real.log 43 ≤ (313081000058948499 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_43_eq : (16647931 / 100000 * Real.log 43) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 + π + π / 2) + ((99 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_43_cos_r : (833306309381549 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) ≤ (104163302606431 / 125000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(585734329 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) (-(585734329 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 - (-(585734329 / 1000000000 : ℝ))| ≤ (5573324692723 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 - (-(585734329 / 1000000000 : ℝ)))]

theorem thL_43_sin_r : (-276405754043517 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) ≤ (-110562279324077 / 200000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (585734329 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3442368412285236338099533807163379414596459191341493282314495938840750790883364028834819731048962113932247757733201676720464089 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(585734329 / 1000000000 : ℝ)) ∧ Real.sin (-(585734329 / 1000000000 : ℝ)) ≤ -((22066464181309494270535490186051520185987886509499334207171996232262452171454137474008856218754447641206871 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399) (-(585734329 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 - (-(585734329 / 1000000000 : ℝ))| ≤ (5573324692723 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 43) 399 - (-(585734329 / 1000000000 : ℝ)))]

theorem thL_43_cos : (-276405754043517 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 43) ∧ Real.cos (16647931 / 100000 * Real.log 43) ≤ (-110562279324077 / 200000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_43_sin : (-104163302606431 / 125000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 43) ∧ Real.sin (16647931 / 100000 * Real.log 43) ≤ (-833306309381549 / 1000000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_43 : (-276405754043517 / 500000000000000 : ℝ) ≤ cCG cZ 43 ∧ cCG cZ 43 ≤ (-110562279324077 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_cos

theorem sCB_43 : (-104163302606431 / 125000000000000 : ℝ) ≤ sCG cZ 43 ∧ sCG cZ 43 ≤ (-833306309381549 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_sin

theorem thL_44_r_bounds : (19990418621036937353 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 ≤ (19990440978963062647 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_44
  have hl : (629989279137858729 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 44 ∧ 16647931 / 100000 * Real.log 44 ≤ (157497319812296209 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_44_eq : (16647931 / 100000 * Real.log 44) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 + π / 2) + ((100 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_44_cos_r : (995008885372889 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) ≤ (24875224929063 / 25000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (99952149 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) (99952149 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 - (99952149 / 1000000000 : ℝ)| ≤ (11178963062647 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 - (99952149 / 1000000000 : ℝ))]

theorem thL_44_sin_r : (99785748693423 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) ≤ (49892930241527 / 500000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (99952149 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401) (99952149 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 - (99952149 / 1000000000 : ℝ)| ≤ (11178963062647 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 44) 401 - (99952149 / 1000000000 : ℝ))]

theorem thL_44_cos : (-49892930241527 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 44) ∧ Real.cos (16647931 / 100000 * Real.log 44) ≤ (-99785748693423 / 1000000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_44_sin : (995008885372889 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 44) ∧ Real.sin (16647931 / 100000 * Real.log 44) ≤ (24875224929063 / 25000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_44 : (-49892930241527 / 500000000000000 : ℝ) ≤ cCG cZ 44 ∧ cCG cZ 44 ≤ (-99785748693423 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_cos

theorem sCB_44 : (995008885372889 / 1000000000000000 : ℝ) ≤ sCG cZ 44 ∧ sCG cZ 44 ≤ (24875224929063 / 25000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_sin

theorem thL_46_r_bounds : (-35373077979505040941 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 ≤ (-35373066820494959059 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_46
  have hl : (637389577898932977 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 46 ∧ 16647931 / 100000 * Real.log 46 ≤ (127477915602054611 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_46_eq : (16647931 / 100000 * Real.log 46) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 + π) + ((101 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_46_cos_r : (234521716427811 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) ≤ (469043488650677 / 500000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(88432681 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) (-(88432681 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 - (-(88432681 / 250000000 : ℝ))| ≤ (5579505040941 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 - (-(88432681 / 250000000 : ℝ)))]

theorem thL_46_sin_r : (-173200004585477 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) ≤ (-86599974395213 / 250000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (88432681 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4591770927375510364545663280951992189693415353804725745008364579316554845235464035173869279355658120290327541104314863 / 13255691528320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(88432681 / 250000000 : ℝ)) ∧ Real.sin (-(88432681 / 250000000 : ℝ)) ≤ -((3296656050423441263917743159090035772232940262241757854280322588965196744529858101050937136720528519 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406) (-(88432681 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 - (-(88432681 / 250000000 : ℝ))| ≤ (5579505040941 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 46) 406 - (-(88432681 / 250000000 : ℝ)))]

theorem thL_46_cos : (-469043488650677 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 46) ∧ Real.cos (16647931 / 100000 * Real.log 46) ≤ (-234521716427811 / 250000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_46_sin : (86599974395213 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 46) ∧ Real.sin (16647931 / 100000 * Real.log 46) ≤ (173200004585477 / 500000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_46 : (-469043488650677 / 500000000000000 : ℝ) ≤ cCG cZ 46 ∧ cCG cZ 46 ≤ (-234521716427811 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_cos

theorem sCB_46 : (86599974395213 / 250000000000000 : ℝ) ≤ sCG cZ 46 ∧ sCG cZ 46 ≤ (173200004585477 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_sin

theorem thL_47_r_bounds : (1062684651695070573 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 ≤ (1062686048304929427 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_47
  have hl : (320484958052418301 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 47 ∧ 16647931 / 100000 * Real.log 47 ≤ (128193983243236443 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_47_eq : (16647931 / 100000 * Real.log 47) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) + ((102 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_47_cos_r : (996388359665517 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) ≤ (996388471394307 / 1000000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (21253707 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) (21253707 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 - (21253707 / 250000000 : ℝ)| ≤ (698304929427 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 - (21253707 / 250000000 : ℝ))]

theorem thL_47_sin_r : (84912401394781 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) ≤ (84912513123571 / 1000000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (21253707 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408) (21253707 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 - (21253707 / 250000000 : ℝ)| ≤ (698304929427 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 47) 408 - (21253707 / 250000000 : ℝ))]

theorem thL_47_cos : (996388359665517 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 47) ∧ Real.cos (16647931 / 100000 * Real.log 47) ≤ (996388471394307 / 1000000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_47_sin : (84912401394781 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 47) ∧ Real.sin (16647931 / 100000 * Real.log 47) ≤ (84912513123571 / 1000000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_47 : (996388359665517 / 1000000000000000 : ℝ) ≤ cCG cZ 47 ∧ cCG cZ 47 ≤ (996388471394307 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_cos

theorem sCB_47 : (84912401394781 / 1000000000000000 : ℝ) ≤ sCG cZ 47 ∧ sCG cZ 47 ≤ (84912513123571 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_sin

theorem thL_48_r_bounds : (4483791553185298843 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 ≤ (4483792666814701157 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_48
  have hl : (322237436570619351 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 48 ∧ 16647931 / 100000 * Real.log 48 ≤ (161118718313147271 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_48_eq : (16647931 / 100000 * Real.log 48) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 + π) + ((102 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_48_cos_r : (901150850997831 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) ≤ (90115096236091 / 100000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (448379211 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) (448379211 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 - (448379211 / 1000000000 : ℝ)| ≤ (556814701157 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 - (448379211 / 1000000000 : ℝ))]

theorem thL_48_sin_r : (43350547299241 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) ≤ (108376396088839 / 250000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (448379211 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410) (448379211 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 - (448379211 / 1000000000 : ℝ)| ≤ (556814701157 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 48) 410 - (448379211 / 1000000000 : ℝ))]

theorem thL_48_cos : (-90115096236091 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 48) ∧ Real.cos (16647931 / 100000 * Real.log 48) ≤ (-901150850997831 / 1000000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_48_sin : (-108376396088839 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 48) ∧ Real.sin (16647931 / 100000 * Real.log 48) ≤ (-43350547299241 / 100000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_48 : (-90115096236091 / 100000000000000 : ℝ) ≤ cCG cZ 48 ∧ cCG cZ 48 ≤ (-901150850997831 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_cos

theorem sCB_48 : (-108376396088839 / 250000000000000 : ℝ) ≤ sCG cZ 48 ∧ sCG cZ 48 ≤ (-43350547299241 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_sin

theorem thL_49_r_bounds : (36973560397198643759 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 ≤ (36973566002801356241 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_49
  have hl : (32395377892372069 / 50000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 49 ∧ 16647931 / 100000 * Real.log 49 ≤ (323953778979397941 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_49_eq : (16647931 / 100000 * Real.log 49) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) + ((103 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_49_cos_r : (369412459835383 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) ≤ (92353128979829 / 125000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (23108477 / 31250000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) (23108477 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 - (23108477 / 31250000 : ℝ)| ≤ (2802801356241 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 - (23108477 / 31250000 : ℝ))]

theorem thL_49_sin_r : (673897306422721 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) ≤ (673897418537951 / 1000000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (23108477 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412) (23108477 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 - (23108477 / 31250000 : ℝ)| ≤ (2802801356241 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 49) 412 - (23108477 / 31250000 : ℝ))]

theorem thL_49_cos : (369412459835383 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 49) ∧ Real.cos (16647931 / 100000 * Real.log 49) ≤ (92353128979829 / 125000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_49_sin : (673897306422721 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 49) ∧ Real.sin (16647931 / 100000 * Real.log 49) ≤ (673897418537951 / 1000000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_49 : (369412459835383 / 500000000000000 : ℝ) ≤ cCG cZ 49 ∧ cCG cZ 49 ≤ (92353128979829 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_cos

theorem sCB_49 : (673897306422721 / 1000000000000000 : ℝ) ≤ sCG cZ 49 ∧ sCG cZ 49 ≤ (673897418537951 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_sin

theorem thL_51_r_bounds : (-45444992413746978109 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 ≤ (-45444981186253021891 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_51
  have hl : (654567618350248179 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 51 ∧ 16647931 / 100000 * Real.log 51 ≤ (8182095230770117 / 12500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_51_eq : (16647931 / 100000 * Real.log 51) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 + π / 2) + ((104 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_51_cos_r : (449251299191577 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) ≤ (898502710658257 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(113612467 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) (-(113612467 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 - (-(113612467 / 250000000 : ℝ))| ≤ (5613746978109 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 - (-(113612467 / 250000000 : ℝ)))]

theorem thL_51_sin_r : (-438968141331713 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) ≤ (-438968029056767 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (113612467 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40731778696786232031689056874641414932408848097194782749792951848025519919889785761636835753418303277156458331074958787 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(113612467 / 250000000 : ℝ)) ∧ Real.sin (-(113612467 / 250000000 : ℝ)) ≤ -((4177618327875457084497652373986986608317810940270564071166636209602075140441162700416742320150339317 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417) (-(113612467 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 - (-(113612467 / 250000000 : ℝ))| ≤ (5613746978109 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 51) 417 - (-(113612467 / 250000000 : ℝ)))]

theorem thL_51_cos : (438968029056767 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 51) ∧ Real.cos (16647931 / 100000 * Real.log 51) ≤ (438968141331713 / 1000000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_51_sin : (449251299191577 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 51) ∧ Real.sin (16647931 / 100000 * Real.log 51) ≤ (898502710658257 / 1000000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_51 : (438968029056767 / 1000000000000000 : ℝ) ≤ cCG cZ 51 ∧ cCG cZ 51 ≤ (438968141331713 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_cos

theorem sCB_51 : (449251299191577 / 500000000000000 : ℝ) ≤ sCG cZ 51 ∧ sCG cZ 51 ≤ (898502710658257 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_sin

theorem thL_52_r_bounds : (-72666608360572291893 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 ≤ (-72666586039427708107 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_52
  have hl : (328900163942629411 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 52 ∧ 16647931 / 100000 * Real.log 52 ≤ (657800327996622711 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_52_eq : (16647931 / 100000 * Real.log 52) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 + π + π / 2) + ((104 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_52_cos_r : (186943489324553 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) ≤ (1869435116457 / 2000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(181666493 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) (-(181666493 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 - (-(181666493 / 500000000 : ℝ))| ≤ (11160572291893 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 - (-(181666493 / 500000000 : ℝ)))]

theorem thL_52_sin_r : (-71078331528791 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) ≤ (-35539154603823 / 100000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (181666493 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((270145373145727851170738341649105852352511298772180825736973908922442797222052537294154019967974423011940105765550990554093 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(181666493 / 500000000 : ℝ)) ∧ Real.sin (-(181666493 / 500000000 : ℝ)) ≤ -((6926804439634041447139903986857855651175710369223681201807778578570198360114681369799723258999371533243 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419) (-(181666493 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 - (-(181666493 / 500000000 : ℝ))| ≤ (11160572291893 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 52) 419 - (-(181666493 / 500000000 : ℝ)))]

theorem thL_52_cos : (-71078331528791 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 52) ∧ Real.cos (16647931 / 100000 * Real.log 52) ≤ (-35539154603823 / 100000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_52_sin : (-1869435116457 / 2000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 52) ∧ Real.sin (16647931 / 100000 * Real.log 52) ≤ (-186943489324553 / 200000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_52 : (-71078331528791 / 200000000000000 : ℝ) ≤ cCG cZ 52 ∧ cCG cZ 52 ≤ (-35539154603823 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_cos

theorem sCB_52 : (-1869435116457 / 2000000000000 : ℝ) ≤ sCG cZ 52 ∧ sCG cZ 52 ≤ (-186943489324553 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_sin

theorem thL_53_r_bounds : (-66759067985261139587 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 ≤ (-66759045614738860413 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_53
  have hl : (660971458240725171 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 53 ∧ 16647931 / 100000 * Real.log 53 ≤ (330485729176045713 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_53_eq : (16647931 / 100000 * Real.log 53) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 + π / 2) + ((105 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_53_cos_r : (944805641759331 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) ≤ (236201438402987 / 250000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(83448821 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) (-(83448821 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 - (-(83448821 / 250000000 : ℝ))| ≤ (11185261139587 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 - (-(83448821 / 250000000 : ℝ)))]

theorem thL_53_sin_r : (-327631241286839 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) ≤ (-327631129434227 / 1000000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (83448821 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4342977928197162953333757814666732445930112095616203929221301840969585932571334821321202911056925559331776568058727123 / 13255691528320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(83448821 / 250000000 : ℝ)) ∧ Real.sin (-(83448821 / 250000000 : ℝ)) ≤ -((3118035435628731400733937406801947282897391735649326143647822907974715104296224149220684562808560979 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421) (-(83448821 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 - (-(83448821 / 250000000 : ℝ))| ≤ (11185261139587 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 53) 421 - (-(83448821 / 250000000 : ℝ)))]

theorem thL_53_cos : (327631129434227 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 53) ∧ Real.cos (16647931 / 100000 * Real.log 53) ≤ (327631241286839 / 1000000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_53_sin : (944805641759331 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 53) ∧ Real.sin (16647931 / 100000 * Real.log 53) ≤ (236201438402987 / 250000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_53 : (327631129434227 / 1000000000000000 : ℝ) ≤ cCG cZ 53 ∧ cCG cZ 53 ≤ (327631241286839 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_cos

theorem sCB_53 : (944805641759331 / 1000000000000000 : ℝ) ≤ sCG cZ 53 ∧ sCG cZ 53 ≤ (236201438402987 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_sin

theorem thL_54_r_bounds : (-36353458814331206571 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 ≤ (-36353447585668793429 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_54
  have hl : (664083311647016253 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 54 ∧ 16647931 / 100000 * Real.log 54 ≤ (332041655879192291 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_54_eq : (16647931 / 100000 * Real.log 54) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 + π + π / 2) + ((105 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_54_cos_r : (934645799542533 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) ≤ (934645911829169 / 1000000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(90883633 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) (-(90883633 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 - (-(90883633 / 250000000 : ℝ))| ≤ (5614331206571 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 - (-(90883633 / 250000000 : ℝ)))]

theorem thL_54_sin_r : (-35558003933873 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) ≤ (-44447490881513 / 125000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (90883633 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4713458570883772927375728549231426745461922837190206097380016051499562077247452882164554834563797136659869864251068359 / 13255691528320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(90883633 / 250000000 : ℝ)) ∧ Real.sin (-(90883633 / 250000000 : ℝ)) ≤ -((3384021538070398115945322326320600950213232643845711367311969680393395654125978508282887575259372783 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423) (-(90883633 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 - (-(90883633 / 250000000 : ℝ))| ≤ (5614331206571 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 54) 423 - (-(90883633 / 250000000 : ℝ)))]

theorem thL_54_cos : (-35558003933873 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 54) ∧ Real.cos (16647931 / 100000 * Real.log 54) ≤ (-44447490881513 / 125000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_54_sin : (-934645911829169 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 54) ∧ Real.sin (16647931 / 100000 * Real.log 54) ≤ (-934645799542533 / 1000000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_54 : (-35558003933873 / 100000000000000 : ℝ) ≤ cCG cZ 54 ∧ cCG cZ 54 ≤ (-44447490881513 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_cos

theorem sCB_54 : (-934645911829169 / 1000000000000000 : ℝ) ≤ sCG cZ 54 ∧ sCG cZ 54 ≤ (-934645799542533 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_sin

theorem thL_56_r_bounds : (-59225958685942858879 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 ≤ (-59225947514057141121 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_56
  have hl : (670137771954908531 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 56 ∧ 16647931 / 100000 * Real.log 56 ≤ (134027554413256057 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_56_eq : (16647931 / 100000 * Real.log 56) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 + π + π / 2) + ((106 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_56_cos_r : (414840694076669 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) ≤ (165936299975217 / 200000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(592259531 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) (-(592259531 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 - (-(592259531 / 1000000000 : ℝ))| ≤ (5585942858879 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 - (-(592259531 / 1000000000 : ℝ)))]

theorem thL_56_sin_r : (-558237193153653 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) ≤ (-558237081434617 / 1000000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (592259531 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((496593466466226662109298133561323031136516702110650891550454325778658228519433033140785140921144091954888783133965987113468013 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(592259531 / 1000000000 : ℝ)) ∧ Real.sin (-(592259531 / 1000000000 : ℝ)) ≤ -((22283040161938996335896314564919484194981261845981255286343941086194248661773577941412249519240198993890669 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427) (-(592259531 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 - (-(592259531 / 1000000000 : ℝ))| ≤ (5585942858879 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 56) 427 - (-(592259531 / 1000000000 : ℝ)))]

theorem thL_56_cos : (-558237193153653 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 56) ∧ Real.cos (16647931 / 100000 * Real.log 56) ≤ (-558237081434617 / 1000000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_56_sin : (-165936299975217 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 56) ∧ Real.sin (16647931 / 100000 * Real.log 56) ≤ (-414840694076669 / 500000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_56 : (-558237193153653 / 1000000000000000 : ℝ) ≤ cCG cZ 56 ∧ cCG cZ 56 ≤ (-558237081434617 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_cos

theorem sCB_56 : (-165936299975217 / 200000000000000 : ℝ) ≤ sCG cZ 56 ∧ sCG cZ 56 ≤ (-414840694076669 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_sin

theorem thL_57_r_bounds : (19588936728354725761 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 ≤ (19588939521645274239 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_57
  have hl : (134616877067541679 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 57 ∧ 16647931 / 100000 * Real.log 57 ≤ (168271096362270391 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_57_eq : (16647931 / 100000 * Real.log 57) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) + ((107 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_57_cos_r : (354203527273077 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) ≤ (177101791597399 / 250000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (31342301 / 40000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) (31342301 / 40000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 - (31342301 / 40000000 : ℝ)| ≤ (1396645274239 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 - (31342301 / 40000000 : ℝ))]

theorem thL_57_sin_r : (705804000335617 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) ≤ (35290205603699 / 50000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (31342301 / 40000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428) (31342301 / 40000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 - (31342301 / 40000000 : ℝ)| ≤ (1396645274239 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 57) 428 - (31342301 / 40000000 : ℝ))]

theorem thL_57_cos : (354203527273077 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 57) ∧ Real.cos (16647931 / 100000 * Real.log 57) ≤ (177101791597399 / 250000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_57_sin : (705804000335617 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 57) ∧ Real.sin (16647931 / 100000 * Real.log 57) ≤ (35290205603699 / 50000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_57 : (354203527273077 / 500000000000000 : ℝ) ≤ cCG cZ 57 ∧ cCG cZ 57 ≤ (177101791597399 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_cos

theorem sCB_57 : (705804000335617 / 1000000000000000 : ℝ) ≤ sCG cZ 57 ∧ sCG cZ 57 ≤ (35290205603699 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_sin

theorem thL_58_r_bounds : (10746602779227894579 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 ≤ (10746605340772105421 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_58
  have hl : (675979750660766941 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 58 ∧ 16647931 / 100000 * Real.log 58 ≤ (675979750788695291 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_58_eq : (16647931 / 100000 * Real.log 58) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 + π) + ((107 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_58_cos_r : (429539098814221 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) ≤ (859078325706863 / 1000000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (537330203 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) (537330203 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 - (537330203 / 1000000000 : ℝ)| ≤ (1280772105421 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 - (537330203 / 1000000000 : ℝ))]

theorem thL_58_sin_r : (511844189938127 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) ≤ (511844318015389 / 1000000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (537330203 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430) (537330203 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 - (537330203 / 1000000000 : ℝ)| ≤ (1280772105421 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 58) 430 - (537330203 / 1000000000 : ℝ))]

theorem thL_58_cos : (-859078325706863 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 58) ∧ Real.cos (16647931 / 100000 * Real.log 58) ≤ (-429539098814221 / 500000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_58_sin : (-511844318015389 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 58) ∧ Real.sin (16647931 / 100000 * Real.log 58) ≤ (-511844189938127 / 1000000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_58 : (-859078325706863 / 1000000000000000 : ℝ) ≤ cCG cZ 58 ∧ cCG cZ 58 ≤ (-429539098814221 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_cos

theorem sCB_58 : (-511844318015389 / 1000000000000000 : ℝ) ≤ sCG cZ 58 ∧ sCG cZ 58 ≤ (-511844189938127 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_sin

theorem thL_59_r_bounds : (1510043450328384421 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 ≤ (1510044349671615579 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_59
  have hl : (27153024805129069 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 59 ∧ 16647931 / 100000 * Real.log 59 ≤ (339412810135671399 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_59_eq : (16647931 / 100000 * Real.log 59) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) + ((108 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_59_cos_r : (970954654990873 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) ≤ (970954798885791 / 1000000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (15100439 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) (15100439 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 - (15100439 / 62500000 : ℝ)| ≤ (449671615579 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 - (15100439 / 62500000 : ℝ))]

theorem thL_59_sin_r : (119631605154473 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) ≤ (29907919275483 / 125000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (15100439 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432) (15100439 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 - (15100439 / 62500000 : ℝ)| ≤ (449671615579 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 59) 432 - (15100439 / 62500000 : ℝ))]

theorem thL_59_cos : (970954654990873 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 59) ∧ Real.cos (16647931 / 100000 * Real.log 59) ≤ (970954798885791 / 1000000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_59_sin : (119631605154473 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 59) ∧ Real.sin (16647931 / 100000 * Real.log 59) ≤ (29907919275483 / 125000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_59 : (970954654990873 / 1000000000000000 : ℝ) ≤ cCG cZ 59 ∧ cCG cZ 59 ≤ (970954798885791 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_cos

theorem sCB_59 : (119631605154473 / 500000000000000 : ℝ) ≤ sCG cZ 59 ∧ sCG cZ 59 ≤ (29907919275483 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_sin

theorem thL_61_r_bounds : (-12293852905496275393 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 ≤ (-12293848644503724607 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_61
  have hl : (171093861091721809 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 61 ∧ 16647931 / 100000 * Real.log 61 ≤ (684375444536794777 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_61_eq : (16647931 / 100000 * Real.log 61) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) + ((109 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_61_cos_r : (22037648102817 / 25000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) ≤ (1101882618191 / 1250000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(491754031 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) (-(491754031 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 - (-(491754031 / 1000000000 : ℝ))| ≤ (2130496275393 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 - (-(491754031 / 1000000000 : ℝ)))]

theorem thL_61_sin_r : (-14755402744197 / 31250000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) ≤ (-236086358687293 / 500000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (491754031 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2940229862949951964823906833010000812584277918290318582375552108122935089707412333121559553194046774678634193459260656753364591 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(491754031 / 1000000000 : ℝ)) ∧ Real.sin (-(491754031 / 1000000000 : ℝ)) ≤ -((18847627326601625810505600894660627774232798082564560580002051879421073999383247672571745435771815159101169 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436) (-(491754031 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 - (-(491754031 / 1000000000 : ℝ))| ≤ (2130496275393 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 61) 436 - (-(491754031 / 1000000000 : ℝ)))]

theorem thL_61_cos : (22037648102817 / 25000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 61) ∧ Real.cos (16647931 / 100000 * Real.log 61) ≤ (1101882618191 / 1250000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_61_sin : (-14755402744197 / 31250000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 61) ∧ Real.sin (16647931 / 100000 * Real.log 61) ≤ (-236086358687293 / 500000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_61 : (22037648102817 / 25000000000000 : ℝ) ≤ cCG cZ 61 ∧ cCG cZ 61 ≤ (1101882618191 / 1250000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_cos

theorem sCB_61 : (-14755402744197 / 31250000000000 : ℝ) ≤ sCG cZ 61 ∧ sCG cZ 61 ≤ (-236086358687293 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_sin

theorem thL_62_r_bounds : (128897970025307878861 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 ≤ (128898006374692121139 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_62
  have hl : (343541242329748181 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 62 ∧ 16647931 / 100000 * Real.log 62 ≤ (137416496968246283 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_62_eq : (16647931 / 100000 * Real.log 62) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 + π / 2) + ((109 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_62_cos_r : (399703109386439 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) ≤ (399703200265261 / 500000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (644489941 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) (644489941 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 - (644489941 / 1000000000 : ℝ)| ≤ (18174692121139 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 - (644489941 / 1000000000 : ℝ))]

theorem thL_62_sin_r : (600790681425749 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) ≤ (600790863173203 / 1000000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (644489941 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437) (644489941 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 - (644489941 / 1000000000 : ℝ)| ≤ (18174692121139 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 62) 437 - (644489941 / 1000000000 : ℝ))]

theorem thL_62_cos : (-600790863173203 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 62) ∧ Real.cos (16647931 / 100000 * Real.log 62) ≤ (-600790681425749 / 1000000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_62_sin : (399703109386439 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 62) ∧ Real.sin (16647931 / 100000 * Real.log 62) ≤ (399703200265261 / 500000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_62 : (-600790863173203 / 1000000000000000 : ℝ) ≤ cCG cZ 62 ∧ cCG cZ 62 ≤ (-600790681425749 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_cos

theorem sCB_62 : (399703109386439 / 500000000000000 : ℝ) ≤ sCG cZ 62 ∧ sCG cZ 62 ≤ (399703200265261 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_sin

theorem thL_63_r_bounds : (33324596294911831167 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 ≤ (33324634905088168833 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_63
  have hl : (27589848417777367 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 63 ∧ 16647931 / 100000 * Real.log 63 ≤ (137949242127416063 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_63_eq : (16647931 / 100000 * Real.log 63) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 + π + π / 2) + ((109 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_63_cos_r : (61634397830743 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) ≤ (986150558342771 / 1000000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (83311539 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) (83311539 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 - (83311539 / 500000000 : ℝ)| ≤ (19305088168833 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 - (83311539 / 500000000 : ℝ))]

theorem thL_63_sin_r : (82926525670891 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) ≤ (33170648878533 / 200000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (83311539 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439) (83311539 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 - (83311539 / 500000000 : ℝ)| ≤ (19305088168833 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 63) 439 - (83311539 / 500000000 : ℝ))]

theorem thL_63_cos : (82926525670891 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 63) ∧ Real.cos (16647931 / 100000 * Real.log 63) ≤ (33170648878533 / 200000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_63_sin : (-986150558342771 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 63) ∧ Real.sin (16647931 / 100000 * Real.log 63) ≤ (-61634397830743 / 62500000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_63 : (82926525670891 / 500000000000000 : ℝ) ≤ cCG cZ 63 ∧ cCG cZ 63 ≤ (33170648878533 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_cos

theorem sCB_63 : (-986150558342771 / 1000000000000000 : ℝ) ≤ sCG cZ 63 ∧ sCG cZ 63 ≤ (-61634397830743 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_sin

theorem thL_64_r_bounds : (-70638814488282016527 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 ≤ (-70638773911717983473 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_64
  have hl : (692367986044107999 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 64 ∧ 16647931 / 100000 * Real.log 64 ≤ (692367986246832701 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_64_eq : (16647931 / 100000 * Real.log 64) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 + π / 2) + ((110 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_64_cos_r : (938272616136939 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) ≤ (117284102377471 / 125000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(353193971 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) (-(353193971 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 - (-(353193971 / 1000000000 : ℝ))| ≤ (20288282016527 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 - (-(353193971 / 1000000000 : ℝ)))]

theorem thL_64_sin_r : (-69179296794509 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) ≤ (-345896281089723 / 1000000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (353193971 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((23669274380946480807441935751043781585380631235102188557970658543332653457394115210466724816751499403935750807731166000876921 / 68428800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(353193971 / 1000000000 : ℝ)) ∧ Real.sin (-(353193971 / 1000000000 : ℝ)) ≤ -((13807076722218771939062498789435918528073170455399968539107572438621684347412308939728829738824699273771829 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441) (-(353193971 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 - (-(353193971 / 1000000000 : ℝ))| ≤ (20288282016527 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 64) 441 - (-(353193971 / 1000000000 : ℝ)))]

theorem thL_64_cos : (345896281089723 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 64) ∧ Real.cos (16647931 / 100000 * Real.log 64) ≤ (69179296794509 / 200000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_64_sin : (938272616136939 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 64) ∧ Real.sin (16647931 / 100000 * Real.log 64) ≤ (117284102377471 / 125000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_64 : (345896281089723 / 1000000000000000 : ℝ) ≤ cCG cZ 64 ∧ cCG cZ 64 ≤ (69179296794509 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_cos

theorem sCB_64 : (938272616136939 / 1000000000000000 : ℝ) ≤ sCG cZ 64 ∧ sCG cZ 64 ≤ (117284102377471 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_sin

theorem thL_66_r_bounds : (1431536133575098453 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 ≤ (1431541666424901547 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_66
  have hl : (697490830542914319 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 66 ∧ 16647931 / 100000 * Real.log 66 ≤ (139498166152718219 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_66_eq : (16647931 / 100000 * Real.log 66) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) + ((111 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_66_cos_r : (249590223589611 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) ≤ (998361115672437 / 1000000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (14315389 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) (14315389 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 - (14315389 / 250000000 : ℝ)| ≤ (2766424901547 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 - (14315389 / 250000000 : ℝ))]

theorem thL_66_sin_r : (14307539530593 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) ≤ (11446075887273 / 200000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (14315389 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444) (14315389 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 - (14315389 / 250000000 : ℝ)| ≤ (2766424901547 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 66) 444 - (14315389 / 250000000 : ℝ))]

theorem thL_66_cos : (249590223589611 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 66) ∧ Real.cos (16647931 / 100000 * Real.log 66) ≤ (998361115672437 / 1000000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_66_sin : (14307539530593 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 66) ∧ Real.sin (16647931 / 100000 * Real.log 66) ≤ (11446075887273 / 200000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_66 : (249590223589611 / 250000000000000 : ℝ) ≤ cCG cZ 66 ∧ cCG cZ 66 ≤ (998361115672437 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_cos

theorem sCB_66 : (14307539530593 / 250000000000000 : ℝ) ≤ sCG cZ 66 ∧ sCG cZ 66 ≤ (11446075887273 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_sin

theorem thL_67_r_bounds : (-58083576169646917881 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 ≤ (-58083553230353082119 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_67
  have hl : (699994325988827423 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 67 ∧ 16647931 / 100000 * Real.log 67 ≤ (349997163108752713 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_67_eq : (16647931 / 100000 * Real.log 67) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 + π) + ((111 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_67_cos_r : (836004288656847 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) ≤ (816410662161 / 976562500000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(580835647 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) (-(580835647 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 - (-(580835647 / 1000000000 : ℝ))| ≤ (11469646917881 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 - (-(580835647 / 1000000000 : ℝ)))]

theorem thL_67_sin_r : (-548722847566841 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) ≤ (-137180654543441 / 250000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (580835647 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((488129695859520423257010780978713645696258626331327252409955144810832631266377612590105583405565623399322125494750061721393161 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(580835647 / 1000000000 : ℝ)) ∧ Real.sin (-(580835647 / 1000000000 : ℝ)) ≤ -((3129036511919218435664653677428008890063779942967824149216959062705040429345797546824855162417328999428471 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446) (-(580835647 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 - (-(580835647 / 1000000000 : ℝ))| ≤ (11469646917881 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 67) 446 - (-(580835647 / 1000000000 : ℝ)))]

theorem thL_67_cos : (-816410662161 / 976562500000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 67) ∧ Real.cos (16647931 / 100000 * Real.log 67) ≤ (-836004288656847 / 1000000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_67_sin : (137180654543441 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 67) ∧ Real.sin (16647931 / 100000 * Real.log 67) ≤ (548722847566841 / 1000000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_67 : (-816410662161 / 976562500000 : ℝ) ≤ cCG cZ 67 ∧ cCG cZ 67 ≤ (-836004288656847 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_cos

theorem sCB_67 : (137180654543441 / 250000000000000 : ℝ) ≤ sCG cZ 67 ∧ sCG cZ 67 ≤ (548722847566841 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_sin

theorem thL_68_r_bounds : (31477316877164979581 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 ≤ (31477340522835020419 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_68
  have hl : (702460731246443301 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 68 ∧ 16647931 / 100000 * Real.log 68 ≤ (702460731482547139 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_68_eq : (16647931 / 100000 * Real.log 68) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 + π + π / 2) + ((111 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_68_cos_r : (950866475671851 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) ≤ (190173342425711 / 200000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (314773287 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) (314773287 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 - (314773287 / 1000000000 : ℝ)| ≤ (11822835020419 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 - (314773287 / 1000000000 : ℝ))]

theorem thL_68_sin_r : (309600787139551 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) ≤ (77400255899063 / 250000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (314773287 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447) (314773287 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 - (314773287 / 1000000000 : ℝ)| ≤ (11822835020419 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 68) 447 - (314773287 / 1000000000 : ℝ))]

theorem thL_68_cos : (309600787139551 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 68) ∧ Real.cos (16647931 / 100000 * Real.log 68) ≤ (77400255899063 / 250000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_68_sin : (-190173342425711 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 68) ∧ Real.sin (16647931 / 100000 * Real.log 68) ≤ (-950866475671851 / 1000000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_68 : (309600787139551 / 1000000000000000 : ℝ) ≤ cCG cZ 68 ∧ cCG cZ 68 ≤ (77400255899063 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_cos

theorem sCB_68 : (-190173342425711 / 200000000000000 : ℝ) ≤ sCG cZ 68 ∧ sCG cZ 68 ≤ (-950866475671851 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_sin

theorem thL_69_r_bounds : (-39642143161998596573 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 ≤ (-39642118838001403427 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_69
  have hl : (704891129299525343 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 69 ∧ 16647931 / 100000 * Real.log 69 ≤ (88111391192816071 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_69_eq : (16647931 / 100000 * Real.log 69) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 + π / 2) + ((112 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_69_cos_r : (11530607236471 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) ≤ (230612205539421 / 250000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(39642131 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) (-(39642131 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 - (-(39642131 / 100000000 : ℝ))| ≤ (12161998596573 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 - (-(39642131 / 100000000 : ℝ)))]

theorem thL_69_sin_r : (-193059892776869 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) ≤ (-96529885578441 / 250000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (39642131 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((240437517860448008227206801691320010437948974802441209560783782400493396696030945431471553002723605024100589417891 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(39642131 / 100000000 : ℝ)) ∧ Real.sin (-(39642131 / 100000000 : ℝ)) ≤ -((154126614013107314830570899530423665519229145197606196887784943750432425780552560400124323002069 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449) (-(39642131 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 - (-(39642131 / 100000000 : ℝ))| ≤ (12161998596573 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 69) 449 - (-(39642131 / 100000000 : ℝ)))]

theorem thL_69_cos : (96529885578441 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 69) ∧ Real.cos (16647931 / 100000 * Real.log 69) ≤ (193059892776869 / 500000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_69_sin : (11530607236471 / 12500000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 69) ∧ Real.sin (16647931 / 100000 * Real.log 69) ≤ (230612205539421 / 250000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_69 : (96529885578441 / 250000000000000 : ℝ) ≤ cCG cZ 69 ∧ cCG cZ 69 ≤ (193059892776869 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_cos

theorem sCB_69 : (11530607236471 / 12500000000000 : ℝ) ≤ sCG cZ 69 ∧ sCG cZ 69 ≤ (230612205539421 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_sin

theorem thL_71_r_bounds : (-8798377150205977701 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 ≤ (-8798370749794022299 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_71
  have hl : (709648004625906481 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 71 ∧ 16647931 / 100000 * Real.log 71 ≤ (709648004881301511 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_71_eq : (16647931 / 100000 * Real.log 71) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) + ((113 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_71_cos_r : (938707333862933 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) ≤ (938707589879419 / 1000000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(175967479 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) (-(175967479 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 - (-(175967479 / 500000000 : ℝ))| ≤ (3200205977701 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 - (-(175967479 / 500000000 : ℝ)))]

theorem thL_71_sin_r : (-172357469579981 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) ≤ (-344714683143483 / 1000000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (175967479 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((37432796789722519582893789536105494059266720066299594914535247796589789413894978528211150198037434933485302378271732222577 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(175967479 / 500000000 : ℝ)) ∧ Real.sin (-(175967479 / 500000000 : ℝ)) ≤ -((6718707116104037999406211334225127964459152576810322068561396920959154755073092500807799172060665149721 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452) (-(175967479 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 - (-(175967479 / 500000000 : ℝ))| ≤ (3200205977701 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 71) 452 - (-(175967479 / 500000000 : ℝ)))]

theorem thL_71_cos : (938707333862933 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 71) ∧ Real.cos (16647931 / 100000 * Real.log 71) ≤ (938707589879419 / 1000000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_71_sin : (-172357469579981 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 71) ∧ Real.sin (16647931 / 100000 * Real.log 71) ≤ (-344714683143483 / 1000000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_71 : (938707333862933 / 1000000000000000 : ℝ) ≤ cCG cZ 71 ∧ cCG cZ 71 ≤ (938707589879419 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_cos

theorem sCB_71 : (-172357469579981 / 500000000000000 : ℝ) ≤ sCG cZ 71 ∧ sCG cZ 71 ≤ (-344714683143483 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_sin

theorem thL_72_r_bounds : (81137700030475897309 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 ≤ (81137752369524102691 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_72
  have hl : (177994106134560137 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 72 ∧ 16647931 / 100000 * Real.log 72 ≤ (71197642479920399 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_72_eq : (16647931 / 100000 * Real.log 72) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 + π / 2) + ((113 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_72_cos_r : (918830714881599 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) ≤ (918830976576883 / 1000000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (405688631 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) (405688631 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 - (405688631 / 1000000000 : ℝ)| ≤ (26169524102691 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 - (405688631 / 1000000000 : ℝ))]

theorem thL_72_sin_r : (19732572922583 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) ≤ (394651720146903 / 1000000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (405688631 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453) (405688631 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 - (405688631 / 1000000000 : ℝ)| ≤ (26169524102691 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 72) 453 - (405688631 / 1000000000 : ℝ))]

theorem thL_72_cos : (-394651720146903 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 72) ∧ Real.cos (16647931 / 100000 * Real.log 72) ≤ (-19732572922583 / 50000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_72_sin : (918830714881599 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 72) ∧ Real.sin (16647931 / 100000 * Real.log 72) ≤ (918830976576883 / 1000000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_72 : (-394651720146903 / 1000000000000000 : ℝ) ≤ cCG cZ 72 ∧ cCG cZ 72 ≤ (-19732572922583 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_cos

theorem sCB_72 : (918830714881599 / 1000000000000000 : ℝ) ≤ sCG cZ 72 ∧ sCG cZ 72 ≤ (918830976576883 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_sin

theorem thL_73_r_bounds : (-17584056131094750077 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 ≤ (-17584045468905249923 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_73
  have hl : (714272727288400593 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 73 ∧ 16647931 / 100000 * Real.log 73 ≤ (35713636377727943 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_73_eq : (16647931 / 100000 * Real.log 73) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 + π + π / 2) + ((113 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_73_cos_r : (904921292859643 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) ≤ (90492155941449 / 100000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(43960127 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) (-(43960127 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 - (-(43960127 / 100000000 : ℝ))| ≤ (5331094750077 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 - (-(43960127 / 100000000 : ℝ)))]

theorem thL_73_sin_r : (-425578812863129 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) ≤ (-425578546308387 / 1000000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (43960127 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((37858389854529466134134652255613868855293088675882923296105256800002009415524401692894743367877399216244950979081 / 88957440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(43960127 / 100000000 : ℝ)) ∧ Real.sin (-(43960127 / 100000000 : ℝ)) ≤ -((169877390372887162374510487362733349524075799002218493285167427393054481579530221992658831040577 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455) (-(43960127 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 - (-(43960127 / 100000000 : ℝ))| ≤ (5331094750077 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 73) 455 - (-(43960127 / 100000000 : ℝ)))]

theorem thL_73_cos : (-425578812863129 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 73) ∧ Real.cos (16647931 / 100000 * Real.log 73) ≤ (-425578546308387 / 1000000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_73_sin : (-90492155941449 / 100000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 73) ∧ Real.sin (16647931 / 100000 * Real.log 73) ≤ (-904921292859643 / 1000000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_73 : (-425578812863129 / 1000000000000000 : ℝ) ≤ cCG cZ 73 ∧ cCG cZ 73 ≤ (-425578546308387 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_cos

theorem sCB_73 : (-90492155941449 / 100000000000000 : ℝ) ≤ sCG cZ 73 ∧ sCG cZ 73 ≤ (-904921292859643 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_sin

theorem thL_74_r_bounds : (6366545882591790721 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 ≤ (6366552667408209279 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_74
  have hl : (71653778685377653 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 74 ∧ 16647931 / 100000 * Real.log 74 ≤ (44783611695299107 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_74_eq : (16647931 / 100000 * Real.log 74) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) + ((114 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_74_cos_r : (96774837096951 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) ≤ (120968580295271 / 125000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (254661971 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) (254661971 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 - (254661971 / 1000000000 : ℝ)| ≤ (3392408209279 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 - (254661971 / 1000000000 : ℝ))]

theorem thL_74_sin_r : (50383632055373 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) ≤ (251918431669523 / 1000000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (254661971 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456) (254661971 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 - (254661971 / 1000000000 : ℝ)| ≤ (3392408209279 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 74) 456 - (254661971 / 1000000000 : ℝ))]

theorem thL_74_cos : (96774837096951 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 74) ∧ Real.cos (16647931 / 100000 * Real.log 74) ≤ (120968580295271 / 125000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_74_sin : (50383632055373 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 74) ∧ Real.sin (16647931 / 100000 * Real.log 74) ≤ (251918431669523 / 1000000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_74 : (96774837096951 / 100000000000000 : ℝ) ≤ cCG cZ 74 ∧ cCG cZ 74 ≤ (120968580295271 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_cos

theorem sCB_74 : (50383632055373 / 200000000000000 : ℝ) ≤ sCG cZ 74 ∧ sCG cZ 74 ≤ (251918431669523 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_sin

theorem thL_76_r_bounds : (-1801577409633077343 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 ≤ (-1801549390366922657 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_76
  have hl : (720977498225169179 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 76 ∧ 16647931 / 100000 * Real.log 76 ≤ (720977498504953879 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_76_eq : (16647931 / 100000 * Real.log 76) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 + π + π / 2) + ((114 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_76_cos_r : (499918791379313 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) ≤ (999837862951289 / 1000000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(9007817 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) (-(9007817 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 - (-(9007817 / 500000000 : ℝ))| ≤ (14009633077343 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 - (-(9007817 / 500000000 : ℝ)))]

theorem thL_76_sin_r : (-9007399788619 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) ≤ (-720580775383 / 40000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (9007817 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((150478702476445815667631362780271055008982635698093737980518991031485233325985421500633262431675041322296081319910437707 / 8353125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(9007817 / 500000000 : ℝ)) ∧ Real.sin (-(9007817 / 500000000 : ℝ)) ≤ -((50159567492148605222543787593414268458500017888745962169486352047633190763232006995442555979778966881 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459) (-(9007817 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 - (-(9007817 / 500000000 : ℝ))| ≤ (14009633077343 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 76) 459 - (-(9007817 / 500000000 : ℝ)))]

theorem thL_76_cos : (-9007399788619 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 76) ∧ Real.cos (16647931 / 100000 * Real.log 76) ≤ (-720580775383 / 40000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_76_sin : (-999837862951289 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 76) ∧ Real.sin (16647931 / 100000 * Real.log 76) ≤ (-499918791379313 / 500000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_76 : (-9007399788619 / 500000000000000 : ℝ) ≤ cCG cZ 76 ∧ cCG cZ 76 ≤ (-720580775383 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_cos

theorem sCB_76 : (-999837862951289 / 1000000000000000 : ℝ) ≤ sCG cZ 76 ∧ sCG cZ 76 ≤ (-499918791379313 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_sin

theorem thL_77_r_bounds : (2937095089623844229 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 ≤ (2937096510376155771 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_77
  have hl : (361576864671985751 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 77 ∧ 16647931 / 100000 * Real.log 77 ≤ (180788432406931919 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_77_eq : (16647931 / 100000 * Real.log 77) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) + ((115 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_77_cos_r : (104046705859181 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) ≤ (166474786205487 / 200000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (14685479 / 25000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) (14685479 / 25000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 - (14685479 / 25000000 : ℝ)| ≤ (710376155771 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 - (14685479 / 25000000 : ℝ))]

theorem thL_77_sin_r : (554214505390159 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) ≤ (277107394770391 / 500000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (14685479 / 25000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460) (14685479 / 25000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 - (14685479 / 25000000 : ℝ)| ≤ (710376155771 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 77) 460 - (14685479 / 25000000 : ℝ))]

theorem thL_77_cos : (104046705859181 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 77) ∧ Real.cos (16647931 / 100000 * Real.log 77) ≤ (166474786205487 / 200000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_77_sin : (554214505390159 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 77) ∧ Real.sin (16647931 / 100000 * Real.log 77) ≤ (277107394770391 / 500000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_77 : (104046705859181 / 125000000000000 : ℝ) ≤ cCG cZ 77 ∧ cCG cZ 77 ≤ (166474786205487 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_cos

theorem sCB_77 : (554214505390159 / 1000000000000000 : ℝ) ≤ sCG cZ 77 ∧ sCG cZ 77 ≤ (277107394770391 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_sin

theorem thL_78_r_bounds : (-20301185159773645787 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 ≤ (-20301170740226354213 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_78
  have hl : (145060375855391953 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 78 ∧ 16647931 / 100000 * Real.log 78 ≤ (725301879564437711 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_78_eq : (16647931 / 100000 * Real.log 78) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 + π) + ((115 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_78_cos_r : (918698470132981 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) ≤ (91869875852397 / 100000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(406023559 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) (-(406023559 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 - (-(406023559 / 1000000000 : ℝ))| ≤ (7209773645787 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 - (-(406023559 / 1000000000 : ℝ)))]

theorem thL_78_sin_r : (-98739863382783 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) ≤ (-394959165140183 / 1000000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (406023559 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((351345690626682465408089474307465579656547094142891093657423763868642073533492445171037417834297174602066024882025018837134497 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(406023559 / 1000000000 : ℝ)) ∧ Real.sin (-(406023559 / 1000000000 : ℝ)) ≤ -((15765511758889545562169491289522870625897631991530552560216830384595547641221730648055212600940974767748841 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462) (-(406023559 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 - (-(406023559 / 1000000000 : ℝ))| ≤ (7209773645787 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 78) 462 - (-(406023559 / 1000000000 : ℝ)))]

theorem thL_78_cos : (-91869875852397 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 78) ∧ Real.cos (16647931 / 100000 * Real.log 78) ≤ (-918698470132981 / 1000000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_78_sin : (394959165140183 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 78) ∧ Real.sin (16647931 / 100000 * Real.log 78) ≤ (98739863382783 / 250000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_78 : (-91869875852397 / 100000000000000 : ℝ) ≤ cCG cZ 78 ∧ cCG cZ 78 ≤ (-918698470132981 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_cos

theorem sCB_78 : (394959165140183 / 1000000000000000 : ℝ) ≤ sCG cZ 78 ∧ sCG cZ 78 ≤ (98739863382783 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_sin

theorem thL_79_r_bounds : (14396419130815470349 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 ≤ (14396448269184529651 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_79
  have hl : (727422663497760357 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 79 ∧ 16647931 / 100000 * Real.log 79 ≤ (36371133189436449 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_79_eq : (16647931 / 100000 * Real.log 79) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 + π + π / 2) + ((115 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_79_cos_r : (989654874946123 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) ≤ (494827583164907 / 500000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (143964337 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) (143964337 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 - (143964337 / 1000000000 : ℝ)| ≤ (14569184529651 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 - (143964337 / 1000000000 : ℝ))]

theorem thL_79_sin_r : (71733706027879 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) ≤ (2869354068789 / 20000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (143964337 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463) (143964337 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 - (143964337 / 1000000000 : ℝ)| ≤ (14569184529651 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 79) 463 - (143964337 / 1000000000 : ℝ))]

theorem thL_79_cos : (71733706027879 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 79) ∧ Real.cos (16647931 / 100000 * Real.log 79) ≤ (2869354068789 / 20000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_79_sin : (-494827583164907 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 79) ∧ Real.sin (16647931 / 100000 * Real.log 79) ≤ (-989654874946123 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_79 : (71733706027879 / 500000000000000 : ℝ) ≤ cCG cZ 79 ∧ cCG cZ 79 ≤ (2869354068789 / 20000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_cos

theorem sCB_79 : (-494827583164907 / 500000000000000 : ℝ) ≤ sCG cZ 79 ∧ sCG cZ 79 ≤ (-989654874946123 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_sin

theorem thL_81_r_bounds : (-40622524967303856351 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 ≤ (-40622495232696143649 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_81
  have hl : (365792431518374393 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 81 ∧ 16647931 / 100000 * Real.log 81 ≤ (731584863334072061 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_81_eq : (16647931 / 100000 * Real.log 81) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 + π) + ((116 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_81_cos_r : (918618846108441 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) ≤ (918619143454561 / 1000000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(406225101 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) (-(406225101 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 - (-(406225101 / 1000000000 : ℝ))| ≤ (14867303856351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 - (-(406225101 / 1000000000 : ℝ)))]

theorem thL_81_sin_r : (-12348268948191 / 31250000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) ≤ (-6174129828063 / 15625000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (406225101 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((10125813814444583082553686727630474741877602960268019663019886809166633707177531481690383007756069488589792883156724767192207 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(406225101 / 1000000000 : ℝ)) ∧ Real.sin (-(406225101 / 1000000000 : ℝ)) ≤ -((194727188739318256264082865517813409624475997572901093123190600351727494429915187734614393824823620567579 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466) (-(406225101 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 - (-(406225101 / 1000000000 : ℝ))| ≤ (14867303856351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 81) 466 - (-(406225101 / 1000000000 : ℝ)))]

theorem thL_81_cos : (-918619143454561 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 81) ∧ Real.cos (16647931 / 100000 * Real.log 81) ≤ (-918618846108441 / 1000000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_81_sin : (6174129828063 / 15625000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 81) ∧ Real.sin (16647931 / 100000 * Real.log 81) ≤ (12348268948191 / 31250000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_81 : (-918619143454561 / 1000000000000000 : ℝ) ≤ cCG cZ 81 ∧ cCG cZ 81 ≤ (-918618846108441 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_cos

theorem sCB_81 : (6174129828063 / 15625000000000 : ℝ) ≤ sCG cZ 81 ∧ sCG cZ 81 ≤ (12348268948191 / 31250000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_sin

theorem thL_82_r_bounds : (6569497050824918041 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 ≤ (6569527149175081959 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_82
  have hl : (733627579584491397 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 82 ∧ 16647931 / 100000 * Real.log 82 ≤ (91703447485588559 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_82_eq : (16647931 / 100000 * Real.log 82) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 + π + π / 2) + ((116 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_82_cos_r : (997842701041333 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) ≤ (249460750506209 / 250000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (65695121 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) (65695121 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 - (65695121 / 1000000000 : ℝ)| ≤ (15049175081959 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 - (65695121 / 1000000000 : ℝ))]

theorem thL_82_sin_r : (16411931417069 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) ≤ (65648026651779 / 1000000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (65695121 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467) (65695121 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 - (65695121 / 1000000000 : ℝ)| ≤ (15049175081959 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 82) 467 - (65695121 / 1000000000 : ℝ))]

theorem thL_82_cos : (16411931417069 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 82) ∧ Real.cos (16647931 / 100000 * Real.log 82) ≤ (65648026651779 / 1000000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_82_sin : (-249460750506209 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 82) ∧ Real.sin (16647931 / 100000 * Real.log 82) ≤ (-997842701041333 / 1000000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_82 : (16411931417069 / 250000000000000 : ℝ) ≤ cCG cZ 82 ∧ cCG cZ 82 ≤ (65648026651779 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_cos

theorem sCB_82 : (-249460750506209 / 250000000000000 : ℝ) ≤ sCG cZ 82 ∧ sCG cZ 82 ≤ (-997842701041333 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_sin

theorem thL_83_r_bounds : (12821359535976244991 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 ≤ (12821367114023755009 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_83
  have hl : (183911383830408219 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 83 ∧ 16647931 / 100000 * Real.log 83 ≤ (91955691953071571 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_83_eq : (16647931 / 100000 * Real.log 83) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) + ((117 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_83_cos_r : (8713472842003 / 10000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) ≤ (871347587322893 / 1000000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (512854533 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) (512854533 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 - (512854533 / 1000000000 : ℝ)| ≤ (3789023755009 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 - (512854533 / 1000000000 : ℝ))]

theorem thL_83_sin_r : (19626655240639 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) ≤ (30666667758619 / 62500000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (512854533 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468) (512854533 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 - (512854533 / 1000000000 : ℝ)| ≤ (3789023755009 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 83) 468 - (512854533 / 1000000000 : ℝ))]

theorem thL_83_cos : (8713472842003 / 10000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 83) ∧ Real.cos (16647931 / 100000 * Real.log 83) ≤ (871347587322893 / 1000000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_83_sin : (19626655240639 / 40000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 83) ∧ Real.sin (16647931 / 100000 * Real.log 83) ≤ (30666667758619 / 62500000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_83 : (8713472842003 / 10000000000000 : ℝ) ≤ cCG cZ 83 ∧ cCG cZ 83 ≤ (871347587322893 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_cos

theorem sCB_83 : (19626655240639 / 40000000000000 : ℝ) ≤ sCG cZ 83 ∧ sCG cZ 83 ≤ (30666667758619 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_sin

theorem thL_84_r_bounds : (-6349502509073219619 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 ≤ (-6349499450926780381 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_84
  have hl : (737639323343005599 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 84 ∧ 16647931 / 100000 * Real.log 84 ≤ (737639323648508733 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_84_eq : (16647931 / 100000 * Real.log 84) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 + π) + ((117 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_84_cos_r : (402550571649553 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) ≤ (201275362280679 / 250000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(317475049 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) (-(317475049 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 - (-(317475049 / 500000000 : ℝ))| ≤ (1529073219619 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 - (-(317475049 / 500000000 : ℝ)))]

theorem thL_84_sin_r : (-593137491836787 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) ≤ (-118627437204341 / 200000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (317475049 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((450864080416311921473065669695204649762216118728464964987459140720074046519132417259945611252256080072012409290891951480649 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(317475049 / 500000000 : ℝ)) ∧ Real.sin (-(317475049 / 500000000 : ℝ)) ≤ -((11560617446563566402425252752661629434389279708985347799115375649373048816335475949015417284196849786951 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470) (-(317475049 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 - (-(317475049 / 500000000 : ℝ))| ≤ (1529073219619 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 84) 470 - (-(317475049 / 500000000 : ℝ)))]

theorem thL_84_cos : (-201275362280679 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 84) ∧ Real.cos (16647931 / 100000 * Real.log 84) ≤ (-402550571649553 / 500000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_84_sin : (118627437204341 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 84) ∧ Real.sin (16647931 / 100000 * Real.log 84) ≤ (593137491836787 / 1000000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_84 : (-201275362280679 / 250000000000000 : ℝ) ≤ cCG cZ 84 ∧ cCG cZ 84 ≤ (-402550571649553 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_cos

theorem sCB_84 : (118627437204341 / 200000000000000 : ℝ) ≤ sCG cZ 84 ∧ sCG cZ 84 ≤ (593137491836787 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_sin

theorem thL_86_r_bounds : (3519951692044543027 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 ≤ (3519959457955456973 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_86
  have hl : (370778332157436493 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 86 ∧ 16647931 / 100000 * Real.log 86 ≤ (185389166156267187 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_86_eq : (16647931 / 100000 * Real.log 86) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) + ((118 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_86_cos_r : (123763017364959 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) ≤ (990104449556109 / 1000000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (140798223 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) (140798223 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 - (140798223 / 1000000000 : ℝ)| ≤ (3882955456973 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 - (140798223 / 1000000000 : ℝ))]

theorem thL_86_sin_r : (70166663984793 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) ≤ (140333638606023 / 1000000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (140798223 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472) (140798223 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 - (140798223 / 1000000000 : ℝ)| ≤ (3882955456973 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 86) 472 - (140798223 / 1000000000 : ℝ))]

theorem thL_86_cos : (123763017364959 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 86) ∧ Real.cos (16647931 / 100000 * Real.log 86) ≤ (990104449556109 / 1000000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_86_sin : (70166663984793 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 86) ∧ Real.sin (16647931 / 100000 * Real.log 86) ≤ (140333638606023 / 1000000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_86 : (123763017364959 / 125000000000000 : ℝ) ≤ cCG cZ 86 ∧ cCG cZ 86 ≤ (990104449556109 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_cos

theorem sCB_86 : (70166663984793 / 500000000000000 : ℝ) ≤ sCG cZ 86 ∧ sCG cZ 86 ≤ (140333638606023 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_sin

theorem thL_87_r_bounds : (98927895364164820369 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 ≤ (98927957835835179631 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_87
  have hl : (29739252082032277 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 87 ∧ 16647931 / 100000 * Real.log 87 ≤ (743481302363151379 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_87_eq : (16647931 / 100000 * Real.log 87) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 + π / 2) + ((118 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_87_cos_r : (110017460280707 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) ≤ (880139994604457 / 1000000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (494639633 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) (494639633 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 - (494639633 / 1000000000 : ℝ)| ≤ (31235835179631 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 - (494639633 / 1000000000 : ℝ))]

theorem thL_87_sin_r : (11867858814243 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) ≤ (474714664928089 / 1000000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (494639633 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473) (494639633 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 - (494639633 / 1000000000 : ℝ)| ≤ (31235835179631 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 87) 473 - (494639633 / 1000000000 : ℝ))]

theorem thL_87_cos : (-474714664928089 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 87) ∧ Real.cos (16647931 / 100000 * Real.log 87) ≤ (-11867858814243 / 25000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_87_sin : (110017460280707 / 125000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 87) ∧ Real.sin (16647931 / 100000 * Real.log 87) ≤ (880139994604457 / 1000000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_87 : (-474714664928089 / 1000000000000000 : ℝ) ≤ cCG cZ 87 ∧ cCG cZ 87 ≤ (-11867858814243 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_cos

theorem sCB_87 : (110017460280707 / 125000000000000 : ℝ) ≤ sCG cZ 87 ∧ sCG cZ 87 ≤ (880139994604457 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_sin

theorem thL_88_r_bounds : (-5954494258064833093 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 ≤ (-5954491741935166907 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_88
  have hl : (74538394344531779 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 88 ∧ 16647931 / 100000 * Real.log 88 ≤ (745383943759690927 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_88_eq : (16647931 / 100000 * Real.log 88) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 + π + π / 2) + ((118 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_88_cos_r : (735554269706807 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) ≤ (183888646070843 / 250000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(5954493 / 8000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) (-(5954493 / 8000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 - (-(5954493 / 8000000 : ℝ))| ≤ (1258064833093 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 - (-(5954493 / 8000000 : ℝ)))]

theorem thL_88_sin_r : (-42341611936693 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) ≤ (-677465476467423 / 1000000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (5954493 / 8000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((9544015654980575246792611625600147344032778567301474588644162225440902317055272649343056828769951 / 14087822584368332800000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(5954493 / 8000000 : ℝ)) ∧ Real.sin (-(5954493 / 8000000 : ℝ)) ≤ -((2867793165544438821516540953595228659037709645528215416735432450027328254325021003 / 4233119766937600000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475) (-(5954493 / 8000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 - (-(5954493 / 8000000 : ℝ))| ≤ (1258064833093 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 88) 475 - (-(5954493 / 8000000 : ℝ)))]

theorem thL_88_cos : (-42341611936693 / 62500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 88) ∧ Real.cos (16647931 / 100000 * Real.log 88) ≤ (-677465476467423 / 1000000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_88_sin : (-183888646070843 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 88) ∧ Real.sin (16647931 / 100000 * Real.log 88) ≤ (-735554269706807 / 1000000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_88 : (-42341611936693 / 62500000000000 : ℝ) ≤ cCG cZ 88 ∧ cCG cZ 88 ≤ (-677465476467423 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_cos

theorem sCB_88 : (-183888646070843 / 250000000000000 : ℝ) ≤ sCG cZ 88 ∧ sCG cZ 88 ≤ (-735554269706807 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_sin

theorem thL_89_r_bounds : (-21698297372731037793 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 ≤ (-21698281527268962207 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_89
  have hl : (74726508560691617 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 89 ∧ 16647931 / 100000 * Real.log 89 ≤ (373632542961602967 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_89_eq : (16647931 / 100000 * Real.log 89) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) + ((119 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_89_cos_r : (907305226048931 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) ≤ (907305542958267 / 1000000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(433965789 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) (-(433965789 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 - (-(433965789 / 1000000000 : ℝ))| ≤ (7922731037793 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 - (-(433965789 / 1000000000 : ℝ)))]

theorem thL_89_sin_r : (-420472439646487 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) ≤ (-210236061368621 / 500000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (433965789 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((10774854488910286386678014996013522573519870043249919767173011396690149225296150895106459870299732649224535374626955543245183 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(433965789 / 1000000000 : ℝ)) ∧ Real.sin (-(433965789 / 1000000000 : ℝ)) ≤ -((207208740171350129095160455303795569977907031348235536988077263164346582672168746216537748171458357540331 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476) (-(433965789 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 - (-(433965789 / 1000000000 : ℝ))| ≤ (7922731037793 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 89) 476 - (-(433965789 / 1000000000 : ℝ)))]

theorem thL_89_cos : (907305226048931 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 89) ∧ Real.cos (16647931 / 100000 * Real.log 89) ≤ (907305542958267 / 1000000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_89_sin : (-420472439646487 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 89) ∧ Real.sin (16647931 / 100000 * Real.log 89) ≤ (-210236061368621 / 500000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_89 : (907305226048931 / 1000000000000000 : ℝ) ≤ cCG cZ 89 ∧ cCG cZ 89 ≤ (907305542958267 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_cos

theorem sCB_89 : (-420472439646487 / 1000000000000000 : ℝ) ≤ sCG cZ 89 ∧ sCG cZ 89 ≤ (-210236061368621 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_sin

theorem thL_91_r_bounds : (6206693798986799597 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 ≤ (6206709801013200403 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_91
  have hl : (150192955616833033 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 91 ∧ 16647931 / 100000 * Real.log 91 ≤ (46935298650248803 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_91_eq : (16647931 / 100000 * Real.log 91) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 + π) + ((119 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_91_cos_r : (992305099005051 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) ≤ (49615270952279 / 50000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (31033509 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) (31033509 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 - (31033509 / 250000000 : ℝ)| ≤ (8001013200403 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 - (31033509 / 250000000 : ℝ))]

theorem thL_91_sin_r : (30953829816313 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) ≤ (123815639305781 / 1000000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (31033509 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478) (31033509 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 - (31033509 / 250000000 : ℝ)| ≤ (8001013200403 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 91) 478 - (31033509 / 250000000 : ℝ))]

theorem thL_91_cos : (-49615270952279 / 50000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 91) ∧ Real.cos (16647931 / 100000 * Real.log 91) ≤ (-992305099005051 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_91_sin : (-123815639305781 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 91) ∧ Real.sin (16647931 / 100000 * Real.log 91) ≤ (-30953829816313 / 250000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_91 : (-49615270952279 / 50000000000000 : ℝ) ≤ cCG cZ 91 ∧ cCG cZ 91 ≤ (-992305099005051 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_cos

theorem sCB_91 : (-123815639305781 / 1000000000000000 : ℝ) ≤ sCG cZ 91 ∧ sCG cZ 91 ≤ (-30953829816313 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_sin

theorem thL_92_r_bounds : (74560334045116877287 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 ≤ (74560398354883122713 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_92
  have hl : (150556848440996213 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 92 ∧ 16647931 / 100000 * Real.log 92 ≤ (752784242526419109 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_92_eq : (16647931 / 100000 * Real.log 92) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 + π + π / 2) + ((119 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_92_cos_r : (931310341327653 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) ≤ (1862621325753 / 2000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (372801831 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) (372801831 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 - (372801831 / 1000000000 : ℝ)| ≤ (32154883122713 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 - (372801831 / 1000000000 : ℝ))]

theorem thL_92_sin_r : (364226072045741 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) ≤ (182113196797287 / 500000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (372801831 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479) (372801831 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 - (372801831 / 1000000000 : ℝ)| ≤ (32154883122713 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 92) 479 - (372801831 / 1000000000 : ℝ))]

theorem thL_92_cos : (364226072045741 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 92) ∧ Real.cos (16647931 / 100000 * Real.log 92) ≤ (182113196797287 / 500000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_92_sin : (-1862621325753 / 2000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 92) ∧ Real.sin (16647931 / 100000 * Real.log 92) ≤ (-931310341327653 / 1000000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_92 : (364226072045741 / 1000000000000000 : ℝ) ≤ cCG cZ 92 ∧ cCG cZ 92 ≤ (182113196797287 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_cos

theorem sCB_92 : (-1862621325753 / 2000000000000 : ℝ) ≤ sCG cZ 92 ∧ sCG cZ 92 ≤ (-931310341327653 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_sin

theorem thL_93_r_bounds : (188062248876351947 / 312500000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 ≤ (188062349873648053 / 312500000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_93
  have hl : (150916807211634293 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 93 ∧ 16647931 / 100000 * Real.log 93 ≤ (754584036381146051 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_93_eq : (16647931 / 100000 * Real.log 93) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) + ((120 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_93_cos_r : (824318123816157 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) ≤ (103039805876527 / 125000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (300899679 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) (300899679 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 - (300899679 / 500000000 : ℝ)| ≤ (50498648053 / 312500000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 - (300899679 / 500000000 : ℝ))]

theorem thL_93_sin_r : (141531617792743 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) ≤ (566126794362539 / 1000000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (300899679 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480) (300899679 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 - (300899679 / 500000000 : ℝ)| ≤ (50498648053 / 312500000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 93) 480 - (300899679 / 500000000 : ℝ))]

theorem thL_93_cos : (824318123816157 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 93) ∧ Real.cos (16647931 / 100000 * Real.log 93) ≤ (103039805876527 / 125000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_93_sin : (141531617792743 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 93) ∧ Real.sin (16647931 / 100000 * Real.log 93) ≤ (566126794362539 / 1000000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_93 : (824318123816157 / 1000000000000000 : ℝ) ≤ cCG cZ 93 ∧ cCG cZ 93 ≤ (103039805876527 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_cos

theorem sCB_93 : (141531617792743 / 250000000000000 : ℝ) ≤ sCG cZ 93 ∧ sCG cZ 93 ≤ (566126794362539 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_sin

theorem thL_94_r_bounds : (-37962455278874076557 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 ≤ (-37962439021125923443 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_94
  have hl : (378182290205143477 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 94 ∧ 16647931 / 100000 * Real.log 94 ≤ (189091145183679413 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_94_eq : (16647931 / 100000 * Real.log 94) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 + π) + ((120 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_94_cos_r : (181338265719269 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) ≤ (90669173513581 / 125000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(759248943 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) (-(759248943 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 - (-(759248943 / 1000000000 : ℝ))| ≤ (8128874076557 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 - (-(759248943 / 1000000000 : ℝ)))]

theorem thL_94_sin_r : (-688377020273833 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) ≤ (-137675339022879 / 200000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (759248943 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((17640070004583605777764208129270813878342224734160379342947542341748777153557392495652676811881015703364916271418634946794901 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(759248943 / 1000000000 : ℝ)) ∧ Real.sin (-(759248943 / 1000000000 : ℝ)) ≤ -((339232115470556769712341732603782240602742003015606665280489320173465213576449218979138707414042075873953 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482) (-(759248943 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 - (-(759248943 / 1000000000 : ℝ))| ≤ (8128874076557 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 94) 482 - (-(759248943 / 1000000000 : ℝ)))]

theorem thL_94_cos : (-90669173513581 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 94) ∧ Real.cos (16647931 / 100000 * Real.log 94) ≤ (-181338265719269 / 250000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_94_sin : (137675339022879 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 94) ∧ Real.sin (16647931 / 100000 * Real.log 94) ≤ (688377020273833 / 1000000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_94 : (-90669173513581 / 125000000000000 : ℝ) ≤ cCG cZ 94 ∧ cCG cZ 94 ≤ (-181338265719269 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_cos

theorem sCB_94 : (137675339022879 / 200000000000000 : ℝ) ≤ sCG cZ 94 ∧ sCG cZ 94 ≤ (688377020273833 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_sin

theorem thL_96_r_bounds : (-19794236128916885487 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 ≤ (-19794219771083114513 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_96
  have hl : (379934768723075813 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 96 ∧ 16647931 / 100000 * Real.log 96 ≤ (11872961527707389 / 15625000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_96_eq : (16647931 / 100000 * Real.log 96) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_96_cos_r : (461327827092813 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) ≤ (461327990671167 / 500000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(395884559 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) (-(395884559 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 - (-(395884559 / 1000000000 : ℝ))| ≤ (8178916885487 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 - (-(395884559 / 1000000000 : ℝ)))]

theorem thL_96_sin_r : (-7712492933051 / 20000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) ≤ (-6025379992123 / 15625000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (395884559 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((343041668156051793854587294666047933818797596996105352348544710488120953548282764192941485561074018096171099990404524028853497 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(395884559 / 1000000000 : ℝ)) ∧ Real.sin (-(395884559 / 1000000000 : ℝ)) ≤ -((2198985052282377921535461801087416617891219964179780626582151095689953229375031606139599809630626724268263 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484) (-(395884559 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 - (-(395884559 / 1000000000 : ℝ))| ≤ (8178916885487 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 96) 484 - (-(395884559 / 1000000000 : ℝ)))]

theorem thL_96_cos : (461327827092813 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 96) ∧ Real.cos (16647931 / 100000 * Real.log 96) ≤ (461327990671167 / 500000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_96_sin : (-7712492933051 / 20000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 96) ∧ Real.sin (16647931 / 100000 * Real.log 96) ≤ (-6025379992123 / 15625000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_96 : (461327827092813 / 500000000000000 : ℝ) ≤ cCG cZ 96 ∧ cCG cZ 96 ≤ (461327990671167 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_cos

theorem sCB_96 : (-7712492933051 / 20000000000000 : ℝ) ≤ sCG cZ 96 ∧ sCG cZ 96 ≤ (-6025379992123 / 15625000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_sin

theorem thL_97_r_bounds : (-9659656570686973159 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 ≤ (-9659643429313026841 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_97
  have hl : (380797363540628843 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 97 ∧ 16647931 / 100000 * Real.log 97 ≤ (761594727409622369 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_97_eq : (16647931 / 100000 * Real.log 97) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 + π / 2) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_97_cos_r : (485491128315591 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) ≤ (242745646291383 / 250000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(193193 / 800000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) (-(193193 / 800000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 - (-(193193 / 800000 : ℝ))| ≤ (6570686973159 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 - (-(193193 / 800000 : ℝ)))]

theorem thL_97_sin_r : (-119575516803889 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) ≤ (-59787676268357 / 250000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (193193 / 800000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((81787707234244838484929519292066387858775954723941633779864465410375417236095868193 / 341992096703447040000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(193193 / 800000 : ℝ)) ∧ Real.sin (-(193193 / 800000 : ℝ)) ≤ -((10649441046125629943123664576227572261018925678083906136086641830916259 / 44530220924928000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485) (-(193193 / 800000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 - (-(193193 / 800000 : ℝ))| ≤ (6570686973159 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 97) 485 - (-(193193 / 800000 : ℝ)))]

theorem thL_97_cos : (59787676268357 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 97) ∧ Real.cos (16647931 / 100000 * Real.log 97) ≤ (119575516803889 / 500000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_97_sin : (485491128315591 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 97) ∧ Real.sin (16647931 / 100000 * Real.log 97) ≤ (242745646291383 / 250000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_97 : (59787676268357 / 250000000000000 : ℝ) ≤ cCG cZ 97 ∧ cCG cZ 97 ≤ (119575516803889 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_cos

theorem sCB_97 : (485491128315591 / 500000000000000 : ℝ) ≤ sCG cZ 97 ∧ sCG cZ 97 ≤ (242745646291383 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_sin

theorem thL_98_r_bounds : (-5239633554794652711 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 ≤ (-5239617045205347289 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_98
  have hl : (30532088886074801 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 98 ∧ 16647931 / 100000 * Real.log 98 ≤ (15266044449628313 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_98_eq : (16647931 / 100000 * Real.log 98) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 + π) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_98_cos_r : (198902824620563 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) ≤ (497257226647301 / 500000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(52396253 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) (-(52396253 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 - (-(52396253 / 500000000 : ℝ))| ≤ (8254794652711 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 - (-(52396253 / 500000000 : ℝ)))]

theorem thL_98_sin_r : (-10460098043027 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) ≤ (-104600650238483 / 1000000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (52396253 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((873743685589967150188128078074617667467062691776334500121487817772090152823683656764315061353328828308598853037619573303 / 8353125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(52396253 / 500000000 : ℝ)) ∧ Real.sin (-(52396253 / 500000000 : ℝ)) ≤ -((291247895196655716729293850904391760324477162114811985561970253588538116336356017274676429699125865229 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486) (-(52396253 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 - (-(52396253 / 500000000 : ℝ))| ≤ (8254794652711 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 98) 486 - (-(52396253 / 500000000 : ℝ)))]

theorem thL_98_cos : (-497257226647301 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 98) ∧ Real.cos (16647931 / 100000 * Real.log 98) ≤ (-198902824620563 / 200000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_98_sin : (104600650238483 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 98) ∧ Real.sin (16647931 / 100000 * Real.log 98) ≤ (10460098043027 / 100000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_98 : (-497257226647301 / 500000000000000 : ℝ) ≤ cCG cZ 98 ∧ cCG cZ 98 ≤ (-198902824620563 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_cos

theorem sCB_98 : (104600650238483 / 1000000000000000 : ℝ) ≤ sCG cZ 98 ∧ sCG cZ 98 ≤ (10460098043027 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_sin

theorem thL_99_r_bounds : (1457079860783356501 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 ≤ (1457112939216643499 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_99
  have hl : (382496190973919497 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 99 ∧ 16647931 / 100000 * Real.log 99 ≤ (38249619113925341 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_99_eq : (16647931 / 100000 * Real.log 99) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 + π + π / 2) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_99_cos_r : (39995747199603 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) ≤ (999894010774409 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (3642741 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) (3642741 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 - (3642741 / 250000000 : ℝ)| ≤ (16539216643499 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 - (3642741 / 250000000 : ℝ))]

theorem thL_99_sin_r : (22766067207 / 1562500000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) ≤ (14570613796813 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (3642741 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487) (3642741 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 - (3642741 / 250000000 : ℝ)| ≤ (16539216643499 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 99) 487 - (3642741 / 250000000 : ℝ))]

theorem thL_99_cos : (22766067207 / 1562500000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 99) ∧ Real.cos (16647931 / 100000 * Real.log 99) ≤ (14570613796813 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_99_sin : (-999894010774409 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 99) ∧ Real.sin (16647931 / 100000 * Real.log 99) ≤ (-39995747199603 / 40000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_99 : (22766067207 / 1562500000000 : ℝ) ≤ cCG cZ 99 ∧ cCG cZ 99 ≤ (14570613796813 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_cos

theorem sCB_99 : (-999894010774409 / 1000000000000000 : ℝ) ≤ sCG cZ 99 ∧ sCG cZ 99 ≤ (-39995747199603 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_sin

theorem thL_101_r_bounds : (40535067516900038817 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 ≤ (40535134083099961183 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_101
  have hl : (768322079140288947 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 101 ∧ 16647931 / 100000 * Real.log 101 ≤ (768322079473038597 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_101_eq : (16647931 / 100000 * Real.log 101) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 + π / 2) + ((122 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_101_cos_r : (979531363656867 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) ≤ (244882924121967 / 250000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (12667219 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) (12667219 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 - (12667219 / 62500000 : ℝ)| ≤ (33283099961183 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 - (12667219 / 62500000 : ℝ))]

theorem thL_101_sin_r : (201290622231389 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) ≤ (201290955062389 / 1000000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (12667219 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489) (12667219 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 - (12667219 / 62500000 : ℝ)| ≤ (33283099961183 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 101) 489 - (12667219 / 62500000 : ℝ))]

theorem thL_101_cos : (-201290955062389 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 101) ∧ Real.cos (16647931 / 100000 * Real.log 101) ≤ (-201290622231389 / 1000000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_101_sin : (979531363656867 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 101) ∧ Real.sin (16647931 / 100000 * Real.log 101) ≤ (244882924121967 / 250000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_101 : (-201290955062389 / 1000000000000000 : ℝ) ≤ cCG cZ 101 ∧ cCG cZ 101 ≤ (-201290622231389 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_cos

theorem sCB_101 : (979531363656867 / 1000000000000000 : ℝ) ≤ sCG cZ 101 ∧ sCG cZ 101 ≤ (244882924121967 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_sin

theorem thL_102_r_bounds : (2720825239400154227 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 ≤ (2720828580599845773 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_102
  have hl : (192490570663460951 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 102 ∧ 16647931 / 100000 * Real.log 102 ≤ (24061321343361229 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_102_eq : (16647931 / 100000 * Real.log 102) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 + π) + ((122 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_102_cos_r : (963213120318467 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) ≤ (963213454438437 / 1000000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (272082691 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) (272082691 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 - (272082691 / 1000000000 : ℝ)| ≤ (1670599845773 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 - (272082691 / 1000000000 : ℝ))]

theorem thL_102_sin_r : (268737926662499 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) ≤ (26873826078247 / 100000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (272082691 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490) (272082691 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 - (272082691 / 1000000000 : ℝ)| ≤ (1670599845773 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 102) 490 - (272082691 / 1000000000 : ℝ))]

theorem thL_102_cos : (-963213454438437 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 102) ∧ Real.cos (16647931 / 100000 * Real.log 102) ≤ (-963213120318467 / 1000000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_102_sin : (-26873826078247 / 100000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 102) ∧ Real.sin (16647931 / 100000 * Real.log 102) ≤ (-268737926662499 / 1000000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_102 : (-963213454438437 / 1000000000000000 : ℝ) ≤ cCG cZ 102 ∧ cCG cZ 102 ≤ (-963213120318467 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_cos

theorem sCB_102 : (-26873826078247 / 100000000000000 : ℝ) ≤ sCG cZ 102 ∧ sCG cZ 102 ≤ (-268737926662499 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_sin

theorem thL_103_r_bounds : (65097494101846591123 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 ≤ (65097561098153408877 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_103
  have hl : (771586483926803473 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 103 ∧ 16647931 / 100000 * Real.log 103 ≤ (154317296852287733 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_103_eq : (16647931 / 100000 * Real.log 103) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 + π + π / 2) + ((122 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_103_cos_r : (947494739161179 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) ≤ (473747537071359 / 500000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (162743819 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) (162743819 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 - (162743819 / 500000000 : ℝ)| ≤ (33498153408877 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 - (162743819 / 500000000 : ℝ))]

theorem thL_103_sin_r : (159885345444249 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) ≤ (159885512935017 / 500000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (162743819 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491) (162743819 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 - (162743819 / 500000000 : ℝ)| ≤ (33498153408877 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 103) 491 - (162743819 / 500000000 : ℝ))]

theorem thL_103_cos : (159885345444249 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 103) ∧ Real.cos (16647931 / 100000 * Real.log 103) ≤ (159885512935017 / 500000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_103_sin : (-473747537071359 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 103) ∧ Real.sin (16647931 / 100000 * Real.log 103) ≤ (-947494739161179 / 1000000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_103 : (159885345444249 / 500000000000000 : ℝ) ≤ cCG cZ 103 ∧ cCG cZ 103 ≤ (159885512935017 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_cos

theorem sCB_103 : (-473747537071359 / 500000000000000 : ℝ) ≤ sCG cZ 103 ∧ sCG cZ 103 ≤ (-947494739161179 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_sin

theorem thL_104_r_bounds : (9079985127054241529 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 ≤ (9079993522945758471 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_104
  have hl : (154638998437699137 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 104 ∧ 16647931 / 100000 * Real.log 104 ≤ (773194992524006967 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_104_eq : (16647931 / 100000 * Real.log 104) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) + ((123 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_104_cos_r : (9347647400489 / 10000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) ≤ (934765075884573 / 1000000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (363199573 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) (363199573 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 - (363199573 / 1000000000 : ℝ)| ≤ (4197945758471 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 - (363199573 / 1000000000 : ℝ))]

theorem thL_104_sin_r : (88816681823667 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) ≤ (35526706313033 / 100000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (363199573 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492) (363199573 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 - (363199573 / 1000000000 : ℝ)| ≤ (4197945758471 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 104) 492 - (363199573 / 1000000000 : ℝ))]

theorem thL_104_cos : (9347647400489 / 10000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 104) ∧ Real.cos (16647931 / 100000 * Real.log 104) ≤ (934765075884573 / 1000000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_104_sin : (88816681823667 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 104) ∧ Real.sin (16647931 / 100000 * Real.log 104) ≤ (35526706313033 / 100000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_104 : (9347647400489 / 10000000000000 : ℝ) ≤ cCG cZ 104 ∧ cCG cZ 104 ≤ (934765075884573 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_cos

theorem sCB_104 : (88816681823667 / 250000000000000 : ℝ) ≤ sCG cZ 104 ∧ sCG cZ 104 ≤ (35526706313033 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_sin

end PsiOmega.Locate.Z3

#print axioms PsiOmega.Locate.Z3.cCB_104
#print axioms PsiOmega.Locate.Z3.sCB_104
