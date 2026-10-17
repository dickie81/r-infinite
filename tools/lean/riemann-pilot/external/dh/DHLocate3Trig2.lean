import DHLocate3Trig

/-! # Generated (`gen_locate_zero.py 3`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 16647931 / 100000`, `n ∈ NS` (part 2 of 2: `106 ≤ n ≤ 209`)

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate.Z3

theorem thL_106_r_bounds : (39273710695722409791 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 ≤ (39273744504277590209 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_106
  have hl : (388183061271818077 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 106 ∧ 16647931 / 100000 * Real.log 106 ≤ (776366122880778539 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_106_eq : (16647931 / 100000 * Real.log 106) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 + π) + ((123 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_106_cos_r : (923864746468297 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) ≤ (461932542276939 / 500000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (98184319 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) (98184319 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 - (98184319 / 250000000 : ℝ)| ≤ (16904277590209 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 - (98184319 / 250000000 : ℝ))]

theorem thL_106_sin_r : (382718549976381 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) ≤ (76543777612387 / 200000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (98184319 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494) (98184319 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 - (98184319 / 250000000 : ℝ)| ≤ (16904277590209 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 106) 494 - (98184319 / 250000000 : ℝ))]

theorem thL_106_cos : (-461932542276939 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 106) ∧ Real.cos (16647931 / 100000 * Real.log 106) ≤ (-923864746468297 / 1000000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_106_sin : (-76543777612387 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 106) ∧ Real.sin (16647931 / 100000 * Real.log 106) ≤ (-382718549976381 / 1000000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_106 : (-461932542276939 / 500000000000000 : ℝ) ≤ cCG cZ 106 ∧ cCG cZ 106 ≤ (-923864746468297 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_cos

theorem sCB_106 : (-76543777612387 / 200000000000000 : ℝ) ≤ sCG cZ 106 ∧ sCG cZ 106 ≤ (-382718549976381 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_sin

theorem thL_107_r_bounds : (7702765471347250377 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 ≤ (7702772248652749623 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_107
  have hl : (48620582502375289 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 107 ∧ 16647931 / 100000 * Real.log 107 ≤ (24310291261747077 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_107_eq : (16647931 / 100000 * Real.log 107) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 + π + π / 2) + ((123 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_107_cos_r : (926746260825397 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) ≤ (115843324961337 / 125000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (385138443 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) (385138443 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 - (385138443 / 1000000000 : ℝ)| ≤ (3388652749623 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 - (385138443 / 1000000000 : ℝ))]

theorem thL_107_sin_r : (375687272470797 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) ≤ (187843805668037 / 500000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (385138443 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495) (385138443 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 - (385138443 / 1000000000 : ℝ)| ≤ (3388652749623 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 107) 495 - (385138443 / 1000000000 : ℝ))]

theorem thL_107_cos : (375687272470797 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 107) ∧ Real.cos (16647931 / 100000 * Real.log 107) ≤ (187843805668037 / 500000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_107_sin : (-115843324961337 / 125000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 107) ∧ Real.sin (16647931 / 100000 * Real.log 107) ≤ (-926746260825397 / 1000000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_107 : (375687272470797 / 1000000000000000 : ℝ) ≤ cCG cZ 107 ∧ cCG cZ 107 ≤ (187843805668037 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_cos

theorem sCB_107 : (-115843324961337 / 125000000000000 : ℝ) ≤ sCG cZ 107 ∧ sCG cZ 107 ≤ (-926746260825397 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_sin

theorem thL_108_r_bounds : (4537473242024535743 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 ≤ (4537477482975464257 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_108
  have hl : (389738987974815343 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 108 ∧ 16647931 / 100000 * Real.log 108 ≤ (194869494072064327 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_108_eq : (16647931 / 100000 * Real.log 108) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_108_cos_r : (93483632125427 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) ≤ (233709165132589 / 250000000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (362998029 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) (362998029 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 - (362998029 / 1000000000 : ℝ)| ≤ (2120475464257 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 - (362998029 / 1000000000 : ℝ))]

theorem thL_108_sin_r : (355078322101657 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) ≤ (355078661377733 / 1000000000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (362998029 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496) (362998029 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 - (362998029 / 1000000000 : ℝ)| ≤ (2120475464257 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 108) 496 - (362998029 / 1000000000 : ℝ))]

theorem thL_108_cos : (93483632125427 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 108) ∧ Real.cos (16647931 / 100000 * Real.log 108) ≤ (233709165132589 / 250000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_108_sin : (355078322101657 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 108) ∧ Real.sin (16647931 / 100000 * Real.log 108) ≤ (355078661377733 / 1000000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_108 : (93483632125427 / 100000000000000 : ℝ) ≤ cCG cZ 108 ∧ cCG cZ 108 ≤ (233709165132589 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_cos

theorem sCB_108 : (355078322101657 / 1000000000000000 : ℝ) ≤ sCG cZ 108 ∧ sCG cZ 108 ≤ (355078661377733 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_sin

theorem thL_109_r_bounds : (32658391387699175731 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 ≤ (32658425412300824269 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_109
  have hl : (156202471666373603 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 109 ∧ 16647931 / 100000 * Real.log 109 ≤ (195253089667796657 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_109_eq : (16647931 / 100000 * Real.log 109) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 + π / 2) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_109_cos_r : (947143555584393 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) ≤ (473571947915207 / 500000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (81646021 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) (81646021 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 - (81646021 / 250000000 : ℝ)| ≤ (17012300824269 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 - (81646021 / 250000000 : ℝ))]

theorem thL_109_sin_r : (5012646450551 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) ≤ (320809713081281 / 1000000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (81646021 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497) (81646021 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 - (81646021 / 250000000 : ℝ)| ≤ (17012300824269 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 109) 497 - (81646021 / 250000000 : ℝ))]

theorem thL_109_cos : (-320809713081281 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 109) ∧ Real.cos (16647931 / 100000 * Real.log 109) ≤ (-5012646450551 / 15625000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_109_sin : (947143555584393 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 109) ∧ Real.sin (16647931 / 100000 * Real.log 109) ≤ (473571947915207 / 500000000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_109 : (-320809713081281 / 1000000000000000 : ℝ) ≤ cCG cZ 109 ∧ cCG cZ 109 ≤ (-5012646450551 / 15625000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_cos

theorem sCB_109 : (947143555584393 / 1000000000000000 : ℝ) ≤ sCG cZ 109 ∧ sCG cZ 109 ≤ (473571947915207 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_sin

theorem thL_111_r_bounds : (21197119526335999577 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 ≤ (21197153673664000423 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_111
  have hl : (784039338266778881 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 111 ∧ 16647931 / 100000 * Real.log 111 ≤ (784039338607390053 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_111_eq : (16647931 / 100000 * Real.log 111) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 + π + π / 2) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_111_cos_r : (12220223663031 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) ≤ (977618234515761 / 1000000000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (105985683 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) (105985683 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 - (105985683 / 500000000 : ℝ)| ≤ (17073664000423 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 - (105985683 / 500000000 : ℝ))]

theorem thL_111_sin_r : (10519368984291 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) ≤ (210387721159101 / 1000000000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (105985683 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499) (105985683 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 - (105985683 / 500000000 : ℝ)| ≤ (17073664000423 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 111) 499 - (105985683 / 500000000 : ℝ))]

theorem thL_111_cos : (10519368984291 / 50000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 111) ∧ Real.cos (16647931 / 100000 * Real.log 111) ≤ (210387721159101 / 1000000000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_111_sin : (-977618234515761 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 111) ∧ Real.sin (16647931 / 100000 * Real.log 111) ≤ (-12220223663031 / 12500000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_111 : (10519368984291 / 50000000000000 : ℝ) ≤ cCG cZ 111 ∧ cCG cZ 111 ≤ (210387721159101 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_cos

theorem sCB_111 : (-977618234515761 / 1000000000000000 : ℝ) ≤ sCG cZ 111 ∧ sCG cZ 111 ≤ (-12220223663031 / 12500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_sin

theorem thL_112_r_bounds : (26854571845514323 / 200000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 ≤ (26854640154485677 / 200000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_112
  have hl : (785532436257005791 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 112 ∧ 16647931 / 100000 * Real.log 112 ≤ (392766218299110369 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_112_eq : (16647931 / 100000 * Real.log 112) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) + ((125 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_112_cos_r : (61937421356467 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) ≤ (99099908324833 / 100000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (13427303 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) (13427303 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 - (13427303 / 100000000 : ℝ)| ≤ (34154485677 / 200000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 - (13427303 / 100000000 : ℝ))]

theorem thL_112_sin_r : (133869749193119 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) ≤ (133870090737977 / 1000000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (13427303 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500) (13427303 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 - (13427303 / 100000000 : ℝ)| ≤ (34154485677 / 200000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 112) 500 - (13427303 / 100000000 : ℝ))]

theorem thL_112_cos : (61937421356467 / 62500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 112) ∧ Real.cos (16647931 / 100000 * Real.log 112) ≤ (99099908324833 / 100000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_112_sin : (133869749193119 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 112) ∧ Real.sin (16647931 / 100000 * Real.log 112) ≤ (133870090737977 / 1000000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_112 : (61937421356467 / 62500000000000 : ℝ) ≤ cCG cZ 112 ∧ cCG cZ 112 ≤ (99099908324833 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_cos

theorem sCB_112 : (133869749193119 / 1000000000000000 : ℝ) ≤ sCG cZ 112 ∧ sCG cZ 112 ≤ (133870090737977 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_sin

theorem thL_113_r_bounds : (4330236491113723423 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 ≤ (4330270708886276577 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_113
  have hl : (78701226208953971 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 113 ∧ 16647931 / 100000 * Real.log 113 ≤ (787012262431332069 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_113_eq : (16647931 / 100000 * Real.log 113) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 + π / 2) + ((125 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_113_cos_r : (999062420591469 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) ≤ (199812552553839 / 200000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (5412817 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) (5412817 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 - (5412817 / 125000000 : ℝ)| ≤ (17108886276577 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 - (5412817 / 125000000 : ℝ))]

theorem thL_113_sin_r : (43288833346191 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) ≤ (21644587761959 / 500000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (5412817 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501) (5412817 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 - (5412817 / 125000000 : ℝ)| ≤ (17108886276577 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 113) 501 - (5412817 / 125000000 : ℝ))]

theorem thL_113_cos : (-21644587761959 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 113) ∧ Real.cos (16647931 / 100000 * Real.log 113) ≤ (-43288833346191 / 1000000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_113_sin : (999062420591469 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 113) ∧ Real.sin (16647931 / 100000 * Real.log 113) ≤ (199812552553839 / 200000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_113 : (-21644587761959 / 500000000000000 : ℝ) ≤ cCG cZ 113 ∧ cCG cZ 113 ≤ (-43288833346191 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_cos

theorem sCB_113 : (999062420591469 / 1000000000000000 : ℝ) ≤ sCG cZ 113 ∧ sCG cZ 113 ≤ (199812552553839 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_sin

theorem thL_114_r_bounds : (-6070641145821085597 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 ≤ (-6070606854178914403 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_114
  have hl : (197119762409894973 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 114 ∧ 16647931 / 100000 * Real.log 114 ≤ (12319985155967573 / 15625000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_114_eq : (16647931 / 100000 * Real.log 114) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 + π) + ((125 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_114_cos_r : (499078885280941 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) ≤ (31192441046197 / 31250000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(189707 / 3125000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) (-(189707 / 3125000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 - (-(189707 / 3125000 : ℝ))| ≤ (17145821085597 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 - (-(189707 / 3125000 : ℝ)))]

theorem thL_114_sin_r : (-12133826414821 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) ≤ (-30334394578841 / 500000000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (189707 / 3125000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((146284769883659792840953148330137389491219737319405775023839673104617468007984273519008179501 / 2411196242668722788948798552155494689941406250000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(189707 / 3125000 : ℝ)) ∧ Real.sin (-(189707 / 3125000 : ℝ)) ≤ -((96022823308248479403292284355430075430626564710129712086220890054472165847851 / 1582733943905623164027929306030273437500000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502) (-(189707 / 3125000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 - (-(189707 / 3125000 : ℝ))| ≤ (17145821085597 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 114) 502 - (-(189707 / 3125000 : ℝ)))]

theorem thL_114_cos : (-31192441046197 / 31250000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 114) ∧ Real.cos (16647931 / 100000 * Real.log 114) ≤ (-499078885280941 / 500000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_114_sin : (30334394578841 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 114) ∧ Real.sin (16647931 / 100000 * Real.log 114) ≤ (12133826414821 / 200000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_114 : (-31192441046197 / 31250000000000 : ℝ) ≤ cCG cZ 114 ∧ cCG cZ 114 ≤ (-499078885280941 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_cos

theorem sCB_114 : (30334394578841 / 500000000000000 : ℝ) ≤ sCG cZ 114 ∧ sCG cZ 114 ≤ (12133826414821 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_sin

theorem thL_116_r_bounds : (-7673343472136952361 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 ≤ (-7673334877863047639 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_116
  have hl : (395687207482871209 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 116 ∧ 16647931 / 100000 * Real.log 116 ≤ (79137441530912213 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_116_eq : (16647931 / 100000 * Real.log 116) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_116_cos_r : (29789511281431 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) ≤ (953264704776751 / 1000000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(306933567 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) (-(306933567 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 - (-(306933567 / 1000000000 : ℝ))| ≤ (4297136952361 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 - (-(306933567 / 1000000000 : ℝ)))]

theorem thL_116_sin_r : (-15106855579299 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) ≤ (-302136767815023 / 1000000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (306933567 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1106062908855594564847257215601681836945910221857291747165353517230777906779739022540456802216429224749168422993867771783187 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(306933567 / 1000000000 : ℝ)) ∧ Real.sin (-(306933567 / 1000000000 : ℝ)) ≤ -((148893083884406943671353297864389417829220240649208163805208984585860091931328246978277969019459604847857 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504) (-(306933567 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 - (-(306933567 / 1000000000 : ℝ))| ≤ (4297136952361 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 116) 504 - (-(306933567 / 1000000000 : ℝ)))]

theorem thL_116_cos : (29789511281431 / 31250000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 116) ∧ Real.cos (16647931 / 100000 * Real.log 116) ≤ (953264704776751 / 1000000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_116_sin : (-15106855579299 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 116) ∧ Real.sin (16647931 / 100000 * Real.log 116) ≤ (-302136767815023 / 1000000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_116 : (29789511281431 / 31250000000000 : ℝ) ≤ cCG cZ 116 ∧ cCG cZ 116 ≤ (953264704776751 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_cos

theorem sCB_116 : (-15106855579299 / 50000000000000 : ℝ) ≤ sCG cZ 116 ∧ sCG cZ 116 ≤ (-302136767815023 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_sin

theorem thL_117_r_bounds : (-8974286780938665777 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 ≤ (-8974279899061334223 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_117
  have hl : (792803430692605151 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 117 ∧ 16647931 / 100000 * Real.log 117 ≤ (396401715518234863 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_117_eq : (16647931 / 100000 * Real.log 117) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 + π / 2) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_117_cos_r : (901005478804671 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) ≤ (450502911449339 / 500000000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(448714167 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) (-(448714167 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 - (-(448714167 / 1000000000 : ℝ))| ≤ (3440938665777 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 - (-(448714167 / 1000000000 : ℝ)))]

theorem thL_117_sin_r : (-433807522299583 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) ≤ (-433807178205711 / 1000000000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (448714167 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1010597603148572183578984672382507310399140625101366021773202251402804670423236772855063538693790100596079924602291376395719 / 2329600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(448714167 / 1000000000 : ℝ)) ∧ Real.sin (-(448714167 / 1000000000 : ℝ)) ≤ -((19434569291318480755665816966471222137867606481707830150784684846198952598986867896621022750813247270587 / 44800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505) (-(448714167 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 - (-(448714167 / 1000000000 : ℝ))| ≤ (3440938665777 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 117) 505 - (-(448714167 / 1000000000 : ℝ)))]

theorem thL_117_cos : (433807178205711 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 117) ∧ Real.cos (16647931 / 100000 * Real.log 117) ≤ (433807522299583 / 1000000000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_117_sin : (901005478804671 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 117) ∧ Real.sin (16647931 / 100000 * Real.log 117) ≤ (450502911449339 / 500000000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_117 : (433807178205711 / 1000000000000000 : ℝ) ≤ cCG cZ 117 ∧ cCG cZ 117 ≤ (433807522299583 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_cos

theorem sCB_117 : (901005478804671 / 1000000000000000 : ℝ) ≤ sCG cZ 117 ∧ sCG cZ 117 ≤ (450502911449339 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_sin

theorem thL_118_r_bounds : (-60265692216789433291 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 ≤ (-60265657783210566709 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_118
  have hl : (158844056887209959 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 118 ∧ 16647931 / 100000 * Real.log 118 ≤ (794220284780378949 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_118_eq : (16647931 / 100000 * Real.log 118) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 + π) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_118_cos_r : (164766483574113 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) ≤ (411916381105573 / 500000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(2410627 / 4000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) (-(2410627 / 4000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 - (-(2410627 / 4000000 : ℝ))| ≤ (17216789433291 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 - (-(2410627 / 4000000 : ℝ)))]

theorem thL_118_sin_r : (-566833360665749 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) ≤ (-566833016329737 / 1000000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (2410627 / 4000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((33838993283708306095104970394131217923685721557143559277024642491151314211668704976197518698581 / 59698327427481600000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(2410627 / 4000000 : ℝ)) ∧ Real.sin (-(2410627 / 4000000 : ℝ)) ≤ -((94901022830875525748085404522470397565787285765147638226188068813159406161171077 / 167423193907200000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506) (-(2410627 / 4000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 - (-(2410627 / 4000000 : ℝ))| ≤ (17216789433291 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 118) 506 - (-(2410627 / 4000000 : ℝ)))]

theorem thL_118_cos : (-411916381105573 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 118) ∧ Real.cos (16647931 / 100000 * Real.log 118) ≤ (-164766483574113 / 200000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_118_sin : (566833016329737 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 118) ∧ Real.sin (16647931 / 100000 * Real.log 118) ≤ (566833360665749 / 1000000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_118 : (-411916381105573 / 500000000000000 : ℝ) ≤ cCG cZ 118 ∧ cCG cZ 118 ≤ (-164766483574113 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_cos

theorem sCB_118 : (566833016329737 / 1000000000000000 : ℝ) ≤ sCG cZ 118 ∧ sCG cZ 118 ≤ (566833360665749 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_sin

theorem thL_119_r_bounds : (-153711243941534790429 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 ≤ (-153711174858465209571 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_119
  have hl : (49726573841581557 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 119 ∧ 16647931 / 100000 * Real.log 119 ≤ (795625181810079369 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_119_eq : (16647931 / 100000 * Real.log 119) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 + π + π / 2) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_119_cos_r : (44932183413123 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) ≤ (359457640056993 / 500000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(768556047 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) (-(768556047 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 - (-(768556047 / 1000000000 : ℝ))| ≤ (34541534790429 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 - (-(768556047 / 1000000000 : ℝ)))]

theorem thL_119_sin_r : (-139019611341841 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) ≤ (-347548855644307 / 500000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (768556047 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2544614333752803123585931535062759389746576762705525578644717907957621668319605957117375601782092052025047148431182708099427 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(768556047 / 1000000000 : ℝ)) ∧ Real.sin (-(768556047 / 1000000000 : ℝ)) ≤ -((48934891033338711550336469719622909588764831943834964615600645799510634112916941048300113457446794046391 / 70400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507) (-(768556047 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 - (-(768556047 / 1000000000 : ℝ))| ≤ (34541534790429 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 119) 507 - (-(768556047 / 1000000000 : ℝ)))]

theorem thL_119_cos : (-139019611341841 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 119) ∧ Real.cos (16647931 / 100000 * Real.log 119) ≤ (-347548855644307 / 500000000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_119_sin : (-359457640056993 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 119) ∧ Real.sin (16647931 / 100000 * Real.log 119) ≤ (-44932183413123 / 62500000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_119 : (-139019611341841 / 200000000000000 : ℝ) ≤ cCG cZ 119 ∧ cCG cZ 119 ≤ (-347548855644307 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_cos

theorem sCB_119 : (-359457640056993 / 500000000000000 : ℝ) ≤ sCG cZ 119 ∧ sCG cZ 119 ≤ (-44932183413123 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_sin

theorem thL_121_r_bounds : (21768342540097621431 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 ≤ (21768359859902378569 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_121
  have hl : (159679980172521887 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 121 ∧ 16647931 / 100000 * Real.log 121 ≤ (798399901208220429 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_121_eq : (16647931 / 100000 * Real.log 121) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_121_cos_r : (56669696268301 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) ≤ (906715486689009 / 1000000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (27210439 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) (27210439 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 - (27210439 / 62500000 : ℝ)| ≤ (8659902378569 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 - (27210439 / 62500000 : ℝ))]

theorem thL_121_sin_r : (84348608569629 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) ≤ (105435847311061 / 250000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (27210439 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508) (27210439 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 - (27210439 / 62500000 : ℝ)| ≤ (8659902378569 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 121) 508 - (27210439 / 62500000 : ℝ))]

theorem thL_121_cos : (56669696268301 / 62500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 121) ∧ Real.cos (16647931 / 100000 * Real.log 121) ≤ (906715486689009 / 1000000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_121_sin : (84348608569629 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 121) ∧ Real.sin (16647931 / 100000 * Real.log 121) ≤ (105435847311061 / 250000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_121 : (56669696268301 / 62500000000000 : ℝ) ≤ cCG cZ 121 ∧ cCG cZ 121 ≤ (906715486689009 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_cos

theorem sCB_121 : (84348608569629 / 200000000000000 : ℝ) ≤ sCG cZ 121 ∧ sCG cZ 121 ≤ (105435847311061 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_sin

theorem thL_122_r_bounds : (23477834117925918807 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 ≤ (23477868682074081193 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_122
  have hl : (799770108679812127 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 122 ∧ 16647931 / 100000 * Real.log 122 ≤ (9997126362817789 / 12500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_122_eq : (16647931 / 100000 * Real.log 122) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 + π / 2) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_122_cos_r : (486282858059557 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) ≤ (972566061760597 / 1000000000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (117389257 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) (117389257 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 - (117389257 / 500000000 : ℝ)| ≤ (17282074081193 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 - (117389257 / 500000000 : ℝ))]

theorem thL_122_sin_r : (116313704335427 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) ≤ (14539234644521 / 62500000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (117389257 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509) (117389257 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 - (117389257 / 500000000 : ℝ)| ≤ (17282074081193 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 122) 509 - (117389257 / 500000000 : ℝ))]

theorem thL_122_cos : (-14539234644521 / 62500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 122) ∧ Real.cos (16647931 / 100000 * Real.log 122) ≤ (-116313704335427 / 500000000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_122_sin : (486282858059557 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 122) ∧ Real.sin (16647931 / 100000 * Real.log 122) ≤ (972566061760597 / 1000000000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_122 : (-14539234644521 / 62500000000000 : ℝ) ≤ cCG cZ 122 ∧ cCG cZ 122 ≤ (-116313704335427 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_cos

theorem sCB_122 : (486282858059557 / 500000000000000 : ℝ) ≤ sCG cZ 122 ∧ sCG cZ 122 ≤ (972566061760597 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_sin

theorem thL_123_r_bounds : (460086738760443803 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 ≤ (460093661239556197 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_123
  have hl : (400564565501167649 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 123 ∧ 16647931 / 100000 * Real.log 123 ≤ (200282282836986573 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_123_eq : (16647931 / 100000 * Real.log 123) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 + π) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_123_cos_r : (249933808716709 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) ≤ (124966947623849 / 125000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (2300451 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) (2300451 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 - (2300451 / 100000000 : ℝ)| ≤ (3461239556197 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 - (2300451 / 100000000 : ℝ))]

theorem thL_123_sin_r : (359411061957 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) ≤ (5750663522301 / 250000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (2300451 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510) (2300451 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 - (2300451 / 100000000 : ℝ)| ≤ (3461239556197 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 123) 510 - (2300451 / 100000000 : ℝ))]

theorem thL_123_cos : (-124966947623849 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 123) ∧ Real.cos (16647931 / 100000 * Real.log 123) ≤ (-249933808716709 / 250000000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_123_sin : (-5750663522301 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 123) ∧ Real.sin (16647931 / 100000 * Real.log 123) ≤ (-359411061957 / 15625000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_123 : (-124966947623849 / 125000000000000 : ℝ) ≤ cCG cZ 123 ∧ cCG cZ 123 ≤ (-249933808716709 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_cos

theorem sCB_123 : (-5750663522301 / 250000000000000 : ℝ) ≤ sCG cZ 123 ∧ sCG cZ 123 ≤ (-359411061957 / 15625000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_sin

theorem thL_124_r_bounds : (-19977401820553157347 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 ≤ (-19977367179446842653 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_124
  have hl : (802477148974786711 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 124 ∧ 16647931 / 100000 * Real.log 124 ≤ (100309643665049713 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_124_eq : (16647931 / 100000 * Real.log 124) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 + π + π / 2) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_124_cos_r : (980111309634549 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) ≤ (980111656045613 / 1000000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(39954769 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) (-(39954769 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 - (-(39954769 / 200000000 : ℝ))| ≤ (17320553157347 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 - (-(39954769 / 200000000 : ℝ)))]

theorem thL_124_sin_r : (-3100747686953 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) ≤ (-24805938194241 / 125000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (39954769 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1012316424885759504086818465734650511430942331190929261704104537463266690397818309297322769930191234742347851100673809 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(39954769 / 200000000 : ℝ)) ∧ Real.sin (-(39954769 / 200000000 : ℝ)) ≤ -((162230196295794792215629523215484279717352145657478456765779005513124290909846784600017582821862031 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511) (-(39954769 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 - (-(39954769 / 200000000 : ℝ))| ≤ (17320553157347 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 124) 511 - (-(39954769 / 200000000 : ℝ)))]

theorem thL_124_cos : (-3100747686953 / 15625000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 124) ∧ Real.cos (16647931 / 100000 * Real.log 124) ≤ (-24805938194241 / 125000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_124_sin : (-980111656045613 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 124) ∧ Real.sin (16647931 / 100000 * Real.log 124) ≤ (-980111309634549 / 1000000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_124 : (-3100747686953 / 15625000000000 : ℝ) ≤ cCG cZ 124 ∧ cCG cZ 124 ≤ (-24805938194241 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_cos

theorem sCB_124 : (-980111656045613 / 1000000000000000 : ℝ) ≤ sCG cZ 124 ∧ sCG cZ 124 ≤ (-980111309634549 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_sin

theorem thL_126_r_bounds : (-135528176775052933511 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 ≤ (-135528107624947066489 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_126
  have hl : (805140874761906701 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 126 ∧ 16647931 / 100000 * Real.log 126 ≤ (161028175021503539 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_126_eq : (16647931 / 100000 * Real.log 126) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 + π / 2) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_126_cos_r : (779053884865761 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) ≤ (97381778829483 / 125000000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(677640711 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) (-(677640711 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 - (-(677640711 / 1000000000 : ℝ))| ≤ (34575052933511 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 - (-(677640711 / 1000000000 : ℝ)))]

theorem thL_126_sin_r : (-39184808114157 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) ≤ (-626956584074961 / 1000000000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (677640711 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1460558460993624699877443335160068439838141012698890533357986846764197451407216320619539628725616309684303346270457595397847 / 2329600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(677640711 / 1000000000 : ℝ)) ∧ Real.sin (-(677640711 / 1000000000 : ℝ)) ≤ -((28087662711370151734917200412907012020233208998291049256942652707208628745184766580347490293609246614379 / 44800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513) (-(677640711 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 - (-(677640711 / 1000000000 : ℝ))| ≤ (34575052933511 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 126) 513 - (-(677640711 / 1000000000 : ℝ)))]

theorem thL_126_cos : (626956584074961 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 126) ∧ Real.cos (16647931 / 100000 * Real.log 126) ≤ (39184808114157 / 62500000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_126_sin : (779053884865761 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 126) ∧ Real.sin (16647931 / 100000 * Real.log 126) ≤ (97381778829483 / 125000000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_126 : (626956584074961 / 1000000000000000 : ℝ) ≤ cCG cZ 126 ∧ cCG cZ 126 ≤ (39184808114157 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_cos

theorem sCB_126 : (779053884865761 / 1000000000000000 : ℝ) ≤ sCG cZ 126 ∧ sCG cZ 126 ≤ (97381778829483 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_sin

theorem thL_127_r_bounds : (127681589179018866489 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 ≤ (127681658420981133511 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_127
  have hl : (40322846179583853 / 50000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 127 ∧ 16647931 / 100000 * Real.log 127 ≤ (806456923937288053 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_127_eq : (16647931 / 100000 * Real.log 127) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 + π / 2) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_127_cos_r : (803045232155473 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) ≤ (401522789187427 / 500000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (638408119 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) (638408119 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 - (638408119 / 1000000000 : ℝ)| ≤ (34620981133511 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 - (638408119 / 1000000000 : ℝ))]

theorem thL_127_sin_r : (2383670684509 / 4000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) ≤ (595918017337533 / 1000000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (638408119 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513) (638408119 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 - (638408119 / 1000000000 : ℝ)| ≤ (34620981133511 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 127) 513 - (638408119 / 1000000000 : ℝ))]

theorem thL_127_cos : (-595918017337533 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 127) ∧ Real.cos (16647931 / 100000 * Real.log 127) ≤ (-2383670684509 / 4000000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_127_sin : (803045232155473 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 127) ∧ Real.sin (16647931 / 100000 * Real.log 127) ≤ (401522789187427 / 500000000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_127 : (-595918017337533 / 1000000000000000 : ℝ) ≤ cCG cZ 127 ∧ cCG cZ 127 ≤ (-2383670684509 / 4000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_cos

theorem sCB_127 : (803045232155473 / 1000000000000000 : ℝ) ≤ sCG cZ 127 ∧ sCG cZ 127 ≤ (401522789187427 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_sin

theorem thL_128_r_bounds : (37333839101933971321 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 ≤ (37333873698066028679 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_128
  have hl : (403881325181798101 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 128 ∧ 16647931 / 100000 * Real.log 128 ≤ (161552530141841439 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_128_eq : (16647931 / 100000 * Real.log 128) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 + π) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_128_cos_r : (186222940549027 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) ≤ (116389381088309 / 125000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (93334641 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) (93334641 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 - (93334641 / 250000000 : ℝ)| ≤ (17298066028679 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 - (93334641 / 250000000 : ℝ))]

theorem thL_128_sin_r : (182362936215827 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) ≤ (364726218392977 / 1000000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (93334641 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514) (93334641 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 - (93334641 / 250000000 : ℝ)| ≤ (17298066028679 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 128) 514 - (93334641 / 250000000 : ℝ))]

theorem thL_128_cos : (-116389381088309 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 128) ∧ Real.cos (16647931 / 100000 * Real.log 128) ≤ (-186222940549027 / 200000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_128_sin : (-364726218392977 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 128) ∧ Real.sin (16647931 / 100000 * Real.log 128) ≤ (-182362936215827 / 500000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_128 : (-116389381088309 / 125000000000000 : ℝ) ≤ cCG cZ 128 ∧ cCG cZ 128 ≤ (-186222940549027 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_cos

theorem sCB_128 : (-364726218392977 / 1000000000000000 : ℝ) ≤ sCG cZ 128 ∧ sCG cZ 128 ≤ (-182362936215827 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_sin

theorem thL_129_r_bounds : (1962148700963218069 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 ≤ (1962155619036781931 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_129
  have hl : (161811643146942521 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 129 ∧ 16647931 / 100000 * Real.log 129 ≤ (404529108040161799 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_129_eq : (16647931 / 100000 * Real.log 129) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 + π + π / 2) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_129_cos_r : (497595567272311 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) ≤ (995191480448301 / 1000000000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (12263451 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) (12263451 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 - (12263451 / 125000000 : ℝ)| ≤ (3459036781931 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 - (12263451 / 125000000 : ℝ))]

theorem thL_129_sin_r : (19590025627491 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) ≤ (48975237020567 / 500000000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (12263451 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515) (12263451 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 - (12263451 / 125000000 : ℝ)| ≤ (3459036781931 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 129) 515 - (12263451 / 125000000 : ℝ))]

theorem thL_129_cos : (19590025627491 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 129) ∧ Real.cos (16647931 / 100000 * Real.log 129) ≤ (48975237020567 / 500000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_129_sin : (-995191480448301 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 129) ∧ Real.sin (16647931 / 100000 * Real.log 129) ≤ (-497595567272311 / 500000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_129 : (19590025627491 / 200000000000000 : ℝ) ≤ cCG cZ 129 ∧ cCG cZ 129 ≤ (48975237020567 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_cos

theorem sCB_129 : (-995191480448301 / 1000000000000000 : ℝ) ≤ sCG cZ 129 ∧ sCG cZ 129 ≤ (-497595567272311 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_sin

theorem thL_131_r_bounds : (-48221454616458185809 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 ≤ (-48221419983541814191 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_131
  have hl : (811619486407515141 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 131 ∧ 16647931 / 100000 * Real.log 131 ≤ (405809743376563067 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_131_eq : (16647931 / 100000 * Real.log 131) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 + π / 2) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_131_cos_r : (885970024446007 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) ≤ (885970370775501 / 1000000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(482214373 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) (-(482214373 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 - (-(482214373 / 1000000000 : ℝ))| ≤ (17316458185809 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 - (-(482214373 / 1000000000 : ℝ)))]

theorem thL_131_sin_r : (-57967794069307 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) ≤ (-463742006225279 / 1000000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (482214373 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((412533170985439334996659735272239054295717368828501837910572490098418633400666939210232007885184763127361963433641389144176419 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(482214373 / 1000000000 : ℝ)) ∧ Real.sin (-(482214373 / 1000000000 : ℝ)) ≤ -((18511103826269225100457105809678443949736933483479101874335350387650713466502047490596921643565380725953923 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517) (-(482214373 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 - (-(482214373 / 1000000000 : ℝ))| ≤ (17316458185809 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 131) 517 - (-(482214373 / 1000000000 : ℝ)))]

theorem thL_131_cos : (463742006225279 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 131) ∧ Real.cos (16647931 / 100000 * Real.log 131) ≤ (57967794069307 / 125000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_131_sin : (885970024446007 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 131) ∧ Real.sin (16647931 / 100000 * Real.log 131) ≤ (885970370775501 / 1000000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_131 : (463742006225279 / 1000000000000000 : ℝ) ≤ cCG cZ 131 ∧ cCG cZ 131 ≤ (57967794069307 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_cos

theorem sCB_131 : (885970024446007 / 1000000000000000 : ℝ) ≤ sCG cZ 131 ∧ sCG cZ 131 ≤ (885970370775501 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_sin

theorem thL_132_r_bounds : (156758782606264771101 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 ≤ (156758851793735228899 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_132
  have hl : (203221373716498219 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 132 ∧ 16647931 / 100000 * Real.log 132 ≤ (812885495211603869 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_132_eq : (16647931 / 100000 * Real.log 132) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 + π / 2) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_132_cos_r : (708239951909479 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) ≤ (44265018622441 / 62500000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (391897043 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) (391897043 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 - (391897043 / 500000000 : ℝ)| ≤ (34593735228899 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 - (391897043 / 500000000 : ℝ))]

theorem thL_132_sin_r : (705971444976847 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) ≤ (705971790920967 / 1000000000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (391897043 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517) (391897043 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 - (391897043 / 500000000 : ℝ)| ≤ (34593735228899 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 132) 517 - (391897043 / 500000000 : ℝ))]

theorem thL_132_cos : (-705971790920967 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 132) ∧ Real.cos (16647931 / 100000 * Real.log 132) ≤ (-705971444976847 / 1000000000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_132_sin : (708239951909479 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 132) ∧ Real.sin (16647931 / 100000 * Real.log 132) ≤ (44265018622441 / 62500000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_132 : (-705971790920967 / 1000000000000000 : ℝ) ≤ cCG cZ 132 ∧ cCG cZ 132 ≤ (-705971444976847 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_cos

theorem sCB_132 : (708239951909479 / 1000000000000000 : ℝ) ≤ sCG cZ 132 ∧ sCG cZ 132 ≤ (44265018622441 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_sin

theorem thL_133_r_bounds : (46945117284308623627 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 ≤ (46945151915691376373 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_133
  have hl : (162828389690519907 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 133 ∧ 16647931 / 100000 * Real.log 133 ≤ (25441935899944079 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_133_eq : (16647931 / 100000 * Real.log 133) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 + π) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_133_cos_r : (55738528669203 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) ≤ (222954201255329 / 250000000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (234725673 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) (234725673 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 - (234725673 / 500000000 : ℝ)| ≤ (17315691376373 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 - (234725673 / 500000000 : ℝ))]

theorem thL_133_sin_r : (113099220393727 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) ≤ (90479445577749 / 200000000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (234725673 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518) (234725673 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 - (234725673 / 500000000 : ℝ)| ≤ (17315691376373 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 133) 518 - (234725673 / 500000000 : ℝ))]

theorem thL_133_cos : (-222954201255329 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 133) ∧ Real.cos (16647931 / 100000 * Real.log 133) ≤ (-55738528669203 / 62500000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_133_sin : (-90479445577749 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 133) ∧ Real.sin (16647931 / 100000 * Real.log 133) ≤ (-113099220393727 / 250000000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_133 : (-222954201255329 / 250000000000000 : ℝ) ≤ cCG cZ 133 ∧ cCG cZ 133 ≤ (-55738528669203 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_cos

theorem sCB_133 : (-90479445577749 / 200000000000000 : ℝ) ≤ sCG cZ 133 ∧ sCG cZ 133 ≤ (-113099220393727 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_sin

theorem thL_134_r_bounds : (29139341390970723407 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 ≤ (29139410609029276593 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_134
  have hl : (815388990313506199 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 134 ∧ 16647931 / 100000 * Real.log 134 ≤ (815388990659117193 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_134_eq : (16647931 / 100000 * Real.log 134) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 + π + π / 2) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_134_cos_r : (989404798678309 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) ≤ (989405144768603 / 1000000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1821211 / 12500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) (1821211 / 12500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 - (1821211 / 12500000 : ℝ)| ≤ (34609029276593 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 - (1821211 / 12500000 : ℝ))]

theorem thL_134_sin_r : (72590894199737 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) ≤ (18147766811221 / 125000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1821211 / 12500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519) (1821211 / 12500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 - (1821211 / 12500000 : ℝ)| ≤ (34609029276593 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 134) 519 - (1821211 / 12500000 : ℝ))]

theorem thL_134_cos : (72590894199737 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 134) ∧ Real.cos (16647931 / 100000 * Real.log 134) ≤ (18147766811221 / 125000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_134_sin : (-989405144768603 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 134) ∧ Real.sin (16647931 / 100000 * Real.log 134) ≤ (-989404798678309 / 1000000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_134 : (72590894199737 / 500000000000000 : ℝ) ≤ cCG cZ 134 ∧ cCG cZ 134 ≤ (18147766811221 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_cos

theorem sCB_134 : (-989405144768603 / 1000000000000000 : ℝ) ≤ sCG cZ 134 ∧ sCG cZ 134 ≤ (-989404798678309 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_sin

theorem thL_136_r_bounds : (-52949068807707638117 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 ≤ (-52949034192292361883 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_136
  have hl : (817855395572607221 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 136 ∧ 16647931 / 100000 * Real.log 136 ≤ (163571079183643643 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_136_eq : (16647931 / 100000 * Real.log 136) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 + π / 2) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_136_cos_r : (431532173549159 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) ≤ (172612938650697 / 200000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(105898103 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) (-(105898103 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 - (-(105898103 / 200000000 : ℝ))| ≤ (17307707638117 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 - (-(105898103 / 200000000 : ℝ)))]

theorem thL_136_sin_r : (-252546930714361 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) ≤ (-505093515274527 / 1000000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (105898103 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2576571517595166273112770946960852103876845662223981628819347453070977425411411864633502666924093977382224409505961623 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(105898103 / 200000000 : ℝ)) ∧ Real.sin (-(105898103 / 200000000 : ℝ)) ≤ -((412912102178678786930317510490810892993754911422096740389767778706891804908846986103136101629196953 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521) (-(105898103 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 - (-(105898103 / 200000000 : ℝ))| ≤ (17307707638117 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 136) 521 - (-(105898103 / 200000000 : ℝ)))]

theorem thL_136_cos : (505093515274527 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 136) ∧ Real.cos (16647931 / 100000 * Real.log 136) ≤ (252546930714361 / 500000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_136_sin : (431532173549159 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 136) ∧ Real.sin (16647931 / 100000 * Real.log 136) ≤ (172612938650697 / 200000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_136 : (505093515274527 / 1000000000000000 : ℝ) ≤ cCG cZ 136 ∧ cCG cZ 136 ≤ (252546930714361 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_cos

theorem sCB_136 : (431532173549159 / 500000000000000 : ℝ) ≤ sCG cZ 136 ∧ sCG cZ 136 ≤ (172612938650697 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_sin

theorem thL_137_r_bounds : (138028682405343275713 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 ≤ (138028751594656724287 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_137
  have hl : (163815005934433571 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 137 ∧ 16647931 / 100000 * Real.log 137 ≤ (819075030017778849 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_137_eq : (16647931 / 100000 * Real.log 137) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 + π / 2) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_137_cos_r : (771154436858261 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) ≤ (192788695707301 / 250000000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (138028717 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) (138028717 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 - (138028717 / 200000000 : ℝ)| ≤ (34594656724287 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 - (138028717 / 200000000 : ℝ))]

theorem thL_137_sin_r : (636647742044443 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) ≤ (127329617598461 / 200000000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (138028717 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521) (138028717 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 - (138028717 / 200000000 : ℝ)| ≤ (34594656724287 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 137) 521 - (138028717 / 200000000 : ℝ))]

theorem thL_137_cos : (-127329617598461 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 137) ∧ Real.cos (16647931 / 100000 * Real.log 137) ≤ (-636647742044443 / 1000000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_137_sin : (771154436858261 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 137) ∧ Real.sin (16647931 / 100000 * Real.log 137) ≤ (192788695707301 / 250000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_137 : (-127329617598461 / 200000000000000 : ℝ) ≤ cCG cZ 137 ∧ cCG cZ 137 ≤ (-636647742044443 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_cos

theorem sCB_137 : (771154436858261 / 1000000000000000 : ℝ) ≤ sCG cZ 137 ∧ sCG cZ 137 ≤ (192788695707301 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_sin

theorem thL_138_r_bounds : (33011104013308375933 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 ≤ (33011138586691624067 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_138
  have hl : (820285793627069119 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 138 ∧ 16647931 / 100000 * Real.log 138 ≤ (820285793972680113 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_138_eq : (16647931 / 100000 * Real.log 138) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 + π) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_138_cos_r : (473003063506871 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) ≤ (946006472747579 / 1000000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (330111213 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) (330111213 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 - (330111213 / 1000000000 : ℝ)| ≤ (17286691624067 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 - (330111213 / 1000000000 : ℝ))]

theorem thL_138_sin_r : (6482961314619 / 20000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) ≤ (324148411464783 / 1000000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (330111213 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522) (330111213 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 - (330111213 / 1000000000 : ℝ)| ≤ (17286691624067 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 138) 522 - (330111213 / 1000000000 : ℝ))]

theorem thL_138_cos : (-946006472747579 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 138) ∧ Real.cos (16647931 / 100000 * Real.log 138) ≤ (-473003063506871 / 500000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_138_sin : (-324148411464783 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 138) ∧ Real.sin (16647931 / 100000 * Real.log 138) ≤ (-6482961314619 / 20000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_138 : (-946006472747579 / 1000000000000000 : ℝ) ≤ cCG cZ 138 ∧ cCG cZ 138 ≤ (-473003063506871 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_cos

theorem sCB_138 : (-324148411464783 / 1000000000000000 : ℝ) ≤ sCG cZ 138 ∧ sCG cZ 138 ≤ (-6482961314619 / 20000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_sin

theorem thL_139_r_bounds : (-7732677201357571981 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 ≤ (-7732607998642428019 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_139
  have hl : (51342988470482759 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 139 ∧ 16647931 / 100000 * Real.log 139 ≤ (410743907936667569 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_139_eq : (16647931 / 100000 * Real.log 139) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 + π + π / 2) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_139_cos_r : (999252498075443 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) ≤ (49962642204451 / 50000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(38663213 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) (-(38663213 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 - (-(38663213 / 1000000000 : ℝ))| ≤ (34601357571981 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 - (-(38663213 / 1000000000 : ℝ)))]

theorem thL_139_sin_r : (-19326877073903 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) ≤ (-38653408134229 / 1000000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (38663213 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((240696653759605660908647700626830760545078131440257470006792372604337784918789204473322563235566446647488395766846195151421853 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(38663213 / 1000000000 : ℝ)) ∧ Real.sin (-(38663213 / 1000000000 : ℝ)) ≤ -((1542927267689779877619536539714343646003765856391887846011324854971733067239770810580441831042271867181163 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523) (-(38663213 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 - (-(38663213 / 1000000000 : ℝ))| ≤ (34601357571981 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 139) 523 - (-(38663213 / 1000000000 : ℝ)))]

theorem thL_139_cos : (-19326877073903 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 139) ∧ Real.cos (16647931 / 100000 * Real.log 139) ≤ (-38653408134229 / 1000000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_139_sin : (-49962642204451 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 139) ∧ Real.sin (16647931 / 100000 * Real.log 139) ≤ (-999252498075443 / 1000000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_139 : (-19326877073903 / 500000000000000 : ℝ) ≤ cCG cZ 139 ∧ cCG cZ 139 ≤ (-38653408134229 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_cos

theorem sCB_139 : (-49962642204451 / 50000000000000 : ℝ) ≤ sCG cZ 139 ∧ sCG cZ 139 ≤ (-999252498075443 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_sin

theorem thL_141_r_bounds : (19221414798532511913 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 ≤ (19221423451467488087 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_141
  have hl : (164773226366594707 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 141 ∧ 16647931 / 100000 * Real.log 141 ≤ (51491633261161533 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_141_eq : (16647931 / 100000 * Real.log 141) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_141_cos_r : (718705873309977 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) ≤ (718706219516463 / 1000000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (153771353 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) (153771353 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 - (153771353 / 200000000 : ℝ)| ≤ (4326467488087 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 - (153771353 / 200000000 : ℝ))]

theorem thL_141_sin_r : (139062774043653 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) ≤ (695314216340933 / 1000000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (153771353 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524) (153771353 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 - (153771353 / 200000000 : ℝ)| ≤ (4326467488087 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 141) 524 - (153771353 / 200000000 : ℝ))]

theorem thL_141_cos : (718705873309977 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 141) ∧ Real.cos (16647931 / 100000 * Real.log 141) ≤ (718706219516463 / 1000000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_141_sin : (139062774043653 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 141) ∧ Real.sin (16647931 / 100000 * Real.log 141) ≤ (695314216340933 / 1000000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_141 : (718705873309977 / 1000000000000000 : ℝ) ≤ cCG cZ 141 ∧ cCG cZ 141 ≤ (718706219516463 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_cos

theorem sCB_141 : (139062774043653 / 200000000000000 : ℝ) ≤ sCG cZ 141 ∧ sCG cZ 141 ≤ (695314216340933 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_sin

theorem thL_142_r_bounds : (1498389551124596383 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 ≤ (1498390936875403617 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_142
  have hl : (412521334477964291 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 142 ∧ 16647931 / 100000 * Real.log 142 ≤ (103130333662692447 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_142_eq : (16647931 / 100000 * Real.log 142) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 + π / 2) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_142_cos_r : (930654775688621 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) ≤ (46532756106317 / 50000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (374597561 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) (374597561 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 - (374597561 / 1000000000 : ℝ)| ≤ (692875403617 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 - (374597561 / 1000000000 : ℝ))]

theorem thL_142_sin_r : (182948926830111 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) ≤ (14635928003917 / 40000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (374597561 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525) (374597561 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 - (374597561 / 1000000000 : ℝ)| ≤ (692875403617 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 142) 525 - (374597561 / 1000000000 : ℝ))]

theorem thL_142_cos : (-14635928003917 / 40000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 142) ∧ Real.cos (16647931 / 100000 * Real.log 142) ≤ (-182948926830111 / 500000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_142_sin : (930654775688621 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 142) ∧ Real.sin (16647931 / 100000 * Real.log 142) ≤ (46532756106317 / 50000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_142 : (-14635928003917 / 40000000000000 : ℝ) ≤ cCG cZ 142 ∧ cCG cZ 142 ≤ (-182948926830111 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_cos

theorem sCB_142 : (930654775688621 / 1000000000000000 : ℝ) ≤ sCG cZ 142 ∧ sCG cZ 142 ≤ (46532756106317 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_sin

theorem thL_143_r_bounds : (-2791828410069571761 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 ≤ (-2791793789930428239 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_143
  have hl : (413105474805007463 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 143 ∧ 16647931 / 100000 * Real.log 143 ≤ (826210949955625919 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_143_eq : (16647931 / 100000 * Real.log 143) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 + π) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_143_cos_r : (249902535437529 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) ≤ (249902621987877 / 250000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(27918111 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) (-(27918111 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 - (-(27918111 / 1000000000 : ℝ))| ≤ (17310069571761 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 - (-(27918111 / 1000000000 : ℝ)))]

theorem thL_143_sin_r : (-1395732879103 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) ≤ (-27914311380667 / 1000000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (27918111 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7860718829952003502998511618102750906423654573102015063533289255497501853651272383912532976145984919077623192291217797887 / 281600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(27918111 / 1000000000 : ℝ)) ∧ Real.sin (-(27918111 / 1000000000 : ℝ)) ≤ -((13756257952416006130247395331184467963385828844795075973775907505606728123982598451984757116510584818769 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526) (-(27918111 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 - (-(27918111 / 1000000000 : ℝ))| ≤ (17310069571761 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 143) 526 - (-(27918111 / 1000000000 : ℝ)))]

theorem thL_143_cos : (-249902621987877 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 143) ∧ Real.cos (16647931 / 100000 * Real.log 143) ≤ (-249902535437529 / 250000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_143_sin : (27914311380667 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 143) ∧ Real.sin (16647931 / 100000 * Real.log 143) ≤ (1395732879103 / 50000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_143 : (-249902621987877 / 250000000000000 : ℝ) ≤ cCG cZ 143 ∧ cCG cZ 143 ≤ (-249902535437529 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_cos

theorem sCB_143 : (27914311380667 / 1000000000000000 : ℝ) ≤ sCG cZ 143 ∧ sCG cZ 143 ≤ (1395732879103 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_sin

theorem thL_144_r_bounds : (-43857535207679166579 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 ≤ (-43857500592320833421 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_144
  have hl : (827371088869376317 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 144 ∧ 16647931 / 100000 * Real.log 144 ≤ (82737108921498731 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_144_eq : (16647931 / 100000 * Real.log 144) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 + π + π / 2) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_144_cos_r : (452678729528763 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) ≤ (56584862825701 / 62500000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(438575179 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) (-(438575179 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 - (-(438575179 / 1000000000 : ℝ))| ≤ (17307679166579 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 - (-(438575179 / 1000000000 : ℝ)))]

theorem thL_144_sin_r : (-212325048528237 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) ≤ (-212324875451443 / 500000000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (438575179 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((377757701334271066797110764748907991221822137875479592578695820853322549996750713897770235714915376445155822420877335275728877 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(438575179 / 1000000000 : ℝ)) ∧ Real.sin (-(438575179 / 1000000000 : ℝ)) ≤ -((2421523726501717267718094127346274573703298666688115136491363396784191070842643438763681924145805184625003 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527) (-(438575179 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 - (-(438575179 / 1000000000 : ℝ))| ≤ (17307679166579 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 144) 527 - (-(438575179 / 1000000000 : ℝ)))]

theorem thL_144_cos : (-212325048528237 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 144) ∧ Real.cos (16647931 / 100000 * Real.log 144) ≤ (-212324875451443 / 500000000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_144_sin : (-56584862825701 / 62500000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 144) ∧ Real.sin (16647931 / 100000 * Real.log 144) ≤ (-452678729528763 / 500000000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_144 : (-212325048528237 / 500000000000000 : ℝ) ≤ cCG cZ 144 ∧ cCG cZ 144 ≤ (-212324875451443 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_cos

theorem sCB_144 : (-56584862825701 / 62500000000000 : ℝ) ≤ sCG cZ 144 ∧ sCG cZ 144 ≤ (-452678729528763 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_sin

theorem thL_146_r_bounds : (3586638410873713049 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 ≤ (3586642739126286951 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_146
  have hl : (51854211976285957 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 146 ∧ 16647931 / 100000 * Real.log 146 ≤ (414833695983093153 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_146_eq : (16647931 / 100000 * Real.log 146) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_146_cos_r : (959116706031833 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) ≤ (23977926307301 / 25000000000000 : ℝ) := by
  have hr := thL_146_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (143465623 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) (143465623 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 - (143465623 / 500000000 : ℝ)| ≤ (2164126286951 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 - (143465623 / 500000000 : ℝ))]

theorem thL_146_sin_r : (141505047711647 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) ≤ (283010441683501 / 1000000000000000 : ℝ) := by
  have hr := thL_146_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (143465623 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528) (143465623 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 - (143465623 / 500000000 : ℝ)| ≤ (2164126286951 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 146) 528 - (143465623 / 500000000 : ℝ))]

theorem thL_146_cos : (959116706031833 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 146) ∧ Real.cos (16647931 / 100000 * Real.log 146) ≤ (23977926307301 / 25000000000000 : ℝ) := by
  have hc := thL_146_cos_r
  have hs := thL_146_sin_r
  rw [thL_146_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_146_sin : (141505047711647 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 146) ∧ Real.sin (16647931 / 100000 * Real.log 146) ≤ (283010441683501 / 1000000000000000 : ℝ) := by
  have hc := thL_146_cos_r
  have hs := thL_146_sin_r
  rw [thL_146_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_146 : (959116706031833 / 1000000000000000 : ℝ) ≤ cCG cZ 146 ∧ cCG cZ 146 ≤ (23977926307301 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_146_cos

theorem sCB_146 : (141505047711647 / 500000000000000 : ℝ) ≤ sCG cZ 146 ∧ sCG cZ 146 ≤ (283010441683501 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_146_sin

theorem thL_147_r_bounds : (-29496659784145715063 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 ≤ (-29496590615854284937 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_147
  have hl : (830803773575579583 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 147 ∧ 16647931 / 100000 * Real.log 147 ≤ (51925235870074411 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_147_eq : (16647931 / 100000 * Real.log 147) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 + π / 2) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_147_cos_r : (989143889808409 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) ≤ (989144235649867 / 1000000000000000 : ℝ) := by
  have hr := thL_147_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(73741563 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) (-(73741563 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 - (-(73741563 / 500000000 : ℝ))| ≤ (34584145715063 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 - (-(73741563 / 500000000 : ℝ)))]

theorem thL_147_sin_r : (-73474611242249 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) ≤ (-918430479019 / 6250000000000 : ℝ) := by
  have hr := thL_147_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (73741563 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((65667856523809307264265229754923654981030580686389551924001052934385672609205359719257899358375523826976126651121604303 / 446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(73741563 / 500000000 : ℝ)) ∧ Real.sin (-(73741563 / 500000000 : ℝ)) ≤ -((5051373578754562097164950583279753769415839473620179094694116499138421861578068160710603382677017739 / 34375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529) (-(73741563 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 - (-(73741563 / 500000000 : ℝ))| ≤ (34584145715063 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 147) 529 - (-(73741563 / 500000000 : ℝ)))]

theorem thL_147_cos : (918430479019 / 6250000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 147) ∧ Real.cos (16647931 / 100000 * Real.log 147) ≤ (73474611242249 / 500000000000000 : ℝ) := by
  have hc := thL_147_cos_r
  have hs := thL_147_sin_r
  rw [thL_147_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_147_sin : (989143889808409 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 147) ∧ Real.sin (16647931 / 100000 * Real.log 147) ≤ (989144235649867 / 1000000000000000 : ℝ) := by
  have hc := thL_147_cos_r
  have hs := thL_147_sin_r
  rw [thL_147_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_147 : (918430479019 / 6250000000000 : ℝ) ≤ cCG cZ 147 ∧ cCG cZ 147 ≤ (73474611242249 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_147_cos

theorem sCB_147 : (989143889808409 / 1000000000000000 : ℝ) ≤ sCG cZ 147 ∧ sCG cZ 147 ≤ (989144235649867 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_147_sin

theorem thL_148_r_bounds : (-5896020152372048081 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 ≤ (-5896016687627951919 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_148
  have hl : (831932451186921419 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 148 ∧ 16647931 / 100000 * Real.log 148 ≤ (831932451532532413 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_148_eq : (16647931 / 100000 * Real.log 148) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 + π) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_148_cos_r : (831161959581163 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) ≤ (415581153029629 / 500000000000000 : ℝ) := by
  have hr := thL_148_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(294800921 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) (-(294800921 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 - (-(294800921 / 500000000 : ℝ))| ≤ (1732372048081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 - (-(294800921 / 500000000 : ℝ)))]

theorem thL_148_sin_r : (-556030306379923 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) ≤ (-278014979952673 / 500000000000000 : ℝ) := by
  have hr := thL_148_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (294800921 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((60379659676800969055987389012671195620014516262512281917451964344284174166370964897253488128755020765084885447738366857023 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(294800921 / 500000000 : ℝ)) ∧ Real.sin (-(294800921 / 500000000 : ℝ)) ≤ -((10837374813781532373970456265301542079822979006041766766073089176247756648737947337899260672303343917879 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530) (-(294800921 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 - (-(294800921 / 500000000 : ℝ))| ≤ (1732372048081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 148) 530 - (-(294800921 / 500000000 : ℝ)))]

theorem thL_148_cos : (-415581153029629 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 148) ∧ Real.cos (16647931 / 100000 * Real.log 148) ≤ (-831161959581163 / 1000000000000000 : ℝ) := by
  have hc := thL_148_cos_r
  have hs := thL_148_sin_r
  rw [thL_148_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_148_sin : (278014979952673 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 148) ∧ Real.sin (16647931 / 100000 * Real.log 148) ≤ (556030306379923 / 1000000000000000 : ℝ) := by
  have hc := thL_148_cos_r
  have hs := thL_148_sin_r
  rw [thL_148_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_148 : (-415581153029629 / 500000000000000 : ℝ) ≤ cCG cZ 148 ∧ cCG cZ 148 ≤ (-831161959581163 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_148_cos

theorem sCB_148 : (278014979952673 / 500000000000000 : ℝ) ≤ sCG cZ 148 ∧ sCG cZ 148 ≤ (556030306379923 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_148_sin

theorem thL_149_r_bounds : (5314750156948391919 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 ≤ (5314753623051608081 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_149
  have hl : (3254115344601521 / 3906250000000 : ℝ) ≤ 16647931 / 100000 * Real.log 149 ∧ 16647931 / 100000 * Real.log 149 ≤ (833053528563600369 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_149_eq : (16647931 / 100000 * Real.log 149) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 + π) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_149_cos_r : (53878762590141 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) ≤ (862060548053639 / 1000000000000000 : ℝ) := by
  have hr := thL_149_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (531475189 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) (531475189 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 - (531475189 / 1000000000 : ℝ)| ≤ (1733051608081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 - (531475189 / 1000000000 : ℝ))]

theorem thL_149_sin_r : (506805420871219 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) ≤ (101361153496317 / 200000000000000 : ℝ) := by
  have hr := thL_149_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (531475189 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530) (531475189 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 - (531475189 / 1000000000 : ℝ)| ≤ (1733051608081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 149) 530 - (531475189 / 1000000000 : ℝ))]

theorem thL_149_cos : (-862060548053639 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 149) ∧ Real.cos (16647931 / 100000 * Real.log 149) ≤ (-53878762590141 / 62500000000000 : ℝ) := by
  have hc := thL_149_cos_r
  have hs := thL_149_sin_r
  rw [thL_149_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_149_sin : (-101361153496317 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 149) ∧ Real.sin (16647931 / 100000 * Real.log 149) ≤ (-506805420871219 / 1000000000000000 : ℝ) := by
  have hc := thL_149_cos_r
  have hs := thL_149_sin_r
  rw [thL_149_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_149 : (-862060548053639 / 1000000000000000 : ℝ) ≤ cCG cZ 149 ∧ cCG cZ 149 ≤ (-53878762590141 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_149_cos

theorem sCB_149 : (-101361153496317 / 200000000000000 : ℝ) ≤ sCG cZ 149 ∧ sCG cZ 149 ≤ (-506805420871219 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_149_sin

theorem thL_151_r_bounds : (-19518030894168021651 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 ≤ (-19518013605831978349 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_151
  have hl : (835273285237001641 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 151 ∧ 16647931 / 100000 * Real.log 151 ≤ (417636642791306317 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_151_eq : (16647931 / 100000 * Real.log 151) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_151_cos_r : (231192947470309 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) ≤ (57798258477999 / 62500000000000 : ℝ) := by
  have hr := thL_151_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(78072089 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) (-(78072089 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 - (-(78072089 / 200000000 : ℝ))| ≤ (8644168021651 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 - (-(78072089 / 200000000 : ℝ)))]

theorem thL_151_sin_r : (-380521942148231 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) ≤ (-95130399095377 / 250000000000000 : ℝ) := by
  have hr := thL_151_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (78072089 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1941108303515767977845278114579550085681897874844982653782559628705089211889997978942929824344245028856981505004669369 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(78072089 / 200000000 : ℝ)) ∧ Real.sin (-(78072089 / 200000000 : ℝ)) ≤ -((311075048640346790752235295655254070625341744576983056057886316886312362487232663531273335859667511 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532) (-(78072089 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 - (-(78072089 / 200000000 : ℝ))| ≤ (8644168021651 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 151) 532 - (-(78072089 / 200000000 : ℝ)))]

theorem thL_151_cos : (231192947470309 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 151) ∧ Real.cos (16647931 / 100000 * Real.log 151) ≤ (57798258477999 / 62500000000000 : ℝ) := by
  have hc := thL_151_cos_r
  have hs := thL_151_sin_r
  rw [thL_151_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_151_sin : (-380521942148231 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 151) ∧ Real.sin (16647931 / 100000 * Real.log 151) ≤ (-95130399095377 / 250000000000000 : ℝ) := by
  have hc := thL_151_cos_r
  have hs := thL_151_sin_r
  rw [thL_151_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_151 : (231192947470309 / 250000000000000 : ℝ) ≤ cCG cZ 151 ∧ cCG cZ 151 ≤ (57798258477999 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_151_cos

theorem sCB_151 : (-380521942148231 / 1000000000000000 : ℝ) ≤ sCG cZ 151 ∧ sCG cZ 151 ≤ (-95130399095377 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_151_sin

theorem thL_152_r_bounds : (35425835259207428349 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 ≤ (35425852540792571651 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_152
  have hl : (16727443251201383 / 20000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 152 ∧ 16647931 / 100000 * Real.log 152 ≤ (836372162905680143 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_152_eq : (16647931 / 100000 * Real.log 152) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_152_cos_r : (37966380886377 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) ≤ (759327963392653 / 1000000000000000 : ℝ) := by
  have hr := thL_152_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (354258439 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) (354258439 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 - (354258439 / 500000000 : ℝ)| ≤ (8640792571651 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 - (354258439 / 500000000 : ℝ))]

theorem thL_152_sin_r : (650708138530737 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) ≤ (325354242082131 / 500000000000000 : ℝ) := by
  have hr := thL_152_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (354258439 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532) (354258439 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 - (354258439 / 500000000 : ℝ)| ≤ (8640792571651 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 152) 532 - (354258439 / 500000000 : ℝ))]

theorem thL_152_cos : (37966380886377 / 50000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 152) ∧ Real.cos (16647931 / 100000 * Real.log 152) ≤ (759327963392653 / 1000000000000000 : ℝ) := by
  have hc := thL_152_cos_r
  have hs := thL_152_sin_r
  rw [thL_152_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_152_sin : (650708138530737 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 152) ∧ Real.sin (16647931 / 100000 * Real.log 152) ≤ (325354242082131 / 500000000000000 : ℝ) := by
  have hc := thL_152_cos_r
  have hs := thL_152_sin_r
  rw [thL_152_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_152 : (37966380886377 / 50000000000000 : ℝ) ≤ cCG cZ 152 ∧ cCG cZ 152 ≤ (759327963392653 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_152_cos

theorem sCB_152 : (650708138530737 / 1000000000000000 : ℝ) ≤ sCG cZ 152 ∧ sCG cZ 152 ≤ (325354242082131 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_152_sin

theorem thL_153_r_bounds : (45878379341487589549 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 ≤ (45878448658512410451 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_153
  have hl : (104682979259798417 / 125000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 153 ∧ 16647931 / 100000 * Real.log 153 ≤ (837463834423998329 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_153_eq : (16647931 / 100000 * Real.log 153) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 + π / 2) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_153_cos_r : (973804636156893 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) ≤ (486902491371009 / 500000000000000 : ℝ) := by
  have hr := thL_153_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (22939207 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) (22939207 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 - (22939207 / 100000000 : ℝ)| ≤ (34658512410451 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 - (22939207 / 100000000 : ℝ))]

theorem thL_153_sin_r : (56846346784933 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) ≤ (227385733724857 / 1000000000000000 : ℝ) := by
  have hr := thL_153_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (22939207 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533) (22939207 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 - (22939207 / 100000000 : ℝ)| ≤ (34658512410451 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 153) 533 - (22939207 / 100000000 : ℝ))]

theorem thL_153_cos : (-227385733724857 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 153) ∧ Real.cos (16647931 / 100000 * Real.log 153) ≤ (-56846346784933 / 250000000000000 : ℝ) := by
  have hc := thL_153_cos_r
  have hs := thL_153_sin_r
  rw [thL_153_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_153_sin : (973804636156893 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 153) ∧ Real.sin (16647931 / 100000 * Real.log 153) ≤ (486902491371009 / 500000000000000 : ℝ) := by
  have hc := thL_153_cos_r
  have hs := thL_153_sin_r
  rw [thL_153_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_153 : (-227385733724857 / 1000000000000000 : ℝ) ≤ cCG cZ 153 ∧ cCG cZ 153 ≤ (-56846346784933 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_153_cos

theorem sCB_153 : (973804636156893 / 1000000000000000 : ℝ) ≤ sCG cZ 153 ∧ sCG cZ 153 ≤ (486902491371009 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_153_sin

theorem thL_154_r_bounds : (-25684482880903667149 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 ≤ (-25684448319096332851 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_154
  have hl : (419274196839832879 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 154 ∧ 16647931 / 100000 * Real.log 154 ≤ (838548394025276751 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_154_eq : (16647931 / 100000 * Real.log 154) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 + π) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_154_cos_r : (967196170776457 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) ≤ (967196516394531 / 1000000000000000 : ℝ) := by
  have hr := thL_154_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(16052791 / 62500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) (-(16052791 / 62500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 - (-(16052791 / 62500000 : ℝ))| ≤ (17280903667149 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 - (-(16052791 / 62500000 : ℝ)))]

theorem thL_154_sin_r : (-254030157170827 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) ≤ (-254029811552753 / 1000000000000000 : ℝ) := by
  have hr := thL_154_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (16052791 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((351241257511190396818275282281399762863217617658552782887319832394405422191707480210468225681340661308239050071 / 1382676373395952396094799041748046875000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(16052791 / 62500000 : ℝ)) ∧ Real.sin (-(16052791 / 62500000 : ℝ)) ≤ -((576395909761953463987911174155195149264837576464208298903182897321679059362833055139701758809 / 2269007381983101367950439453125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534) (-(16052791 / 62500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 - (-(16052791 / 62500000 : ℝ))| ≤ (17280903667149 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 154) 534 - (-(16052791 / 62500000 : ℝ)))]

theorem thL_154_cos : (-967196516394531 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 154) ∧ Real.cos (16647931 / 100000 * Real.log 154) ≤ (-967196170776457 / 1000000000000000 : ℝ) := by
  have hc := thL_154_cos_r
  have hs := thL_154_sin_r
  rw [thL_154_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_154_sin : (254029811552753 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 154) ∧ Real.sin (16647931 / 100000 * Real.log 154) ≤ (254030157170827 / 1000000000000000 : ℝ) := by
  have hc := thL_154_cos_r
  have hs := thL_154_sin_r
  rw [thL_154_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_154 : (-967196516394531 / 1000000000000000 : ℝ) ≤ cCG cZ 154 ∧ cCG cZ 154 ≤ (-967196170776457 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_154_cos

theorem sCB_154 : (254029811552753 / 1000000000000000 : ℝ) ≤ sCG cZ 154 ∧ sCG cZ 154 ≤ (254030157170827 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_154_sin

theorem thL_156_r_bounds : (12820351125146988371 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 ≤ (12820364954853011629 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_156
  have hl : (420348271806699183 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 156 ∧ 16647931 / 100000 * Real.log 156 ≤ (840696543959009359 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_156_eq : (16647931 / 100000 * Real.log 156) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 + π + π / 2) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_156_cos_r : (474537511655839 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) ≤ (237268842263583 / 250000000000000 : ℝ) := by
  have hr := thL_156_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (320508951 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) (320508951 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 - (320508951 / 1000000000 : ℝ)| ≤ (6914853011629 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 - (320508951 / 1000000000 : ℝ))]

theorem thL_156_sin_r : (15752473064897 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) ≤ (19690612940037 / 62500000000000 : ℝ) := by
  have hr := thL_156_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (320508951 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535) (320508951 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 - (320508951 / 1000000000 : ℝ)| ≤ (6914853011629 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 156) 535 - (320508951 / 1000000000 : ℝ))]

theorem thL_156_cos : (15752473064897 / 50000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 156) ∧ Real.cos (16647931 / 100000 * Real.log 156) ≤ (19690612940037 / 62500000000000 : ℝ) := by
  have hc := thL_156_cos_r
  have hs := thL_156_sin_r
  rw [thL_156_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_156_sin : (-237268842263583 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 156) ∧ Real.sin (16647931 / 100000 * Real.log 156) ≤ (-474537511655839 / 500000000000000 : ℝ) := by
  have hc := thL_156_cos_r
  have hs := thL_156_sin_r
  rw [thL_156_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_156 : (15752473064897 / 50000000000000 : ℝ) ≤ cCG cZ 156 ∧ cCG cZ 156 ≤ (19690612940037 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_156_cos

theorem sCB_156 : (-237268842263583 / 250000000000000 : ℝ) ≤ sCG cZ 156 ∧ sCG cZ 156 ≤ (-474537511655839 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_156_sin

theorem thL_157_r_bounds : (-4662959253587797749 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 ≤ (-4662950596412202251 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_157
  have hl : (210440078197980269 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 157 ∧ 16647931 / 100000 * Real.log 157 ≤ (841760313137532069 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_157_eq : (16647931 / 100000 * Real.log 157) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_157_cos_r : (982655677723097 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) ≤ (491328012005061 / 500000000000000 : ℝ) := by
  have hr := thL_157_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(186518197 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) (-(186518197 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 - (-(186518197 / 1000000000 : ℝ))| ≤ (4328587797749 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 - (-(186518197 / 1000000000 : ℝ)))]

theorem thL_157_sin_r : (-37087756994801 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) ≤ (-185438438686981 / 1000000000000000 : ℝ) := by
  have hr := thL_157_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (186518197 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1154730092991606051125671282733367873730060290573101019296948903493758122251135045817302788859855615737724276049706191356006277 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(186518197 / 1000000000 : ℝ)) ∧ Real.sin (-(186518197 / 1000000000 : ℝ)) ≤ -((7402115980715423402532152641889171927959127815759752366268990038513537048713356269015516131303966065667347 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536) (-(186518197 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 - (-(186518197 / 1000000000 : ℝ))| ≤ (4328587797749 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 157) 536 - (-(186518197 / 1000000000 : ℝ)))]

theorem thL_157_cos : (982655677723097 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 157) ∧ Real.cos (16647931 / 100000 * Real.log 157) ≤ (491328012005061 / 500000000000000 : ℝ) := by
  have hc := thL_157_cos_r
  have hs := thL_157_sin_r
  rw [thL_157_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_157_sin : (-37087756994801 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 157) ∧ Real.sin (16647931 / 100000 * Real.log 157) ≤ (-185438438686981 / 1000000000000000 : ℝ) := by
  have hc := thL_157_cos_r
  have hs := thL_157_sin_r
  rw [thL_157_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_157 : (982655677723097 / 1000000000000000 : ℝ) ≤ cCG cZ 157 ∧ cCG cZ 157 ≤ (491328012005061 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_157_cos

theorem sCB_157 : (-37087756994801 / 200000000000000 : ℝ) ≤ sCG cZ 157 ∧ sCG cZ 157 ≤ (-185438438686981 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_157_sin

theorem thL_158_r_bounds : (-140059930792479705839 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 ≤ (-140059861607520294161 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_158
  have hl : (421408663917448543 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 158 ∧ 16647931 / 100000 * Real.log 158 ≤ (842817328180508079 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_158_eq : (16647931 / 100000 * Real.log 158) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_158_cos_r : (7646490490399 / 10000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) ≤ (764649394993743 / 1000000000000000 : ℝ) := by
  have hr := thL_158_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(700299481 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) (-(700299481 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 - (-(700299481 / 1000000000 : ℝ))| ≤ (34592479705839 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 - (-(700299481 / 1000000000 : ℝ)))]

theorem thL_158_sin_r : (-322223443505091 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) ≤ (-644446541083819 / 1000000000000000 : ℝ) := by
  have hr := thL_158_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (700299481 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((573283298981028231075131049860180658411134725682637861762159967864210346267934059651401318313999885557005106233168063830728063 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(700299481 / 1000000000 : ℝ)) ∧ Real.sin (-(700299481 / 1000000000 : ℝ)) ≤ -((3674892942177156309804572075240268347483677962269058324686292479843331437526674255571321125719378259964817 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537) (-(700299481 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 - (-(700299481 / 1000000000 : ℝ))| ≤ (34592479705839 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 158) 537 - (-(700299481 / 1000000000 : ℝ)))]

theorem thL_158_cos : (644446541083819 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 158) ∧ Real.cos (16647931 / 100000 * Real.log 158) ≤ (322223443505091 / 500000000000000 : ℝ) := by
  have hc := thL_158_cos_r
  have hs := thL_158_sin_r
  rw [thL_158_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_158_sin : (7646490490399 / 10000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 158) ∧ Real.sin (16647931 / 100000 * Real.log 158) ≤ (764649394993743 / 1000000000000000 : ℝ) := by
  have hc := thL_158_cos_r
  have hs := thL_158_sin_r
  rw [thL_158_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_158 : (644446541083819 / 1000000000000000 : ℝ) ≤ cCG cZ 158 ∧ cCG cZ 158 ≤ (322223443505091 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_158_cos

theorem sCB_158 : (7646490490399 / 10000000000000 : ℝ) ≤ sCG cZ 158 ∧ sCG cZ 158 ≤ (764649394993743 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_158_sin

theorem thL_159_r_bounds : (70009296001113694161 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 ≤ (70009365198886305839 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_159
  have hl : (843867673968865053 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 159 ∧ 16647931 / 100000 * Real.log 159 ≤ (421933837157238023 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_159_eq : (16647931 / 100000 * Real.log 159) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_159_cos_r : (939356541619261 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) ≤ (234839221902033 / 250000000000000 : ℝ) := by
  have hr := thL_159_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (350046653 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) (350046653 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 - (350046653 / 1000000000 : ℝ)| ≤ (34598886305839 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 - (350046653 / 1000000000 : ℝ))]

theorem thL_159_sin_r : (342941458643017 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) ≤ (342941804631881 / 1000000000000000 : ℝ) := by
  have hr := thL_159_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (350046653 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537) (350046653 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 - (350046653 / 1000000000 : ℝ)| ≤ (34598886305839 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 159) 537 - (350046653 / 1000000000 : ℝ))]

theorem thL_159_cos : (-342941804631881 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 159) ∧ Real.cos (16647931 / 100000 * Real.log 159) ≤ (-342941458643017 / 1000000000000000 : ℝ) := by
  have hc := thL_159_cos_r
  have hs := thL_159_sin_r
  rw [thL_159_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_159_sin : (939356541619261 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 159) ∧ Real.sin (16647931 / 100000 * Real.log 159) ≤ (234839221902033 / 250000000000000 : ℝ) := by
  have hc := thL_159_cos_r
  have hs := thL_159_sin_r
  rw [thL_159_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_159 : (-342941804631881 / 1000000000000000 : ℝ) ≤ cCG cZ 159 ∧ cCG cZ 159 ≤ (-342941458643017 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_159_cos

theorem sCB_159 : (939356541619261 / 1000000000000000 : ℝ) ≤ sCG cZ 159 ∧ sCG cZ 159 ≤ (234839221902033 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_159_sin

theorem thL_161_r_bounds : (-71052770190371623503 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 ≤ (-71052735609628376497 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_161
  have hl : (845948692440742001 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 161 ∧ 16647931 / 100000 * Real.log 161 ≤ (422974346393176497 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_161_eq : (16647931 / 100000 * Real.log 161) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 + π + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_161_cos_r : (758017736329813 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) ≤ (758018082171811 / 1000000000000000 : ℝ) := by
  have hr := thL_161_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(710527529 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) (-(710527529 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 - (-(710527529 / 1000000000 : ℝ))| ≤ (17290371623503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 - (-(710527529 / 1000000000 : ℝ)))]

theorem thL_161_sin_r : (-326116955545201 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) ≤ (-16305839132027 / 25000000000000 : ℝ) := by
  have hr := thL_161_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (710527529 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4061473054150244883428424323261941169754862802771550975910574771226278595642203162982111983841205567106018705265779452224759689 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(710527529 / 1000000000 : ℝ)) ∧ Real.sin (-(710527529 / 1000000000 : ℝ)) ≤ -((26035083680374878013107332729032444021874907325910598355218681117946660081030522560730971333680547914241671 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539) (-(710527529 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 - (-(710527529 / 1000000000 : ℝ))| ≤ (17290371623503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 161) 539 - (-(710527529 / 1000000000 : ℝ)))]

theorem thL_161_cos : (-326116955545201 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 161) ∧ Real.cos (16647931 / 100000 * Real.log 161) ≤ (-16305839132027 / 25000000000000 : ℝ) := by
  have hc := thL_161_cos_r
  have hs := thL_161_sin_r
  rw [thL_161_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_161_sin : (-758018082171811 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 161) ∧ Real.sin (16647931 / 100000 * Real.log 161) ≤ (-758017736329813 / 1000000000000000 : ℝ) := by
  have hc := thL_161_cos_r
  have hs := thL_161_sin_r
  rw [thL_161_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_161 : (-326116955545201 / 500000000000000 : ℝ) ≤ cCG cZ 161 ∧ cCG cZ 161 ≤ (-16305839132027 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_161_cos

theorem sCB_161 : (-758018082171811 / 1000000000000000 : ℝ) ≤ sCG cZ 161 ∧ sCG cZ 161 ≤ (-758017736329813 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_161_sin

theorem thL_162_r_bounds : (64061446541430646467 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 ≤ (64061515858569353533 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_162
  have hl : (846979527375156431 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 162 ∧ 16647931 / 100000 * Real.log 162 ≤ (13234055120636991 / 15625000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_162_eq : (16647931 / 100000 * Real.log 162) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 + π + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_162_cos_r : (118642312536543 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) ≤ (949138846878041 / 1000000000000000 : ℝ) := by
  have hr := thL_162_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (160153703 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) (160153703 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 - (160153703 / 500000000 : ℝ)| ≤ (34658569353533 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 - (160153703 / 500000000 : ℝ))]

theorem thL_162_sin_r : (15742908655929 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) ≤ (157429259852137 / 500000000000000 : ℝ) := by
  have hr := thL_162_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (160153703 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539) (160153703 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 - (160153703 / 500000000 : ℝ)| ≤ (34658569353533 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 162) 539 - (160153703 / 500000000 : ℝ))]

theorem thL_162_cos : (15742908655929 / 50000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 162) ∧ Real.cos (16647931 / 100000 * Real.log 162) ≤ (157429259852137 / 500000000000000 : ℝ) := by
  have hc := thL_162_cos_r
  have hs := thL_162_sin_r
  rw [thL_162_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_162_sin : (-949138846878041 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 162) ∧ Real.sin (16647931 / 100000 * Real.log 162) ≤ (-118642312536543 / 125000000000000 : ℝ) := by
  have hc := thL_162_cos_r
  have hs := thL_162_sin_r
  rw [thL_162_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_162 : (15742908655929 / 50000000000000 : ℝ) ≤ cCG cZ 162 ∧ cCG cZ 162 ≤ (157429259852137 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_162_cos

theorem sCB_162 : (-949138846878041 / 1000000000000000 : ℝ) ≤ sCG cZ 162 ∧ sCG cZ 162 ≤ (-118642312536543 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_162_sin

theorem thL_163_r_bounds : (-1129989000892483079 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 ≤ (-1129987269107516921 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_163
  have hl : (424002009334905839 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 163 ∧ 16647931 / 100000 * Real.log 163 ≤ (848004019015422671 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_163_eq : (16647931 / 100000 * Real.log 163) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_163_cos_r : (974570871910061 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) ≤ (194914243653411 / 200000000000000 : ℝ) := by
  have hr := thL_163_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(225997627 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) (-(225997627 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 - (-(225997627 / 1000000000 : ℝ))| ≤ (865892483079 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 - (-(225997627 / 1000000000 : ℝ)))]

theorem thL_163_sin_r : (-44815781009043 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) ≤ (-224078558688221 / 1000000000000000 : ℝ) := by
  have hr := thL_163_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (225997627 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1395342924171674942512825647601301870322614613430889015625259892793562788343915623215866735035225799898300107115610542381841067 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(225997627 / 1000000000 : ℝ)) ∧ Real.sin (-(225997627 / 1000000000 : ℝ)) ≤ -((8944505924177403451928991133733893840037526662547322038806370791054104466938314711326282086838051196578077 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540) (-(225997627 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 - (-(225997627 / 1000000000 : ℝ))| ≤ (865892483079 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 163) 540 - (-(225997627 / 1000000000 : ℝ)))]

theorem thL_163_cos : (974570871910061 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 163) ∧ Real.cos (16647931 / 100000 * Real.log 163) ≤ (194914243653411 / 200000000000000 : ℝ) := by
  have hc := thL_163_cos_r
  have hs := thL_163_sin_r
  rw [thL_163_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_163_sin : (-44815781009043 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 163) ∧ Real.sin (16647931 / 100000 * Real.log 163) ≤ (-224078558688221 / 1000000000000000 : ℝ) := by
  have hc := thL_163_cos_r
  have hs := thL_163_sin_r
  rw [thL_163_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_163 : (974570871910061 / 1000000000000000 : ℝ) ≤ cCG cZ 163 ∧ cCG cZ 163 ≤ (194914243653411 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_163_cos

theorem sCB_163 : (-44815781009043 / 200000000000000 : ℝ) ≤ sCG cZ 163 ∧ sCG cZ 163 ≤ (-224078558688221 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_163_sin

theorem thL_164_r_bounds : (-77856887304971799657 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 ≤ (-77856852695028200343 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_164
  have hl : (212255560980869449 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 164 ∧ 16647931 / 100000 * Real.log 164 ≤ (849022244269088789 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_164_eq : (16647931 / 100000 * Real.log 164) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 + π / 2) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_164_cos_r : (711919240152733 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) ≤ (355959793177869 / 500000000000000 : ℝ) := by
  have hr := thL_164_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(7785687 / 10000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) (-(7785687 / 10000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 - (-(7785687 / 10000000 : ℝ))| ≤ (17304971799657 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 - (-(7785687 / 10000000 : ℝ)))]

theorem thL_164_sin_r : (-351130670837351 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) ≤ (-351130497784531 / 500000000000000 : ℝ) := by
  have hr := thL_164_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (7785687 / 10000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1977567450847953070432663480362346452283187103742410125822448735808691311059640485412773555656919 / 2816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(7785687 / 10000000 : ℝ)) ∧ Real.sin (-(7785687 / 10000000 : ℝ)) ≤ -((4943918627076215755545551344667983405851275022609869861563905740894691418723106511 / 7040000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541) (-(7785687 / 10000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 - (-(7785687 / 10000000 : ℝ))| ≤ (17304971799657 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 164) 541 - (-(7785687 / 10000000 : ℝ)))]

theorem thL_164_cos : (351130497784531 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 164) ∧ Real.cos (16647931 / 100000 * Real.log 164) ≤ (351130670837351 / 500000000000000 : ℝ) := by
  have hc := thL_164_cos_r
  have hs := thL_164_sin_r
  rw [thL_164_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_164_sin : (711919240152733 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 164) ∧ Real.sin (16647931 / 100000 * Real.log 164) ≤ (355959793177869 / 500000000000000 : ℝ) := by
  have hc := thL_164_cos_r
  have hs := thL_164_sin_r
  rw [thL_164_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_164 : (351130497784531 / 500000000000000 : ℝ) ≤ cCG cZ 164 ∧ cCG cZ 164 ≤ (351130670837351 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_164_cos

theorem sCB_164 : (711919240152733 / 1000000000000000 : ℝ) ≤ sCG cZ 164 ∧ sCG cZ 164 ≤ (355959793177869 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_164_sin

theorem thL_166_r_bounds : (-16570473097040868867 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 ≤ (-16570455802959131133 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_166
  have hl : (53190012478822737 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 166 ∧ 16647931 / 100000 * Real.log 166 ≤ (170208040001354957 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_166_eq : (16647931 / 100000 * Real.log 166) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 + π) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_166_cos_r : (945584560998229 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) ≤ (236396226719967 / 250000000000000 : ℝ) := by
  have hr := thL_166_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(331409289 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) (-(331409289 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 - (-(331409289 / 1000000000 : ℝ))| ≤ (8647040868867 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 - (-(331409289 / 1000000000 : ℝ)))]

theorem thL_166_sin_r : (-81344031543121 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) ≤ (-325375780290849 / 1000000000000000 : ℝ) := by
  have hr := thL_166_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (331409289 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((8337954027133393685790893541785761948829097285657341140909500354370346544660376041143321935684535283270966418930040315173683 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(331409289 / 1000000000 : ℝ)) ∧ Real.sin (-(331409289 / 1000000000 : ℝ)) ≤ -((160345269752565217148724362611306432923496616090336334937457504000417692713625408830687969150802751691831 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542) (-(331409289 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 - (-(331409289 / 1000000000 : ℝ))| ≤ (8647040868867 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 166) 542 - (-(331409289 / 1000000000 : ℝ)))]

theorem thL_166_cos : (-236396226719967 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 166) ∧ Real.cos (16647931 / 100000 * Real.log 166) ≤ (-945584560998229 / 1000000000000000 : ℝ) := by
  have hc := thL_166_cos_r
  have hs := thL_166_sin_r
  rw [thL_166_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_166_sin : (325375780290849 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 166) ∧ Real.sin (16647931 / 100000 * Real.log 166) ≤ (81344031543121 / 250000000000000 : ℝ) := by
  have hc := thL_166_cos_r
  have hs := thL_166_sin_r
  rw [thL_166_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_166 : (-236396226719967 / 250000000000000 : ℝ) ≤ cCG cZ 166 ∧ cCG cZ 166 ≤ (-945584560998229 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_166_cos

theorem sCB_166 : (325375780290849 / 1000000000000000 : ℝ) ≤ sCG cZ 166 ∧ sCG cZ 166 ≤ (81344031543121 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_166_sin

theorem thL_167_r_bounds : (66846927971729637463 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 ≤ (66846962628270362537 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_167
  have hl : (26626252450079727 / 31250000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 167 ∧ 16647931 / 100000 * Real.log 167 ≤ (852040078748162257 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_167_eq : (16647931 / 100000 * Real.log 167) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 + π) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_167_cos_r : (784771022369989 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) ≤ (784771368952017 / 1000000000000000 : ℝ) := by
  have hr := thL_167_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (668469453 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) (668469453 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 - (668469453 / 1000000000 : ℝ)| ≤ (17328270362537 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 - (668469453 / 1000000000 : ℝ))]

theorem thL_167_sin_r : (619785410969433 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) ≤ (38736609845981 / 62500000000000 : ℝ) := by
  have hr := thL_167_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (668469453 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542) (668469453 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 - (668469453 / 1000000000 : ℝ)| ≤ (17328270362537 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 167) 542 - (668469453 / 1000000000 : ℝ))]

theorem thL_167_cos : (-784771368952017 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 167) ∧ Real.cos (16647931 / 100000 * Real.log 167) ≤ (-784771022369989 / 1000000000000000 : ℝ) := by
  have hc := thL_167_cos_r
  have hs := thL_167_sin_r
  rw [thL_167_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_167_sin : (-38736609845981 / 62500000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 167) ∧ Real.sin (16647931 / 100000 * Real.log 167) ≤ (-619785410969433 / 1000000000000000 : ℝ) := by
  have hc := thL_167_cos_r
  have hs := thL_167_sin_r
  rw [thL_167_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_167 : (-784771368952017 / 1000000000000000 : ℝ) ≤ cCG cZ 167 ∧ cCG cZ 167 ≤ (-784771022369989 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_167_cos

theorem sCB_167 : (-38736609845981 / 62500000000000 : ℝ) ≤ sCG cZ 167 ∧ sCG cZ 167 ≤ (-619785410969433 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_167_sin

theorem thL_168_r_bounds : (9158223296867224189 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 ≤ (9158257903132775811 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_168
  have hl : (426516993841524599 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 168 ∧ 16647931 / 100000 * Real.log 168 ≤ (26657312125895631 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_168_eq : (16647931 / 100000 * Real.log 168) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 + π + π / 2) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_168_cos_r : (995809088747581 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) ≤ (995809434810237 / 1000000000000000 : ℝ) := by
  have hr := thL_168_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (45791203 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) (45791203 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 - (45791203 / 500000000 : ℝ)| ≤ (17303132775811 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 - (45791203 / 500000000 : ℝ))]

theorem thL_168_sin_r : (22863566140271 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) ≤ (4572730531187 / 50000000000000 : ℝ) := by
  have hr := thL_168_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (45791203 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543) (45791203 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 - (45791203 / 500000000 : ℝ)| ≤ (17303132775811 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 168) 543 - (45791203 / 500000000 : ℝ))]

theorem thL_168_cos : (22863566140271 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 168) ∧ Real.cos (16647931 / 100000 * Real.log 168) ≤ (4572730531187 / 50000000000000 : ℝ) := by
  have hc := thL_168_cos_r
  have hs := thL_168_sin_r
  rw [thL_168_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_168_sin : (-995809434810237 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 168) ∧ Real.sin (16647931 / 100000 * Real.log 168) ≤ (-995809088747581 / 1000000000000000 : ℝ) := by
  have hc := thL_168_cos_r
  have hs := thL_168_sin_r
  rw [thL_168_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_168 : (22863566140271 / 250000000000000 : ℝ) ≤ cCG cZ 168 ∧ cCG cZ 168 ≤ (4572730531187 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_168_cos

theorem sCB_168 : (-995809434810237 / 1000000000000000 : ℝ) ≤ sCG cZ 168 ∧ sCG cZ 168 ≤ (-995809088747581 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_168_sin

theorem thL_169_r_bounds : (-3070021368770905399 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 ≤ (-3070019206229094601 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_169
  have hl : (6672046862167347 / 7812500000000 : ℝ) ≤ 16647931 / 100000 * Real.log 169 ∧ 16647931 / 100000 * Real.log 169 ≤ (854021998703031409 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_169_eq : (16647931 / 100000 * Real.log 169) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_169_cos_r : (881765768304477 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) ≤ (44088305715579 / 50000000000000 : ℝ) := by
  have hr := thL_169_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(245601623 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) (-(245601623 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 - (-(245601623 / 500000000 : ℝ))| ≤ (1081270905399 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 - (-(245601623 / 500000000 : ℝ)))]

theorem thL_169_sin_r : (-94337476742971 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) ≤ (-471687037708149 / 1000000000000000 : ℝ) := by
  have hr := thL_169_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (245601623 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((358545663109686947846759465811865010501293895408277042935420077976573666469849867939820711867161845955819950868400255304183 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(245601623 / 500000000 : ℝ)) ∧ Real.sin (-(245601623 / 500000000 : ℝ)) ≤ -((9193478541273720955568630950744266781784582220333223973399951461981587809706420908611758010164913063673 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544) (-(245601623 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 - (-(245601623 / 500000000 : ℝ))| ≤ (1081270905399 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 169) 544 - (-(245601623 / 500000000 : ℝ)))]

theorem thL_169_cos : (881765768304477 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 169) ∧ Real.cos (16647931 / 100000 * Real.log 169) ≤ (44088305715579 / 50000000000000 : ℝ) := by
  have hc := thL_169_cos_r
  have hs := thL_169_sin_r
  rw [thL_169_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_169_sin : (-94337476742971 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 169) ∧ Real.sin (16647931 / 100000 * Real.log 169) ≤ (-471687037708149 / 1000000000000000 : ℝ) := by
  have hc := thL_169_cos_r
  have hs := thL_169_sin_r
  rw [thL_169_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_169 : (881765768304477 / 1000000000000000 : ℝ) ≤ cCG cZ 169 ∧ cCG cZ 169 ≤ (44088305715579 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_169_cos

theorem sCB_169 : (-94337476742971 / 200000000000000 : ℝ) ≤ sCG cZ 169 ∧ sCG cZ 169 ≤ (-471687037708149 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_169_sin

theorem thL_171_r_bounds : (-2067940764832010393 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 ≤ (-2067933835167989607 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_171
  have hl : (171196120213169853 / 200000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 171 ∧ 16647931 / 100000 * Real.log 171 ≤ (427990300705730129 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_171_eq : (16647931 / 100000 * Real.log 171) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 + π / 2) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_171_cos_r : (994659131532059 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) ≤ (994659478015261 / 1000000000000000 : ℝ) := by
  have hr := thL_171_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(20679373 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) (-(20679373 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 - (-(20679373 / 200000000 : ℝ))| ≤ (3464832010393 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 - (-(20679373 / 200000000 : ℝ)))]

theorem thL_171_sin_r : (-12901612779929 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) ≤ (-10321255575623 / 100000000000000 : ℝ) := by
  have hr := thL_171_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (20679373 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3681861805545839860580202975474775383813053441703719031594143182128115603898966628687760396821395964170278673228531 / 35672555520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(20679373 / 200000000 : ℝ)) ∧ Real.sin (-(20679373 / 200000000 : ℝ)) ≤ -((7670545428220499709540247028010131196143759297585828741404872050167772991623255783426752969028993 / 74317824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545) (-(20679373 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 - (-(20679373 / 200000000 : ℝ))| ≤ (3464832010393 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 171) 545 - (-(20679373 / 200000000 : ℝ)))]

theorem thL_171_cos : (10321255575623 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 171) ∧ Real.cos (16647931 / 100000 * Real.log 171) ≤ (12901612779929 / 125000000000000 : ℝ) := by
  have hc := thL_171_cos_r
  have hs := thL_171_sin_r
  rw [thL_171_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_171_sin : (994659131532059 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 171) ∧ Real.sin (16647931 / 100000 * Real.log 171) ≤ (994659478015261 / 1000000000000000 : ℝ) := by
  have hc := thL_171_cos_r
  have hs := thL_171_sin_r
  rw [thL_171_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_171 : (10321255575623 / 100000000000000 : ℝ) ≤ cCG cZ 171 ∧ cCG cZ 171 ≤ (12901612779929 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_171_cos

theorem sCB_171 : (994659131532059 / 1000000000000000 : ℝ) ≤ sCG cZ 171 ∧ sCG cZ 171 ≤ (994659478015261 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_171_sin

theorem thL_172_r_bounds : (-70346577415845210231 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 ≤ (-70346542784154789769 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_172
  have hl : (428475664327927551 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 172 ∧ 16647931 / 100000 * Real.log 172 ≤ (171390265800293219 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_172_eq : (16647931 / 100000 * Real.log 172) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 + π) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_172_cos_r : (762604824081423 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) ≤ (762605170428989 / 1000000000000000 : ℝ) := by
  have hr := thL_172_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(703465601 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) (-(703465601 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 - (-(703465601 / 1000000000 : ℝ))| ≤ (17315845210231 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 - (-(703465601 / 1000000000 : ℝ)))]

theorem thL_172_sin_r : (-161716156072581 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) ≤ (-8085803474647 / 12500000000000 : ℝ) := by
  have hr := thL_172_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (703465601 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4028038391978747349713365239599732090451263192993210240318451157200981822185995892528738314567284396266634957360693234023132801 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(703465601 / 1000000000 : ℝ)) ∧ Real.sin (-(703465601 / 1000000000 : ℝ)) ≤ -((25820758922874461509491129690989227441258912168785902648581988527742329460127672709924894650743084537078399 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546) (-(703465601 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 - (-(703465601 / 1000000000 : ℝ))| ≤ (17315845210231 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 172) 546 - (-(703465601 / 1000000000 : ℝ)))]

theorem thL_172_cos : (-762605170428989 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 172) ∧ Real.cos (16647931 / 100000 * Real.log 172) ≤ (-762604824081423 / 1000000000000000 : ℝ) := by
  have hc := thL_172_cos_r
  have hs := thL_172_sin_r
  rw [thL_172_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_172_sin : (8085803474647 / 12500000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 172) ∧ Real.sin (16647931 / 100000 * Real.log 172) ≤ (161716156072581 / 250000000000000 : ℝ) := by
  have hc := thL_172_cos_r
  have hs := thL_172_sin_r
  rw [thL_172_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_172 : (-762605170428989 / 1000000000000000 : ℝ) ≤ cCG cZ 172 ∧ cCG cZ 172 ≤ (-762604824081423 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_172_cos

theorem sCB_172 : (8085803474647 / 12500000000000 : ℝ) ≤ sCG cZ 172 ∧ sCG cZ 172 ≤ (161716156072581 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_172_sin

theorem thL_173_r_bounds : (26163437791692189769 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 ≤ (26163472408307810231 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_173
  have hl : (214479107201982619 / 250000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 173 ∧ 16647931 / 100000 * Real.log 173 ≤ (85791642915354147 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_173_eq : (16647931 / 100000 * Real.log 173) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 + π) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_173_cos_r : (482984151493041 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) ≤ (12074608114403 / 12500000000000 : ℝ) := by
  have hr := thL_173_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (261634551 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) (261634551 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 - (261634551 / 1000000000 : ℝ)| ≤ (17308307810231 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 - (261634551 / 1000000000 : ℝ))]

theorem thL_173_sin_r : (129329824191267 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) ≤ (258659994548691 / 1000000000000000 : ℝ) := by
  have hr := thL_173_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (261634551 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546) (261634551 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 - (261634551 / 1000000000 : ℝ)| ≤ (17308307810231 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 173) 546 - (261634551 / 1000000000 : ℝ))]

theorem thL_173_cos : (-12074608114403 / 12500000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 173) ∧ Real.cos (16647931 / 100000 * Real.log 173) ≤ (-482984151493041 / 500000000000000 : ℝ) := by
  have hc := thL_173_cos_r
  have hs := thL_173_sin_r
  rw [thL_173_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_173_sin : (-258659994548691 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 173) ∧ Real.sin (16647931 / 100000 * Real.log 173) ≤ (-129329824191267 / 500000000000000 : ℝ) := by
  have hc := thL_173_cos_r
  have hs := thL_173_sin_r
  rw [thL_173_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_173 : (-12074608114403 / 12500000000000 : ℝ) ≤ cCG cZ 173 ∧ cCG cZ 173 ≤ (-482984151493041 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_173_cos

theorem sCB_173 : (-258659994548691 / 1000000000000000 : ℝ) ≤ sCG cZ 173 ∧ sCG cZ 173 ≤ (-129329824191267 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_173_sin

theorem thL_174_r_bounds : (-34962436502131828119 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 ≤ (-34962401897868171881 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_174
  have hl : (34355038655688751 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 174 ∧ 16647931 / 100000 * Real.log 174 ≤ (858875966737829769 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_174_eq : (16647931 / 100000 * Real.log 174) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 + π + π / 2) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_174_cos_r : (58718833576729 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) ≤ (939501683270309 / 1000000000000000 : ℝ) := by
  have hr := thL_174_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(2731439 / 7812500 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) (-(2731439 / 7812500 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 - (-(2731439 / 7812500 : ℝ))| ≤ (17302131828119 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 - (-(2731439 / 7812500 : ℝ)))]

theorem thL_174_sin_r : (-171272466245299 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) ≤ (-342544586447961 / 1000000000000000 : ℝ) := by
  have hr := thL_174_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (2731439 / 7812500 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((861525305933850595132666865055103578267585545404615130159811644467699729676033460394882940043391919 / 2515073671740451383984325806064674679873860441148281097412109375000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(2731439 / 7812500 : ℝ)) ∧ Real.sin (-(2731439 / 7812500 : ℝ)) ≤ -((90482247515514105336982756882770529558590557563832254428350530114506900825701142161 / 264147224601253560738456371836946345865726470947265625000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547) (-(2731439 / 7812500 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 - (-(2731439 / 7812500 : ℝ))| ≤ (17302131828119 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 174) 547 - (-(2731439 / 7812500 : ℝ)))]

theorem thL_174_cos : (-171272466245299 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 174) ∧ Real.cos (16647931 / 100000 * Real.log 174) ≤ (-342544586447961 / 1000000000000000 : ℝ) := by
  have hc := thL_174_cos_r
  have hs := thL_174_sin_r
  rw [thL_174_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_174_sin : (-939501683270309 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 174) ∧ Real.sin (16647931 / 100000 * Real.log 174) ≤ (-58718833576729 / 62500000000000 : ℝ) := by
  have hc := thL_174_cos_r
  have hs := thL_174_sin_r
  rw [thL_174_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_174 : (-171272466245299 / 500000000000000 : ℝ) ≤ cCG cZ 174 ∧ cCG cZ 174 ≤ (-342544586447961 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_174_cos

theorem sCB_174 : (-939501683270309 / 1000000000000000 : ℝ) ≤ sCG cZ 174 ∧ sCG cZ 174 ≤ (-58718833576729 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_174_sin

theorem thL_176_r_bounds : (-444482428575466549 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 ≤ (-444473771424533451 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_176
  have hl : (860778607787135373 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 176 ∧ 16647931 / 100000 * Real.log 176 ≤ (430389304066373183 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_176_eq : (16647931 / 100000 * Real.log 176) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_176_cos_r : (999841782395061 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) ≤ (9998421286811 / 10000000000000 : ℝ) := by
  have hr := thL_176_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(4444781 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) (-(4444781 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 - (-(4444781 / 250000000 : ℝ))| ≤ (4328575466549 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 - (-(4444781 / 250000000 : ℝ)))]

theorem thL_176_sin_r : (-3555672100491 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) ≤ (-17778014216417 / 1000000000000000 : ℝ) := by
  have hr := thL_176_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (4444781 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((149966833907776349597093603203917496041995711945918115487079920975056446135590212117226322168287321493250590099439031 / 8435440063476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(4444781 / 250000000 : ℝ)) ∧ Real.sin (-(4444781 / 250000000 : ℝ)) ≤ -((15381213734130907650983959302963432934775929079032527540733105373725465828704631507019662617724129 / 865173339843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548) (-(4444781 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 - (-(4444781 / 250000000 : ℝ))| ≤ (4328575466549 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 176) 548 - (-(4444781 / 250000000 : ℝ)))]

theorem thL_176_cos : (999841782395061 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 176) ∧ Real.cos (16647931 / 100000 * Real.log 176) ≤ (9998421286811 / 10000000000000 : ℝ) := by
  have hc := thL_176_cos_r
  have hs := thL_176_sin_r
  rw [thL_176_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_176_sin : (-3555672100491 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 176) ∧ Real.sin (16647931 / 100000 * Real.log 176) ≤ (-17778014216417 / 1000000000000000 : ℝ) := by
  have hc := thL_176_cos_r
  have hs := thL_176_sin_r
  rw [thL_176_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_176 : (999841782395061 / 1000000000000000 : ℝ) ≤ cCG cZ 176 ∧ cCG cZ 176 ≤ (9998421286811 / 10000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_176_cos

theorem sCB_176 : (-3555672100491 / 200000000000000 : ℝ) ≤ sCG cZ 176 ∧ sCG cZ 176 ≤ (-17778014216417 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_176_sin

theorem thL_177_r_bounds : (-64534754792879004273 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 ≤ (-64534720207120995727 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_177
  have hl : (21543045896567901 / 25000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 177 ∧ 16647931 / 100000 * Real.log 177 ≤ (430860918104163517 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_177_eq : (16647931 / 100000 * Real.log 177) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 + π / 2) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_177_cos_r : (99861338060809 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) ≤ (798891050354947 / 1000000000000000 : ℝ) := by
  have hr := thL_177_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(5162779 / 8000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) (-(5162779 / 8000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 - (-(5162779 / 8000000 : ℝ))| ≤ (17292879004273 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 - (-(5162779 / 8000000 : ℝ)))]

theorem thL_177_sin_r : (-601476162445667 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) ≤ (-300737908293773 / 500000000000000 : ℝ) := by
  have hr := thL_177_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (5162779 / 8000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2059057348064289385714921706865152798613500037400608381025712534864118585776455575297012415450972939 / 3423340888001504870400000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(5162779 / 8000000 : ℝ)) ∧ Real.sin (-(5162779 / 8000000 : ℝ)) ≤ -((206235711945356374869928926351173541577459558828312308788591493473129182715210391421 / 342882701121945600000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549) (-(5162779 / 8000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 - (-(5162779 / 8000000 : ℝ))| ≤ (17292879004273 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 177) 549 - (-(5162779 / 8000000 : ℝ)))]

theorem thL_177_cos : (300737908293773 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 177) ∧ Real.cos (16647931 / 100000 * Real.log 177) ≤ (601476162445667 / 1000000000000000 : ℝ) := by
  have hc := thL_177_cos_r
  have hs := thL_177_sin_r
  rw [thL_177_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_177_sin : (99861338060809 / 125000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 177) ∧ Real.sin (16647931 / 100000 * Real.log 177) ≤ (798891050354947 / 1000000000000000 : ℝ) := by
  have hc := thL_177_cos_r
  have hs := thL_177_sin_r
  rw [thL_177_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_177 : (300737908293773 / 500000000000000 : ℝ) ≤ cCG cZ 177 ∧ cCG cZ 177 ≤ (601476162445667 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_177_cos

theorem sCB_177 : (99861338060809 / 125000000000000 : ℝ) ≤ sCG cZ 177 ∧ sCG cZ 177 ≤ (798891050354947 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_177_sin

theorem thL_178_r_bounds : (58513307743766207997 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 ≤ (58513377056233792003 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_178
  have hl : (34506389997964683 / 40000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 178 ∧ 16647931 / 100000 * Real.log 178 ≤ (215664937573682017 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_178_eq : (16647931 / 100000 * Real.log 178) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 + π / 2) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_178_cos_r : (95750658957119 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) ≤ (95750693613353 / 100000000000000 : ℝ) := by
  have hr := thL_178_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (36570839 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) (36570839 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 - (36570839 / 125000000 : ℝ)| ≤ (34656233792003 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 - (36570839 / 125000000 : ℝ))]

theorem thL_178_sin_r : (57682128649937 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) ≤ (36051373726503 / 125000000000000 : ℝ) := by
  have hr := thL_178_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (36570839 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549) (36570839 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 - (36570839 / 125000000 : ℝ)| ≤ (34656233792003 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 178) 549 - (36570839 / 125000000 : ℝ))]

theorem thL_178_cos : (-36051373726503 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 178) ∧ Real.cos (16647931 / 100000 * Real.log 178) ≤ (-57682128649937 / 200000000000000 : ℝ) := by
  have hc := thL_178_cos_r
  have hs := thL_178_sin_r
  rw [thL_178_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_178_sin : (95750658957119 / 100000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 178) ∧ Real.sin (16647931 / 100000 * Real.log 178) ≤ (95750693613353 / 100000000000000 : ℝ) := by
  have hc := thL_178_cos_r
  have hs := thL_178_sin_r
  rw [thL_178_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_178 : (-36051373726503 / 125000000000000 : ℝ) ≤ cCG cZ 178 ∧ cCG cZ 178 ≤ (-57682128649937 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_178_cos

theorem sCB_178 : (95750658957119 / 100000000000000 : ℝ) ≤ sCG cZ 178 ∧ sCG cZ 178 ≤ (95750693613353 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_178_sin

theorem thL_179_r_bounds : (-1382280599559354317 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 ≤ (-1382279216440645683 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_179
  have hl : (431796204793651651 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 179 ∧ 16647931 / 100000 * Real.log 179 ≤ (107949051241614287 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_179_eq : (16647931 / 100000 * Real.log 179) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 + π) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_179_cos_r : (117610295316779 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) ≤ (235220677078479 / 250000000000000 : ℝ) := by
  have hr := thL_179_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(345569977 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) (-(345569977 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 - (-(345569977 / 1000000000 : ℝ))| ≤ (691559354317 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 - (-(345569977 / 1000000000 : ℝ)))]

theorem thL_179_sin_r : (-169366593268111 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) ≤ (-5292700636821 / 15625000000000 : ℝ) := by
  have hr := thL_179_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (345569977 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((301328217374673204786465460608168009757470612654566172213187909346978866776980426727594527634159675901006904856713918418163231 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(345569977 / 1000000000 : ℝ)) ∧ Real.sin (-(345569977 / 1000000000 : ℝ)) ≤ -((13521137959119945072267610624180442164385102908977630898034612772812531601103777126937027368249280723683927 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550) (-(345569977 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 - (-(345569977 / 1000000000 : ℝ))| ≤ (691559354317 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 179) 550 - (-(345569977 / 1000000000 : ℝ)))]

theorem thL_179_cos : (-235220677078479 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 179) ∧ Real.cos (16647931 / 100000 * Real.log 179) ≤ (-117610295316779 / 125000000000000 : ℝ) := by
  have hc := thL_179_cos_r
  have hs := thL_179_sin_r
  rw [thL_179_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_179_sin : (5292700636821 / 15625000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 179) ∧ Real.sin (16647931 / 100000 * Real.log 179) ≤ (169366593268111 / 500000000000000 : ℝ) := by
  have hc := thL_179_cos_r
  have hs := thL_179_sin_r
  rw [thL_179_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_179 : (-235220677078479 / 250000000000000 : ℝ) ≤ cCG cZ 179 ∧ cCG cZ 179 ≤ (-117610295316779 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_179_cos

theorem sCB_179 : (5292700636821 / 15625000000000 : ℝ) ≤ sCG cZ 179 ∧ sCG cZ 179 ≤ (169366593268111 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_179_sin

theorem thL_181_r_bounds : (-6657733494649380427 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 ≤ (-6657698905350619573 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_181
  have hl : (432721099364661769 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 181 ∧ 16647931 / 100000 * Real.log 181 ≤ (865442199074934531 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_181_eq : (16647931 / 100000 * Real.log 181) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 + π + π / 2) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_181_cos_r : (62361524144797 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) ≤ (49889236610487 / 50000000000000 : ℝ) := by
  have hr := thL_181_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(33288581 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) (-(33288581 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 - (-(33288581 / 500000000 : ℝ))| ≤ (17294649380427 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 - (-(33288581 / 500000000 : ℝ)))]

theorem thL_181_sin_r : (-13305632352421 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) ≤ (-66527815869117 / 1000000000000000 : ℝ) := by
  have hr := thL_181_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (33288581 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((50570211198361402260362821405008535849506595301394679129687922596631831736605560920399205241471996175110518557502708862741 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(33288581 / 500000000 : ℝ)) ∧ Real.sin (-(33288581 / 500000000 : ℝ)) ≤ -((1296672082009266724624686147907903882677538568227158382088968326174455732026087147437687319100577043619 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551) (-(33288581 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 - (-(33288581 / 500000000 : ℝ))| ≤ (17294649380427 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 181) 551 - (-(33288581 / 500000000 : ℝ)))]

theorem thL_181_cos : (-13305632352421 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 181) ∧ Real.cos (16647931 / 100000 * Real.log 181) ≤ (-66527815869117 / 1000000000000000 : ℝ) := by
  have hc := thL_181_cos_r
  have hs := thL_181_sin_r
  rw [thL_181_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_181_sin : (-49889236610487 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 181) ∧ Real.sin (16647931 / 100000 * Real.log 181) ≤ (-62361524144797 / 62500000000000 : ℝ) := by
  have hc := thL_181_cos_r
  have hs := thL_181_sin_r
  rw [thL_181_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_181 : (-13305632352421 / 200000000000000 : ℝ) ≤ cCG cZ 181 ∧ cCG cZ 181 ≤ (-66527815869117 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_181_cos

theorem sCB_181 : (-49889236610487 / 50000000000000 : ℝ) ≤ sCG cZ 181 ∧ sCG cZ 181 ≤ (-62361524144797 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_181_sin

theorem thL_182_r_bounds : (-9001624548741339813 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 ≤ (-9001620226258660187 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_182
  have hl : (54147465151691953 / 62500000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 182 ∧ 16647931 / 100000 * Real.log 182 ≤ (866359442772682241 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_182_eq : (16647931 / 100000 * Real.log 182) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_182_cos_r : (751719967673029 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) ≤ (3006881254049 / 4000000000000 : ℝ) := by
  have hr := thL_182_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(720129791 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) (-(720129791 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 - (-(720129791 / 1000000000 : ℝ))| ≤ (2161241339813 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 - (-(720129791 / 1000000000 : ℝ)))]

theorem thL_182_sin_r : (-164870604233501 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) ≤ (-659482071133139 / 1000000000000000 : ℝ) := by
  have hr := thL_182_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (720129791 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((586658521547818516184636695515291585116562902497597862123027779908527946245668401647569201145851881811711002374810239512590153 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(720129791 / 1000000000 : ℝ)) ∧ Real.sin (-(720129791 / 1000000000 : ℝ)) ≤ -((26324420838594376764083184746403277836633186092936552017588299352894078072367533376374858884121426449111809 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552) (-(720129791 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 - (-(720129791 / 1000000000 : ℝ))| ≤ (2161241339813 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 182) 552 - (-(720129791 / 1000000000 : ℝ)))]

theorem thL_182_cos : (751719967673029 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 182) ∧ Real.cos (16647931 / 100000 * Real.log 182) ≤ (3006881254049 / 4000000000000 : ℝ) := by
  have hc := thL_182_cos_r
  have hs := thL_182_sin_r
  rw [thL_182_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_182_sin : (-164870604233501 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 182) ∧ Real.sin (16647931 / 100000 * Real.log 182) ≤ (-659482071133139 / 1000000000000000 : ℝ) := by
  have hc := thL_182_cos_r
  have hs := thL_182_sin_r
  rw [thL_182_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_182 : (751719967673029 / 1000000000000000 : ℝ) ≤ cCG cZ 182 ∧ cCG cZ 182 ≤ (3006881254049 / 4000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_182_cos

theorem sCB_182 : (-164870604233501 / 250000000000000 : ℝ) ≤ sCG cZ 182 ∧ sCG cZ 182 ≤ (-659482071133139 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_182_sin

theorem thL_183_r_bounds : (4802192898795104557 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 ≤ (4802201551204895443 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_183
  have hl : (433635830053367369 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 183 ∧ 16647931 / 100000 * Real.log 183 ≤ (216817915113086433 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_183_eq : (16647931 / 100000 * Real.log 183) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_183_cos_r : (490803802765511 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) ≤ (196321590325483 / 200000000000000 : ℝ) := by
  have hr := thL_183_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (192087889 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) (192087889 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 - (192087889 / 1000000000 : ℝ)| ≤ (4326204895443 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 - (192087889 / 1000000000 : ℝ))]

theorem thL_183_sin_r : (47727156158703 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) ≤ (47727242682801 / 250000000000000 : ℝ) := by
  have hr := thL_183_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (192087889 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552) (192087889 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 - (192087889 / 1000000000 : ℝ)| ≤ (4326204895443 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 183) 552 - (192087889 / 1000000000 : ℝ))]

theorem thL_183_cos : (490803802765511 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 183) ∧ Real.cos (16647931 / 100000 * Real.log 183) ≤ (196321590325483 / 200000000000000 : ℝ) := by
  have hc := thL_183_cos_r
  have hs := thL_183_sin_r
  rw [thL_183_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_183_sin : (47727156158703 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 183) ∧ Real.sin (16647931 / 100000 * Real.log 183) ≤ (47727242682801 / 250000000000000 : ℝ) := by
  have hc := thL_183_cos_r
  have hs := thL_183_sin_r
  rw [thL_183_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_183 : (490803802765511 / 500000000000000 : ℝ) ≤ cCG cZ 183 ∧ cCG cZ 183 ≤ (196321590325483 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_183_cos

theorem sCB_183 : (47727156158703 / 250000000000000 : ℝ) ≤ sCG cZ 183 ∧ sCG cZ 183 ≤ (47727242682801 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_183_sin

theorem thL_184_r_bounds : (-47146217024477956581 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 ≤ (-47146182375522043419 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_184
  have hl : (868178906548211617 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 184 ∧ 16647931 / 100000 * Real.log 184 ≤ (86817890689382261 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_184_eq : (16647931 / 100000 * Real.log 184) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 + π / 2) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_184_cos_r : (890905043961041 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) ≤ (890905390450853 / 1000000000000000 : ℝ) := by
  have hr := thL_184_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(471461997 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) (-(471461997 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 - (-(471461997 / 1000000000 : ℝ))| ≤ (17324477956581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 - (-(471461997 / 1000000000 : ℝ)))]

theorem thL_184_sin_r : (-227094722157337 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) ≤ (-90837819565021 / 200000000000000 : ℝ) := by
  have hr := thL_184_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (471461997 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((11638872584728669736289150183673645017066394271675499156855118235583701480093109016720204844553279264782090800354447408115439 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(471461997 / 1000000000 : ℝ)) ∧ Real.sin (-(471461997 / 1000000000 : ℝ)) ≤ -((223824472783239148931688089227200325596388927160700941511925693041208722546293738566547170569638406224187 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553) (-(471461997 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 - (-(471461997 / 1000000000 : ℝ))| ≤ (17324477956581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 184) 553 - (-(471461997 / 1000000000 : ℝ)))]

theorem thL_184_cos : (90837819565021 / 200000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 184) ∧ Real.cos (16647931 / 100000 * Real.log 184) ≤ (227094722157337 / 500000000000000 : ℝ) := by
  have hc := thL_184_cos_r
  have hs := thL_184_sin_r
  rw [thL_184_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_184_sin : (890905043961041 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 184) ∧ Real.sin (16647931 / 100000 * Real.log 184) ≤ (890905390450853 / 1000000000000000 : ℝ) := by
  have hc := thL_184_cos_r
  have hs := thL_184_sin_r
  rw [thL_184_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_184 : (90837819565021 / 200000000000000 : ℝ) ≤ cCG cZ 184 ∧ cCG cZ 184 ≤ (227094722157337 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_184_cos

theorem sCB_184 : (890905043961041 / 1000000000000000 : ℝ) ≤ sCG cZ 184 ∧ sCG cZ 184 ≤ (890905390450853 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_184_sin

theorem thL_186_r_bounds : (-12123232147379397329 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 ≤ (-12123214852620602671 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_186
  have hl : (434989350200854661 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 186 ∧ 16647931 / 100000 * Real.log 186 ≤ (173995740149464063 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_186_eq : (16647931 / 100000 * Real.log 186) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 + π) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_186_cos_r : (485374520871003 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) ≤ (970749387637183 / 1000000000000000 : ℝ) := by
  have hr := thL_186_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(24246447 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) (-(24246447 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 - (-(24246447 / 100000000 : ℝ))| ≤ (8647379397329 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 - (-(24246447 / 100000000 : ℝ)))]

theorem thL_186_sin_r : (-240095908393963 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) ≤ (-120047781249393 / 500000000000000 : ℝ) := by
  have hr := thL_186_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (24246447 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((87894246832208684820018051355937389728746688647561703884330989988106060697552497797936109714855309662300922627 / 366080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(24246447 / 100000000 : ℝ)) ∧ Real.sin (-(24246447 / 100000000 : ℝ)) ≤ -((1183191784279732287732436799338692162654023093607442541666210659517088432553729556690877007137 / 4928000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554) (-(24246447 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 - (-(24246447 / 100000000 : ℝ))| ≤ (8647379397329 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 186) 554 - (-(24246447 / 100000000 : ℝ)))]

theorem thL_186_cos : (-970749387637183 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 186) ∧ Real.cos (16647931 / 100000 * Real.log 186) ≤ (-485374520871003 / 500000000000000 : ℝ) := by
  have hc := thL_186_cos_r
  have hs := thL_186_sin_r
  rw [thL_186_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_186_sin : (120047781249393 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 186) ∧ Real.sin (16647931 / 100000 * Real.log 186) ≤ (240095908393963 / 1000000000000000 : ℝ) := by
  have hc := thL_186_cos_r
  have hs := thL_186_sin_r
  rw [thL_186_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_186 : (-970749387637183 / 1000000000000000 : ℝ) ≤ cCG cZ 186 ∧ cCG cZ 186 ≤ (-485374520871003 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_186_cos

theorem sCB_186 : (120047781249393 / 500000000000000 : ℝ) ≤ sCG cZ 186 ∧ sCG cZ 186 ≤ (240095908393963 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_186_sin

theorem thL_187_r_bounds : (65018795177366494381 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 ≤ (65018829822633505619 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_187
  have hl : (108858919124518299 / 125000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 187 ∧ 16647931 / 100000 * Real.log 187 ≤ (435435676670878693 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_187_eq : (16647931 / 100000 * Real.log 187) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 + π) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_187_cos_r : (795969760531817 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) ≤ (198992526749101 / 250000000000000 : ℝ) := by
  have hr := thL_187_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1040301 / 1600000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) (1040301 / 1600000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 - (1040301 / 1600000 : ℝ)| ≤ (17322633505619 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 - (1040301 / 1600000 : ℝ))]

theorem thL_187_sin_r : (605335985063747 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) ≤ (302668165758507 / 500000000000000 : ℝ) := by
  have hr := thL_187_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1040301 / 1600000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554) (1040301 / 1600000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 - (1040301 / 1600000 : ℝ)| ≤ (17322633505619 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 187) 554 - (1040301 / 1600000 : ℝ))]

theorem thL_187_cos : (-198992526749101 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 187) ∧ Real.cos (16647931 / 100000 * Real.log 187) ≤ (-795969760531817 / 1000000000000000 : ℝ) := by
  have hc := thL_187_cos_r
  have hs := thL_187_sin_r
  rw [thL_187_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_187_sin : (-302668165758507 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 187) ∧ Real.sin (16647931 / 100000 * Real.log 187) ≤ (-605335985063747 / 1000000000000000 : ℝ) := by
  have hc := thL_187_cos_r
  have hs := thL_187_sin_r
  rw [thL_187_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_187 : (-198992526749101 / 250000000000000 : ℝ) ≤ cCG cZ 187 ∧ cCG cZ 187 ≤ (-795969760531817 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_187_cos

theorem sCB_187 : (-302668165758507 / 500000000000000 : ℝ) ≤ sCG cZ 187 ∧ sCG cZ 187 ≤ (-605335985063747 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_187_sin

theorem thL_188_r_bounds : (-1308664682063667017 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 ≤ (-1308650837936332983 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_188
  have hl : (13621238199283063 / 15625000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 188 ∧ 16647931 / 100000 * Real.log 188 ≤ (34870369803989081 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_188_eq : (16647931 / 100000 * Real.log 188) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 + π + π / 2) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_188_cos_r : (999464691829483 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) ≤ (249866259483167 / 250000000000000 : ℝ) := by
  have hr := thL_188_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(8179111 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) (-(8179111 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 - (-(8179111 / 250000000 : ℝ))| ≤ (6922063667017 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 - (-(8179111 / 250000000 : ℝ)))]

theorem thL_188_sin_r : (-8177695234329 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) ≤ (-32710434834131 / 1000000000000000 : ℝ) := by
  have hr := thL_188_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (8179111 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3035212094858933453771846971230400851515032192978136254447849673432820706997795153268941215789538959958829695232628231 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(8179111 / 250000000 : ℝ)) ∧ Real.sin (-(8179111 / 250000000 : ℝ)) ≤ -((311303804600916251668907381589463965173521306853821978691666713197949596474334496816732630664849289 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555) (-(8179111 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 - (-(8179111 / 250000000 : ℝ))| ≤ (6922063667017 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 188) 555 - (-(8179111 / 250000000 : ℝ)))]

theorem thL_188_cos : (-8177695234329 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 188) ∧ Real.cos (16647931 / 100000 * Real.log 188) ≤ (-32710434834131 / 1000000000000000 : ℝ) := by
  have hc := thL_188_cos_r
  have hs := thL_188_sin_r
  rw [thL_188_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_188_sin : (-249866259483167 / 250000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 188) ∧ Real.sin (16647931 / 100000 * Real.log 188) ≤ (-999464691829483 / 1000000000000000 : ℝ) := by
  have hc := thL_188_cos_r
  have hs := thL_188_sin_r
  rw [thL_188_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_188 : (-8177695234329 / 250000000000000 : ℝ) ≤ cCG cZ 188 ∧ cCG cZ 188 ≤ (-32710434834131 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_188_cos

theorem sCB_188 : (-249866259483167 / 250000000000000 : ℝ) ≤ sCG cZ 188 ∧ sCG cZ 188 ≤ (-999464691829483 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_188_sin

theorem thL_189_r_bounds : (-36016575456660364733 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 ≤ (-36016558143339635267 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_189
  have hl : (872642426188829313 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 189 ∧ 16647931 / 100000 * Real.log 189 ≤ (436321213267220153 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_189_eq : (16647931 / 100000 * Real.log 189) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_189_cos_r : (751587036823437 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) ≤ (150317476626119 / 200000000000000 : ℝ) := by
  have hr := thL_189_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(90041417 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) (-(90041417 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 - (-(90041417 / 125000000 : ℝ))| ≤ (8656660364733 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 - (-(90041417 / 125000000 : ℝ)))]

theorem thL_189_sin_r : (-329816954604203 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) ≤ (-659633562939733 / 1000000000000000 : ℝ) := by
  have hr := thL_189_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (90041417 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1067370767466587536623049682232484359739520832574696491786813428566414635466679268307677606829855804738140499616591 / 1618126407265663146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(90041417 / 125000000 : ℝ)) ∧ Real.sin (-(90041417 / 125000000 : ℝ)) ≤ -((3065269896303811943179822714804095587718827861570874734739089137958791042293738465000818272617767 / 4646927118301391601562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556) (-(90041417 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 - (-(90041417 / 125000000 : ℝ))| ≤ (8656660364733 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 189) 556 - (-(90041417 / 125000000 : ℝ)))]

theorem thL_189_cos : (751587036823437 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 189) ∧ Real.cos (16647931 / 100000 * Real.log 189) ≤ (150317476626119 / 200000000000000 : ℝ) := by
  have hc := thL_189_cos_r
  have hs := thL_189_sin_r
  rw [thL_189_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_189_sin : (-329816954604203 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 189) ∧ Real.sin (16647931 / 100000 * Real.log 189) ≤ (-659633562939733 / 1000000000000000 : ℝ) := by
  have hc := thL_189_cos_r
  have hs := thL_189_sin_r
  rw [thL_189_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_189 : (751587036823437 / 1000000000000000 : ℝ) ≤ cCG cZ 189 ∧ cCG cZ 189 ≤ (150317476626119 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_189_cos

theorem sCB_189 : (-329816954604203 / 500000000000000 : ℝ) ≤ sCG cZ 189 ∧ sCG cZ 189 ≤ (-659633562939733 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_189_sin

theorem thL_191_r_bounds : (-107739573015877382779 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 ≤ (-107739503784122617221 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_191
  have hl : (87439485615967803 / 100000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 191 ∧ 16647931 / 100000 * Real.log 191 ≤ (874394856505289023 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_191_eq : (16647931 / 100000 * Real.log 191) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_191_cos_r : (858377344169459 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) ≤ (858377690329481 / 1000000000000000 : ℝ) := by
  have hr := thL_191_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(134674423 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) (-(134674423 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 - (-(134674423 / 250000000 : ℝ))| ≤ (34615877382779 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 - (-(134674423 / 250000000 : ℝ)))]

theorem thL_191_sin_r : (-513018728181997 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) ≤ (-51301838202317 / 100000000000000 : ℝ) := by
  have hr := thL_191_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (134674423 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3661762307939500061513743432391657970406901352956424799752761802234338003089854294357476826655353079595041197593299891 / 7137680053710937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(134674423 / 250000000 : ℝ)) ∧ Real.sin (-(134674423 / 250000000 : ℝ)) ≤ -((4882349743918841713334251322891626135174761682555526585149037084114497858740142813118748034179944473 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557) (-(134674423 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 - (-(134674423 / 250000000 : ℝ))| ≤ (34615877382779 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 191) 557 - (-(134674423 / 250000000 : ℝ)))]

theorem thL_191_cos : (51301838202317 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 191) ∧ Real.cos (16647931 / 100000 * Real.log 191) ≤ (513018728181997 / 1000000000000000 : ℝ) := by
  have hc := thL_191_cos_r
  have hs := thL_191_sin_r
  rw [thL_191_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_191_sin : (858377344169459 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 191) ∧ Real.sin (16647931 / 100000 * Real.log 191) ≤ (858377690329481 / 1000000000000000 : ℝ) := by
  have hc := thL_191_cos_r
  have hs := thL_191_sin_r
  rw [thL_191_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_191 : (51301838202317 / 100000000000000 : ℝ) ≤ cCG cZ 191 ∧ cCG cZ 191 ≤ (513018728181997 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_191_cos

theorem sCB_191 : (858377344169459 / 1000000000000000 : ℝ) ≤ sCG cZ 191 ∧ sCG cZ 191 ≤ (858377690329481 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_191_sin

theorem thL_192_r_bounds : (66129553152279417221 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 ≤ (66129622447720582779 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_192
  have hl : (437632100895259407 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 192 ∧ 16647931 / 100000 * Real.log 192 ≤ (875264202136129807 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_192_eq : (16647931 / 100000 * Real.log 192) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_192_cos_r : (472916005801307 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) ≤ (37833294323193 / 40000000000000 : ℝ) := by
  have hr := thL_192_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (330647939 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) (330647939 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 - (330647939 / 1000000000 : ℝ)| ≤ (34647720582779 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 - (330647939 / 1000000000 : ℝ))]

theorem thL_192_sin_r : (162327882411363 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) ≤ (324656111299933 / 1000000000000000 : ℝ) := by
  have hr := thL_192_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (330647939 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557) (330647939 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 - (330647939 / 1000000000 : ℝ)| ≤ (34647720582779 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 192) 557 - (330647939 / 1000000000 : ℝ))]

theorem thL_192_cos : (-324656111299933 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 192) ∧ Real.cos (16647931 / 100000 * Real.log 192) ≤ (-162327882411363 / 500000000000000 : ℝ) := by
  have hc := thL_192_cos_r
  have hs := thL_192_sin_r
  rw [thL_192_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_192_sin : (472916005801307 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 192) ∧ Real.sin (16647931 / 100000 * Real.log 192) ≤ (37833294323193 / 40000000000000 : ℝ) := by
  have hc := thL_192_cos_r
  have hs := thL_192_sin_r
  rw [thL_192_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_192 : (-324656111299933 / 1000000000000000 : ℝ) ≤ cCG cZ 192 ∧ cCG cZ 192 ≤ (-162327882411363 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_192_cos

theorem sCB_192 : (472916005801307 / 500000000000000 : ℝ) ≤ sCG cZ 192 ∧ sCG cZ 192 ≤ (37833294323193 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_192_sin

theorem thL_193_r_bounds : (-18765951592706123483 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 ≤ (-18765934307293876517 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_193
  have hl : (876129031319795443 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 193 ∧ 16647931 / 100000 * Real.log 193 ≤ (219032257916351609 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_193_eq : (16647931 / 100000 * Real.log 193) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 + π) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_193_cos_r : (465195306232477 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) ≤ (29074717442913 / 31250000000000 : ℝ) := by
  have hr := thL_193_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(375318859 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) (-(375318859 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 - (-(375318859 / 1000000000 : ℝ))| ≤ (8642706123483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 - (-(375318859 / 1000000000 : ℝ)))]

theorem thL_193_sin_r : (-3665693840453 / 10000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) ≤ (-366569038337053 / 1000000000000000 : ℝ) := by
  have hr := thL_193_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (375318859 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2282634102727051499088396016069614899101999430731093074649999270914969227158065570631916246900293809446239915352633003661792379 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(375318859 / 1000000000 : ℝ)) ∧ Real.sin (-(375318859 / 1000000000 : ℝ)) ≤ -((14632269889275952351353291513720857961300519975257899122932846234485962383915605112208023953638446583330541 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558) (-(375318859 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 - (-(375318859 / 1000000000 : ℝ))| ≤ (8642706123483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 193) 558 - (-(375318859 / 1000000000 : ℝ)))]

theorem thL_193_cos : (-29074717442913 / 31250000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 193) ∧ Real.cos (16647931 / 100000 * Real.log 193) ≤ (-465195306232477 / 500000000000000 : ℝ) := by
  have hc := thL_193_cos_r
  have hs := thL_193_sin_r
  rw [thL_193_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_193_sin : (366569038337053 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 193) ∧ Real.sin (16647931 / 100000 * Real.log 193) ≤ (3665693840453 / 10000000000000 : ℝ) := by
  have hc := thL_193_cos_r
  have hs := thL_193_sin_r
  rw [thL_193_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_193 : (-29074717442913 / 31250000000000 : ℝ) ≤ cCG cZ 193 ∧ cCG cZ 193 ≤ (-465195306232477 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_193_cos

theorem sCB_193 : (366569038337053 / 1000000000000000 : ℝ) ≤ sCG cZ 193 ∧ sCG cZ 193 ≤ (3665693840453 / 10000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_193_sin

theorem thL_194_r_bounds : (24252053703388276517 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 ≤ (24252070996611723483 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_194
  have hl : (438494695712936777 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 194 ∧ 16647931 / 100000 * Real.log 194 ≤ (219247347942871137 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_194_eq : (16647931 / 100000 * Real.log 194) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 + π) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_194_cos_r : (221163886431797 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) ≤ (221163972898003 / 250000000000000 : ℝ) := by
  have hr := thL_194_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (485041247 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) (485041247 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 - (485041247 / 1000000000 : ℝ)| ≤ (8646611723483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 - (485041247 / 1000000000 : ℝ))]

theorem thL_194_sin_r : (910634133413 / 1953125000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) ≤ (23312251108597 / 50000000000000 : ℝ) := by
  have hr := thL_194_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (485041247 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558) (485041247 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 - (485041247 / 1000000000 : ℝ)| ≤ (8646611723483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 194) 558 - (485041247 / 1000000000 : ℝ))]

theorem thL_194_cos : (-221163972898003 / 250000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 194) ∧ Real.cos (16647931 / 100000 * Real.log 194) ≤ (-221163886431797 / 250000000000000 : ℝ) := by
  have hc := thL_194_cos_r
  have hs := thL_194_sin_r
  rw [thL_194_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_194_sin : (-23312251108597 / 50000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 194) ∧ Real.sin (16647931 / 100000 * Real.log 194) ≤ (-910634133413 / 1953125000000 : ℝ) := by
  have hc := thL_194_cos_r
  have hs := thL_194_sin_r
  rw [thL_194_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_194 : (-221163972898003 / 250000000000000 : ℝ) ≤ cCG cZ 194 ∧ cCG cZ 194 ≤ (-221163886431797 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_194_cos

theorem sCB_194 : (-23312251108597 / 50000000000000 : ℝ) ≤ sCG cZ 194 ∧ sCG cZ 194 ≤ (-910634133413 / 1953125000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_194_sin

theorem thL_196_r_bounds : (62173981801413714957 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 ≤ (62174016398586285043 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_196
  have hl : (5491855540604513 / 6250000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 196 ∧ 16647931 / 100000 * Real.log 196 ≤ (878696886842333073 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_196_eq : (16647931 / 100000 * Real.log 196) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 + π + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_196_cos_r : (812866056193693 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) ≤ (162573280434477 / 200000000000000 : ℝ) := by
  have hr := thL_196_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (621739991 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) (621739991 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 - (621739991 / 1000000000 : ℝ)| ≤ (17298586285043 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 - (621739991 / 1000000000 : ℝ))]

theorem thL_196_sin_r : (582450248464513 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) ≤ (582450594436573 / 1000000000000000 : ℝ) := by
  have hr := thL_196_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (621739991 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559) (621739991 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 - (621739991 / 1000000000 : ℝ)| ≤ (17298586285043 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 196) 559 - (621739991 / 1000000000 : ℝ))]

theorem thL_196_cos : (582450248464513 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 196) ∧ Real.cos (16647931 / 100000 * Real.log 196) ≤ (582450594436573 / 1000000000000000 : ℝ) := by
  have hc := thL_196_cos_r
  have hs := thL_196_sin_r
  rw [thL_196_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_196_sin : (-162573280434477 / 200000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 196) ∧ Real.sin (16647931 / 100000 * Real.log 196) ≤ (-812866056193693 / 1000000000000000 : ℝ) := by
  have hc := thL_196_cos_r
  have hs := thL_196_sin_r
  rw [thL_196_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_196 : (582450248464513 / 1000000000000000 : ℝ) ≤ cCG cZ 196 ∧ cCG cZ 196 ≤ (582450594436573 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_196_cos

theorem sCB_196 : (-162573280434477 / 200000000000000 : ℝ) ≤ sCG cZ 196 ∧ sCG cZ 196 ≤ (-812866056193693 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_196_sin

theorem thL_197_r_bounds : (-254579320685421929 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 ≤ (-254578454314578071 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_197
  have hl : (439772055638433969 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 197 ∧ 16647931 / 100000 * Real.log 197 ≤ (879544111622478931 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_197_eq : (16647931 / 100000 * Real.log 197) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_197_cos_r : (994819472795767 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) ≤ (198963963868821 / 200000000000000 : ℝ) := by
  have hr := thL_197_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(20366311 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) (-(20366311 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 - (-(20366311 / 200000000 : ℝ))| ≤ (433185421929 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 - (-(20366311 / 200000000 : ℝ)))]

theorem thL_197_sin_r : (-101655826305799 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) ≤ (-101655479757461 / 1000000000000000 : ℝ) := by
  have hr := thL_197_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (20366311 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((74080474359579067802941181032446581355098492598794419614024301654515164732727292026862971128667219312526864007984833 / 728739348480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(20366311 / 200000000 : ℝ)) ∧ Real.sin (-(20366311 / 200000000 : ℝ)) ≤ -((11871870890958183942776660888934247965306157388647230107140667108034816238174142736338673374295727 / 116785152000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560) (-(20366311 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 - (-(20366311 / 200000000 : ℝ))| ≤ (433185421929 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 197) 560 - (-(20366311 / 200000000 : ℝ)))]

theorem thL_197_cos : (994819472795767 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 197) ∧ Real.cos (16647931 / 100000 * Real.log 197) ≤ (198963963868821 / 200000000000000 : ℝ) := by
  have hc := thL_197_cos_r
  have hs := thL_197_sin_r
  rw [thL_197_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_197_sin : (-101655826305799 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 197) ∧ Real.sin (16647931 / 100000 * Real.log 197) ≤ (-101655479757461 / 1000000000000000 : ℝ) := by
  have hc := thL_197_cos_r
  have hs := thL_197_sin_r
  rw [thL_197_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_197 : (994819472795767 / 1000000000000000 : ℝ) ≤ cCG cZ 197 ∧ cCG cZ 197 ≤ (198963963868821 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_197_cos

theorem sCB_197 : (-101655826305799 / 1000000000000000 : ℝ) ≤ sCG cZ 197 ∧ sCG cZ 197 ≤ (-101655479757461 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_197_sin

theorem thL_198_r_bounds : (1852758219433453071 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 ≤ (1852759085566546929 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_198
  have hl : (27512095196653609 / 31250000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 198 ∧ 16647931 / 100000 * Real.log 198 ≤ (880387046638526481 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_198_eq : (16647931 / 100000 * Real.log 198) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_198_cos_r : (368861942797149 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) ≤ (184431058026211 / 250000000000000 : ℝ) := by
  have hr := thL_198_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (741103461 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) (741103461 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 - (741103461 / 1000000000 : ℝ)| ≤ (433066546929 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 - (741103461 / 1000000000 : ℝ))]

theorem thL_198_sin_r : (675102198971919 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) ≤ (84387818178553 / 125000000000000 : ℝ) := by
  have hr := thL_198_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (741103461 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560) (741103461 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 - (741103461 / 1000000000 : ℝ)| ≤ (433066546929 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 198) 560 - (741103461 / 1000000000 : ℝ))]

theorem thL_198_cos : (368861942797149 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 198) ∧ Real.cos (16647931 / 100000 * Real.log 198) ≤ (184431058026211 / 250000000000000 : ℝ) := by
  have hc := thL_198_cos_r
  have hs := thL_198_sin_r
  rw [thL_198_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_198_sin : (675102198971919 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 198) ∧ Real.sin (16647931 / 100000 * Real.log 198) ≤ (84387818178553 / 125000000000000 : ℝ) := by
  have hc := thL_198_cos_r
  have hs := thL_198_sin_r
  rw [thL_198_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_198 : (368861942797149 / 500000000000000 : ℝ) ≤ cCG cZ 198 ∧ cCG cZ 198 ≤ (184431058026211 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_198_cos

theorem sCB_198 : (675102198971919 / 1000000000000000 : ℝ) ≤ sCG cZ 198 ∧ sCG cZ 198 ≤ (84387818178553 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_198_sin

theorem thL_199_r_bounds : (1799087001574321833 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 ≤ (1799156198425678167 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_199
  have hl : (7049805878135559 / 8000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 199 ∧ 16647931 / 100000 * Real.log 199 ≤ (220306433778138967 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_199_eq : (16647931 / 100000 * Real.log 199) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_199_cos_r : (999959366799067 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) ≤ (39998388511333 / 40000000000000 : ℝ) := by
  have hr := thL_199_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1124451 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) (1124451 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 - (1124451 / 125000000 : ℝ)| ≤ (34598425678167 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 - (1124451 / 125000000 : ℝ))]

theorem thL_199_sin_r : (8995313686151 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) ≤ (8995659670409 / 1000000000000000 : ℝ) := by
  have hr := thL_199_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1124451 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561) (1124451 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 - (1124451 / 125000000 : ℝ)| ≤ (34598425678167 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 199) 561 - (1124451 / 125000000 : ℝ))]

theorem thL_199_cos : (-8995659670409 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 199) ∧ Real.cos (16647931 / 100000 * Real.log 199) ≤ (-8995313686151 / 1000000000000000 : ℝ) := by
  have hc := thL_199_cos_r
  have hs := thL_199_sin_r
  rw [thL_199_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_199_sin : (999959366799067 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 199) ∧ Real.sin (16647931 / 100000 * Real.log 199) ≤ (39998388511333 / 40000000000000 : ℝ) := by
  have hc := thL_199_cos_r
  have hs := thL_199_sin_r
  rw [thL_199_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_199 : (-8995659670409 / 1000000000000000 : ℝ) ≤ cCG cZ 199 ∧ cCG cZ 199 ≤ (-8995313686151 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_199_cos

theorem sCB_199 : (999959366799067 / 1000000000000000 : ℝ) ≤ sCG cZ 199 ∧ sCG cZ 199 ≤ (39998388511333 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_199_sin

theorem thL_201_r_bounds : (10300608169691098993 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 ≤ (10300642830308901007 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_201
  have hl : (882890541740428811 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 201 ∧ 16647931 / 100000 * Real.log 201 ≤ (220722635521509951 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_201_eq : (16647931 / 100000 * Real.log 201) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 + π) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_201_cos_r : (198939874302593 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) ≤ (124337464764893 / 125000000000000 : ℝ) := by
  have hr := thL_201_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (20601251 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) (20601251 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 - (20601251 / 200000000 : ℝ)| ≤ (17330308901007 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 - (20601251 / 200000000 : ℝ))]

theorem thL_201_sin_r : (51412011979841 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) ≤ (102824370565861 / 1000000000000000 : ℝ) := by
  have hr := thL_201_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (20601251 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562) (20601251 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 - (20601251 / 200000000 : ℝ)| ≤ (17330308901007 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 201) 562 - (20601251 / 200000000 : ℝ))]

theorem thL_201_cos : (-124337464764893 / 125000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 201) ∧ Real.cos (16647931 / 100000 * Real.log 201) ≤ (-198939874302593 / 200000000000000 : ℝ) := by
  have hc := thL_201_cos_r
  have hs := thL_201_sin_r
  rw [thL_201_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_201_sin : (-102824370565861 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 201) ∧ Real.sin (16647931 / 100000 * Real.log 201) ≤ (-51412011979841 / 500000000000000 : ℝ) := by
  have hc := thL_201_cos_r
  have hs := thL_201_sin_r
  rw [thL_201_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_201 : (-124337464764893 / 125000000000000 : ℝ) ≤ cCG cZ 201 ∧ cCG cZ 201 ≤ (-198939874302593 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_201_cos

theorem sCB_201 : (-102824370565861 / 1000000000000000 : ℝ) ≤ sCG cZ 201 ∧ sCG cZ 201 ≤ (-51412011979841 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_201_sin

theorem thL_202_r_bounds : (-64158849986599937351 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 ≤ (-64158815413400062649 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_202
  have hl : (883716743485781803 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 202 ∧ 16647931 / 100000 * Real.log 202 ≤ (220929185957848199 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_202_eq : (16647931 / 100000 * Real.log 202) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 + π + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_202_cos_r : (200286508001693 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) ≤ (12517912152327 / 15625000000000 : ℝ) := by
  have hr := thL_202_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(641588327 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) (-(641588327 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 - (-(641588327 / 1000000000 : ℝ))| ≤ (17286599937351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 - (-(641588327 / 1000000000 : ℝ)))]

theorem thL_202_sin_r : (-299234425372283 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) ≤ (-119693701002413 / 200000000000000 : ℝ) := by
  have hr := thL_202_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (641588327 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3726676905298330535990585373513229351019159176428927872592637913876412325325229689800567389068854274135069193064004050038132167 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(641588327 / 1000000000 : ℝ)) ∧ Real.sin (-(641588327 / 1000000000 : ℝ)) ≤ -((23888954521123136202435282743394769692158324657459829270090374012636676045540659344479753238979379503720777 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563) (-(641588327 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 - (-(641588327 / 1000000000 : ℝ))| ≤ (17286599937351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 202) 563 - (-(641588327 / 1000000000 : ℝ)))]

theorem thL_202_cos : (-299234425372283 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 202) ∧ Real.cos (16647931 / 100000 * Real.log 202) ≤ (-119693701002413 / 200000000000000 : ℝ) := by
  have hc := thL_202_cos_r
  have hs := thL_202_sin_r
  rw [thL_202_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_202_sin : (-12517912152327 / 15625000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 202) ∧ Real.sin (16647931 / 100000 * Real.log 202) ≤ (-200286508001693 / 250000000000000 : ℝ) := by
  have hc := thL_202_cos_r
  have hs := thL_202_sin_r
  rw [thL_202_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_202 : (-299234425372283 / 500000000000000 : ℝ) ≤ cCG cZ 202 ∧ cCG cZ 202 ≤ (-119693701002413 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_202_cos

theorem sCB_202 : (-12517912152327 / 15625000000000 : ℝ) ≤ sCG cZ 202 ∧ sCG cZ 202 ≤ (-200286508001693 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_202_sin

theorem thL_203_r_bounds : (18053322002414662649 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 ≤ (18053356597585337351 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_203
  have hl : (884538865205891657 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 203 ∧ 16647931 / 100000 * Real.log 203 ≤ (17690777311030053 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_203_eq : (16647931 / 100000 * Real.log 203) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 + π + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_203_cos_r : (491873943369897 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) ≤ (491874116345751 / 500000000000000 : ℝ) := by
  have hr := thL_203_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (180533393 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) (180533393 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 - (180533393 / 1000000000 : ℝ)| ≤ (17297585337351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 - (180533393 / 1000000000 : ℝ))]

theorem thL_203_sin_r : (179554150296233 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) ≤ (179554496247941 / 1000000000000000 : ℝ) := by
  have hr := thL_203_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (180533393 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563) (180533393 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 - (180533393 / 1000000000 : ℝ)| ≤ (17297585337351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 203) 563 - (180533393 / 1000000000 : ℝ))]

theorem thL_203_cos : (179554150296233 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 203) ∧ Real.cos (16647931 / 100000 * Real.log 203) ≤ (179554496247941 / 1000000000000000 : ℝ) := by
  have hc := thL_203_cos_r
  have hs := thL_203_sin_r
  rw [thL_203_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_203_sin : (-491874116345751 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 203) ∧ Real.sin (16647931 / 100000 * Real.log 203) ≤ (-491873943369897 / 500000000000000 : ℝ) := by
  have hc := thL_203_cos_r
  have hs := thL_203_sin_r
  rw [thL_203_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_203 : (179554150296233 / 1000000000000000 : ℝ) ≤ cCG cZ 203 ∧ cCG cZ 203 ≤ (179554496247941 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_203_cos

theorem sCB_203 : (-491874116345751 / 500000000000000 : ℝ) ≤ sCG cZ 203 ∧ sCG cZ 203 ≤ (-491873943369897 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_203_sin

theorem thL_204_r_bounds : (-14304532820478318857 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 ≤ (-14304524179521681143 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_204
  have hl : (885356946999529833 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 204 ∧ 16647931 / 100000 * Real.log 204 ≤ (442678473672570413 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_204_eq : (16647931 / 100000 * Real.log 204) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_204_cos_r : (840721787609899 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) ≤ (52545133328171 / 62500000000000 : ℝ) := by
  have hr := thL_204_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(28609057 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) (-(28609057 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 - (-(28609057 / 50000000 : ℝ))| ≤ (4320478318857 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 - (-(28609057 / 50000000 : ℝ)))]

theorem thL_204_sin_r : (-270733620187731 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) ≤ (-541466894737083 / 1000000000000000 : ℝ) := by
  have hr := thL_204_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (28609057 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((41158773098001289359400744295762528671564104946394876599046667842212807159063384309082734554276776682562993057 / 76013437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(28609057 / 50000000 : ℝ)) ∧ Real.sin (-(28609057 / 50000000 : ℝ)) ≤ -((105535315635878688247712944224541382774685001817819638667870056472443248150142370130853147807 / 194906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564) (-(28609057 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 - (-(28609057 / 50000000 : ℝ))| ≤ (4320478318857 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 204) 564 - (-(28609057 / 50000000 : ℝ)))]

theorem thL_204_cos : (840721787609899 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 204) ∧ Real.cos (16647931 / 100000 * Real.log 204) ≤ (52545133328171 / 62500000000000 : ℝ) := by
  have hc := thL_204_cos_r
  have hs := thL_204_sin_r
  rw [thL_204_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_204_sin : (-270733620187731 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 204) ∧ Real.sin (16647931 / 100000 * Real.log 204) ≤ (-541466894737083 / 1000000000000000 : ℝ) := by
  have hc := thL_204_cos_r
  have hs := thL_204_sin_r
  rw [thL_204_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_204 : (840721787609899 / 1000000000000000 : ℝ) ≤ cCG cZ 204 ∧ cCG cZ 204 ≤ (52545133328171 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_204_cos

theorem sCB_204 : (-270733620187731 / 500000000000000 : ℝ) ≤ sCG cZ 204 ∧ sCG cZ 204 ≤ (-541466894737083 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_204_sin

theorem thL_206_r_bounds : (-10375527343356742701 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 ≤ (-10375520416643257299 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_206
  have hl : (443490574136336717 / 500000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 206 ∧ 16647931 / 100000 * Real.log 206 ≤ (886981148618284427 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_206_eq : (16647931 / 100000 * Real.log 206) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 + π / 2) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_206_cos_r : (434213220692203 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) ≤ (434213393860437 / 500000000000000 : ℝ) := by
  have hr := thL_206_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(259388097 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) (-(259388097 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 - (-(259388097 / 500000000 : ℝ))| ≤ (3463356742701 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 - (-(259388097 / 500000000 : ℝ)))]

theorem thL_206_sin_r : (-495817896868749 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) ≤ (-247908775266521 / 500000000000000 : ℝ) := by
  have hr := thL_206_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (259388097 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1550979816951913392548505721310375516130030864821899116196949886614769387338528058647175365224144077216445781103393244539 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(259388097 / 500000000 : ℝ)) ∧ Real.sin (-(259388097 / 500000000 : ℝ)) ≤ -((119306139765524182129045008287411409979306954947217401213536829076289729612740479016106698395819478287 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565) (-(259388097 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 - (-(259388097 / 500000000 : ℝ))| ≤ (3463356742701 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 206) 565 - (-(259388097 / 500000000 : ℝ)))]

theorem thL_206_cos : (247908775266521 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 206) ∧ Real.cos (16647931 / 100000 * Real.log 206) ≤ (495817896868749 / 1000000000000000 : ℝ) := by
  have hc := thL_206_cos_r
  have hs := thL_206_sin_r
  rw [thL_206_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_206_sin : (434213220692203 / 500000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 206) ∧ Real.sin (16647931 / 100000 * Real.log 206) ≤ (434213393860437 / 500000000000000 : ℝ) := by
  have hc := thL_206_cos_r
  have hs := thL_206_sin_r
  rw [thL_206_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_206 : (247908775266521 / 500000000000000 : ℝ) ≤ cCG cZ 206 ∧ cCG cZ 206 ≤ (495817896868749 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_206_cos

theorem sCB_206 : (434213220692203 / 500000000000000 : ℝ) ≤ sCG cZ 206 ∧ sCG cZ 206 ≤ (434213393860437 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_206_sin

theorem thL_207_r_bounds : (11496816595005645289 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 ≤ (11496830444994354711 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_207
  have hl : (887787345053991731 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 207 ∧ 16647931 / 100000 * Real.log 207 ≤ (221946836349900681 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_207_eq : (16647931 / 100000 * Real.log 207) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 + π / 2) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_207_cos_r : (958978102398821 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) ≤ (958978448648541 / 1000000000000000 : ℝ) := by
  have hr := thL_207_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (71855147 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) (71855147 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 - (71855147 / 250000000 : ℝ)| ≤ (6924994354711 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 - (71855147 / 250000000 : ℝ))]

theorem thL_207_sin_r : (56695879539499 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) ≤ (141739871973607 / 500000000000000 : ℝ) := by
  have hr := thL_207_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (71855147 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565) (71855147 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 - (71855147 / 250000000 : ℝ)| ≤ (6924994354711 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 207) 565 - (71855147 / 250000000 : ℝ))]

theorem thL_207_cos : (-141739871973607 / 500000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 207) ∧ Real.cos (16647931 / 100000 * Real.log 207) ≤ (-56695879539499 / 200000000000000 : ℝ) := by
  have hc := thL_207_cos_r
  have hs := thL_207_sin_r
  rw [thL_207_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_207_sin : (958978102398821 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 207) ∧ Real.sin (16647931 / 100000 * Real.log 207) ≤ (958978448648541 / 1000000000000000 : ℝ) := by
  have hc := thL_207_cos_r
  have hs := thL_207_sin_r
  rw [thL_207_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_207 : (-141739871973607 / 500000000000000 : ℝ) ≤ cCG cZ 207 ∧ cCG cZ 207 ≤ (-56695879539499 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_207_cos

theorem sCB_207 : (958978102398821 / 1000000000000000 : ℝ) ≤ sCG cZ 207 ∧ sCG cZ 207 ≤ (958978448648541 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_207_sin

theorem thL_208_r_bounds : (-24053221612018475791 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 ≤ (-24053204287981524209 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_208
  have hl : (888589656534540863 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 208 ∧ 16647931 / 100000 * Real.log 208 ≤ (55536853555009491 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_208_eq : (16647931 / 100000 * Real.log 208) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 + π) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_208_cos_r : (443251397330833 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) ≤ (886503141142727 / 1000000000000000 : ℝ) := by
  have hr := thL_208_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(481064259 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) (-(481064259 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 - (-(481064259 / 1000000000 : ℝ))| ≤ (8662018475791 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 - (-(481064259 / 1000000000 : ℝ)))]

theorem thL_208_sin_r : (-462723079416749 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) ≤ (-462722732935997 / 1000000000000000 : ℝ) := by
  have hr := thL_208_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (481064259 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((130302770379268195897788537791962874029708983943445905982472497191405940434490178020617903702707934720277113589259989706483 / 281600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(481064259 / 1000000000 : ℝ)) ∧ Real.sin (-(481064259 / 1000000000 : ℝ)) ≤ -((228029848163713494508540634558600830786467107534577117431037770516314277189342672323905364813923799950261 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566) (-(481064259 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 - (-(481064259 / 1000000000 : ℝ))| ≤ (8662018475791 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 208) 566 - (-(481064259 / 1000000000 : ℝ)))]

theorem thL_208_cos : (-886503141142727 / 1000000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 208) ∧ Real.cos (16647931 / 100000 * Real.log 208) ≤ (-443251397330833 / 500000000000000 : ℝ) := by
  have hc := thL_208_cos_r
  have hs := thL_208_sin_r
  rw [thL_208_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_208_sin : (462722732935997 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 208) ∧ Real.sin (16647931 / 100000 * Real.log 208) ≤ (462723079416749 / 1000000000000000 : ℝ) := by
  have hc := thL_208_cos_r
  have hs := thL_208_sin_r
  rw [thL_208_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_208 : (-886503141142727 / 1000000000000000 : ℝ) ≤ cCG cZ 208 ∧ cCG cZ 208 ≤ (-443251397330833 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_208_cos

theorem sCB_208 : (462722732935997 / 1000000000000000 : ℝ) ≤ sCG cZ 208 ∧ sCG cZ 208 ≤ (462723079416749 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_208_sin

theorem thL_209_r_bounds : (31739901769683451299 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 ∧ PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 ≤ (31739936430316548701 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_209
  have hl : (889388119983608321 / 1000000000000000 : ℝ) ≤ 16647931 / 100000 * Real.log 209 ∧ 16647931 / 100000 * Real.log 209 ≤ (444694060164609657 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_209_eq : (16647931 / 100000 * Real.log 209) = (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 + π) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_209_cos_r : (118756270123507 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) ∧ Real.cos (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) ≤ (95005050759439 / 100000000000000 : ℝ) := by
  have hr := thL_209_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (317399191 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) (317399191 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 - (317399191 / 1000000000 : ℝ)| ≤ (17330316548701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 - (317399191 / 1000000000 : ℝ))]

theorem thL_209_sin_r : (312096546181569 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) ∧ Real.sin (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) ≤ (312096892787901 / 1000000000000000 : ℝ) := by
  have hr := thL_209_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (317399191 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566) (317399191 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 - (317399191 / 1000000000 : ℝ)| ≤ (17330316548701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (16647931 / 100000 * Real.log 209) 566 - (317399191 / 1000000000 : ℝ))]

theorem thL_209_cos : (-95005050759439 / 100000000000000 : ℝ) ≤ Real.cos (16647931 / 100000 * Real.log 209) ∧ Real.cos (16647931 / 100000 * Real.log 209) ≤ (-118756270123507 / 125000000000000 : ℝ) := by
  have hc := thL_209_cos_r
  have hs := thL_209_sin_r
  rw [thL_209_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_209_sin : (-312096892787901 / 1000000000000000 : ℝ) ≤ Real.sin (16647931 / 100000 * Real.log 209) ∧ Real.sin (16647931 / 100000 * Real.log 209) ≤ (-312096546181569 / 1000000000000000 : ℝ) := by
  have hc := thL_209_cos_r
  have hs := thL_209_sin_r
  rw [thL_209_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_209 : (-95005050759439 / 100000000000000 : ℝ) ≤ cCG cZ 209 ∧ cCG cZ 209 ≤ (-118756270123507 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_209_cos

theorem sCB_209 : (-312096892787901 / 1000000000000000 : ℝ) ≤ sCG cZ 209 ∧ sCG cZ 209 ≤ (-312096546181569 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_209_sin

end PsiOmega.Locate.Z3

#print axioms PsiOmega.Locate.Z3.cCB_209
#print axioms PsiOmega.Locate.Z3.sCB_209
