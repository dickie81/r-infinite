import DHLocate2Exp

/-! # Generated (`gen_locate_zero.py 2`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 11416334 / 100000`, `n ∈ NS`

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate.Z2

theorem thL_2_r_bounds : (1184361784548969923 / 2000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 ≤ (1184361831451030077 / 2000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_2
  have hl : (79131997232637677 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 2 ∧ 11416334 / 100000 * Real.log 2 ≤ (39565998627735173 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_2_eq : (11416334 / 100000 * Real.log 2) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 + π) + ((12 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_2_cos_r : (103715665279247 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) ≤ (829725345688889 / 1000000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (74022613 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) (74022613 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 - (74022613 / 125000000 : ℝ)| ≤ (23451030077 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 - (74022613 / 125000000 : ℝ))]

theorem thL_2_sin_r : (139542972120033 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) ≤ (27908595596567 / 50000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (74022613 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50) (74022613 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 - (74022613 / 125000000 : ℝ)| ≤ (23451030077 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 2) 50 - (74022613 / 125000000 : ℝ))]

theorem thL_2_cos : (-829725345688889 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 2) ∧ Real.cos (11416334 / 100000 * Real.log 2) ≤ (-103715665279247 / 125000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_2_sin : (-27908595596567 / 50000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 2) ∧ Real.sin (11416334 / 100000 * Real.log 2) ≤ (-139542972120033 / 250000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_2 : (-829725345688889 / 1000000000000000 : ℝ) ≤ cCG cZ 2 ∧ cCG cZ 2 ≤ (-103715665279247 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_cos

theorem sCB_2 : (-27908595596567 / 50000000000000 : ℝ) ≤ sCG cZ 2 ∧ sCG cZ 2 ≤ (-139542972120033 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_sin

theorem thL_3_r_bounds : (-606144790954926347 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 ≤ (-606144714045073653 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_3
  have hl : (125421248227209759 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 3 ∧ 11416334 / 100000 * Real.log 3 ≤ (125421248257835979 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_3_eq : (11416334 / 100000 * Real.log 3) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) + ((20 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_3_cos_r : (194150155295113 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) ≤ (970750807239507 / 1000000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(242457901 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) (-(242457901 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 - (-(242457901 / 1000000000 : ℝ))| ≤ (38454926347 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 - (-(242457901 / 1000000000 : ℝ)))]

theorem thL_3_sin_r : (-120044686985787 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) ≤ (-15005583950477 / 62500000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (242457901 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((213577347113730687060963495575306398481352766083441215796354090037814134343787750891743814726664466182021372560730098579133243 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(242457901 / 1000000000 : ℝ)) ∧ Real.sin (-(242457901 / 1000000000 : ℝ)) ≤ -((1369085558421350548919843841989079891780308139025379741618434361536361646252047849333141145843826487916157 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80) (-(242457901 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 - (-(242457901 / 1000000000 : ℝ))| ≤ (38454926347 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 3) 80 - (-(242457901 / 1000000000 : ℝ)))]

theorem thL_3_cos : (194150155295113 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 3) ∧ Real.cos (11416334 / 100000 * Real.log 3) ≤ (970750807239507 / 1000000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_3_sin : (-120044686985787 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 3) ∧ Real.sin (11416334 / 100000 * Real.log 3) ≤ (-15005583950477 / 62500000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_3 : (194150155295113 / 200000000000000 : ℝ) ≤ cCG cZ 3 ∧ cCG cZ 3 ≤ (970750807239507 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_cos

theorem sCB_3 : (-120044686985787 / 500000000000000 : ℝ) ≤ sCG cZ 3 ∧ sCG cZ 3 ≤ (-15005583950477 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_sin

theorem thL_4_r_bounds : (-38643453098985445777 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 ≤ (-38643449701014554223 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_4
  have hl : (79131997238121259 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 4 ∧ 11416334 / 100000 * Real.log 4 ≤ (158263994509274413 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_4_eq : (11416334 / 100000 * Real.log 4) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 + π / 2) + ((25 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_4_cos_r : (3705034869727 / 4000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) ≤ (926258751411483 / 1000000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(193217257 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) (-(193217257 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 - (-(193217257 / 500000000 : ℝ))| ≤ (1698985445777 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 - (-(193217257 / 500000000 : ℝ)))]

theorem thL_4_sin_r : (-18844413609489 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) ≤ (-37688823821007 / 100000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (193217257 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40926531187319375252098113045998613179206544807183150945927349186868913890379799491702439857049020121230000478011203579951 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(193217257 / 500000000 : ℝ)) ∧ Real.sin (-(193217257 / 500000000 : ℝ)) ≤ -((7345787649006028298719567814533362277224878094171512653493007013200722249105658318872875599633779688007 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101) (-(193217257 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 - (-(193217257 / 500000000 : ℝ))| ≤ (1698985445777 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 4) 101 - (-(193217257 / 500000000 : ℝ)))]

theorem thL_4_cos : (37688823821007 / 100000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 4) ∧ Real.cos (11416334 / 100000 * Real.log 4) ≤ (18844413609489 / 50000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_4_sin : (3705034869727 / 4000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 4) ∧ Real.sin (11416334 / 100000 * Real.log 4) ≤ (926258751411483 / 1000000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_4 : (37688823821007 / 100000000000000 : ℝ) ≤ cCG cZ 4 ∧ cCG cZ 4 ≤ (18844413609489 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_cos

theorem sCB_4 : (3705034869727 / 4000000000000 : ℝ) ≤ sCG cZ 4 ∧ sCG cZ 4 ≤ (926258751411483 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_sin

theorem thL_6_r_bounds : (6994459745067749989 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 ≤ (6994460574932250011 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_6
  have hl : (51138311367647487 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 6 ∧ 11416334 / 100000 * Real.log 6 ≤ (204553245511795671 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_6_eq : (11416334 / 100000 * Real.log 6) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 + π) + ((32 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_6_cos_r : (1834897726587 / 1953125000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) ≤ (939467677505777 / 1000000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (2732211 / 7812500 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) (2732211 / 7812500 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 - (2732211 / 7812500 : ℝ)| ≤ (414932250011 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 - (2732211 / 7812500 : ℝ))]

theorem thL_6_sin_r : (68527514966269 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) ≤ (85659404081143 / 250000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (2732211 / 7812500 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130) (2732211 / 7812500 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 - (2732211 / 7812500 : ℝ)| ≤ (414932250011 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 6) 130 - (2732211 / 7812500 : ℝ))]

theorem thL_6_cos : (-939467677505777 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 6) ∧ Real.cos (11416334 / 100000 * Real.log 6) ≤ (-1834897726587 / 1953125000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_6_sin : (-85659404081143 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 6) ∧ Real.sin (11416334 / 100000 * Real.log 6) ≤ (-68527514966269 / 200000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_6 : (-939467677505777 / 1000000000000000 : ℝ) ≤ cCG cZ 6 ∧ cCG cZ 6 ≤ (-1834897726587 / 1953125000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_cos

theorem sCB_6 : (-85659404081143 / 250000000000000 : ℝ) ≤ sCG cZ 6 ∧ sCG cZ 6 ≤ (-68527514966269 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_sin

theorem thL_7_r_bounds : (133863972969662937573 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 ≤ (133863981430337062427 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_7
  have hl : (111075800971464369 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 7 ∧ 11416334 / 100000 * Real.log 7 ≤ (222151601984262623 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_7_eq : (11416334 / 100000 * Real.log 7) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 + π / 2) + ((35 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_7_cos_r : (196060951165757 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) ≤ (31369753879331 / 40000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (334659943 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) (334659943 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 - (334659943 / 500000000 : ℝ)| ≤ (4230337062427 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 - (334659943 / 500000000 : ℝ))]

theorem thL_7_sin_r : (310226367108269 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) ≤ (310226388260389 / 500000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (334659943 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141) (334659943 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 - (334659943 / 500000000 : ℝ)| ≤ (4230337062427 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 7) 141 - (334659943 / 500000000 : ℝ))]

theorem thL_7_cos : (-310226388260389 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 7) ∧ Real.cos (11416334 / 100000 * Real.log 7) ≤ (-310226367108269 / 500000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_7_sin : (196060951165757 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 7) ∧ Real.sin (11416334 / 100000 * Real.log 7) ≤ (31369753879331 / 40000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_7 : (-310226388260389 / 500000000000000 : ℝ) ≤ cCG cZ 7 ∧ cCG cZ 7 ≤ (-310226367108269 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_cos

theorem sCB_7 : (196060951165757 / 250000000000000 : ℝ) ≤ sCG cZ 7 ∧ sCG cZ 7 ≤ (31369753879331 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_sin

theorem thL_8_r_bounds : (41149274620777299103 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 ≤ (41149284179222700897 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_8
  have hl : (59348997929783319 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 8 ∧ 11416334 / 100000 * Real.log 8 ≤ (14837249485402061 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_8_eq : (11416334 / 100000 * Real.log 8) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 + π + π / 2) + ((37 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_8_cos_r : (978908745998471 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) ≤ (978908793790699 / 1000000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (205746397 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) (205746397 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 - (205746397 / 1000000000 : ℝ)| ≤ (4779222700897 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 - (205746397 / 1000000000 : ℝ))]

theorem thL_8_sin_r : (10214892370899 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) ≤ (6384309225319 / 31250000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (205746397 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151) (205746397 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 - (205746397 / 1000000000 : ℝ)| ≤ (4779222700897 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 8) 151 - (205746397 / 1000000000 : ℝ))]

theorem thL_8_cos : (10214892370899 / 50000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 8) ∧ Real.cos (11416334 / 100000 * Real.log 8) ≤ (6384309225319 / 31250000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_8_sin : (-978908793790699 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 8) ∧ Real.sin (11416334 / 100000 * Real.log 8) ≤ (-978908745998471 / 1000000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_8 : (10214892370899 / 50000000000000 : ℝ) ≤ cCG cZ 8 ∧ cCG cZ 8 ≤ (6384309225319 / 31250000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_cos

theorem sCB_8 : (-978908793790699 / 1000000000000000 : ℝ) ≤ sCG cZ 8 ∧ sCG cZ 8 ≤ (-978908745998471 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_sin

theorem thL_9_r_bounds : (-303072389274294327 / 625000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 ≤ (-303072358225705673 / 625000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_9
  have hl : (50168499292958113 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 9 ∧ 11416334 / 100000 * Real.log 9 ≤ (25084249651402233 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_9_eq : (11416334 / 100000 * Real.log 9) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) + ((40 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_9_cos_r : (442357088404689 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) ≤ (442357113243737 / 500000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(242457899 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) (-(242457899 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 - (-(242457899 / 500000000 : ℝ))| ≤ (15524294327 / 625000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 - (-(242457899 / 500000000 : ℝ)))]

theorem thL_9_sin_r : (-29133368202179 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) ≤ (-116533460389277 / 250000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (242457899 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((50617767885607346357557677713523757696612518865820588989309719250550838756128772269266585889899966248994959763016651138957 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(242457899 / 500000000 : ℝ)) ∧ Real.sin (-(242457899 / 500000000 : ℝ)) ≤ -((9085240389724138928948286997042943307653726638961546286174115692689046349308095557892077109791380513101 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160) (-(242457899 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 - (-(242457899 / 500000000 : ℝ))| ≤ (15524294327 / 625000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 9) 160 - (-(242457899 / 500000000 : ℝ)))]

theorem thL_9_cos : (442357088404689 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 9) ∧ Real.cos (11416334 / 100000 * Real.log 9) ≤ (442357113243737 / 500000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_9_sin : (-29133368202179 / 62500000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 9) ∧ Real.sin (11416334 / 100000 * Real.log 9) ≤ (-116533460389277 / 250000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_9 : (442357088404689 / 500000000000000 : ℝ) ≤ cCG cZ 9 ∧ cCG cZ 9 ≤ (442357113243737 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_cos

theorem sCB_9 : (-29133368202179 / 62500000000000 : ℝ) ≤ sCG cZ 9 ∧ sCG cZ 9 ≤ (-116533460389277 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_sin

theorem thL_11_r_bounds : (43317243644977525311 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 ≤ (43317248755022474689 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_11
  have hl : (273751733298761787 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 11 ∧ 11416334 / 100000 * Real.log 11 ≤ (68437933337247803 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_11_eq : (11416334 / 100000 * Real.log 11) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 + π) + ((43 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_11_cos_r : (907638645417411 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) ≤ (14181854633093 / 15625000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (216586231 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) (216586231 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 - (216586231 / 500000000 : ℝ)| ≤ (2555022474689 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 - (216586231 / 500000000 : ℝ))]

theorem thL_11_sin_r : (104938083385633 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) ≤ (209876192321493 / 500000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (216586231 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174) (216586231 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 - (216586231 / 500000000 : ℝ)| ≤ (2555022474689 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 11) 174 - (216586231 / 500000000 : ℝ))]

theorem thL_11_cos : (-14181854633093 / 15625000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 11) ∧ Real.cos (11416334 / 100000 * Real.log 11) ≤ (-907638645417411 / 1000000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_11_sin : (-209876192321493 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 11) ∧ Real.sin (11416334 / 100000 * Real.log 11) ≤ (-104938083385633 / 250000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_11 : (-14181854633093 / 15625000000000 : ℝ) ≤ cCG cZ 11 ∧ cCG cZ 11 ≤ (-907638645417411 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_cos

theorem sCB_11 : (-209876192321493 / 500000000000000 : ℝ) ≤ sCG cZ 11 ∧ sCG cZ 11 ≤ (-104938083385633 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_sin

theorem thL_12_r_bounds : (-62889243636310391937 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 ≤ (-62889238563689608063 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_12
  have hl : (283685242713882959 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 12 ∧ 11416334 / 100000 * Real.log 12 ≤ (8865163836382481 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_12_eq : (11416334 / 100000 * Real.log 12) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 + π / 2) + ((45 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_12_cos_r : (80867951743577 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) ≤ (80867956816997 / 100000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(628892411 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) (-(628892411 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 - (-(628892411 / 1000000000 : ℝ))| ≤ (2536310391937 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 - (-(628892411 / 1000000000 : ℝ)))]

theorem thL_12_sin_r : (-23529978389633 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) ≤ (-58824940901423 / 100000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (628892411 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((523291637636900427263559861356589268613715332314447099285324995122819337553790584041679668648772160005650034272545140617412733 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(628892411 / 1000000000 : ℝ)) ∧ Real.sin (-(628892411 / 1000000000 : ℝ)) ≤ -((3354433574593311263121184754572770219898028443882965569987373705228903631418334892562123473195505142610427 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181) (-(628892411 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 - (-(628892411 / 1000000000 : ℝ))| ≤ (2536310391937 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 12) 181 - (-(628892411 / 1000000000 : ℝ)))]

theorem thL_12_cos : (58824940901423 / 100000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 12) ∧ Real.cos (11416334 / 100000 * Real.log 12) ≤ (23529978389633 / 40000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_12_sin : (80867951743577 / 100000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 12) ∧ Real.sin (11416334 / 100000 * Real.log 12) ≤ (80867956816997 / 100000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_12 : (58824940901423 / 100000000000000 : ℝ) ≤ cCG cZ 12 ∧ cCG cZ 12 ≤ (23529978389633 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_cos

theorem sCB_12 : (80867951743577 / 100000000000000 : ℝ) ≤ sCG cZ 12 ∧ sCG cZ 12 ≤ (80867956816997 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_sin

theorem thL_13_r_bounds : (65506878068007682229 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 ≤ (65506883131992317771 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_13
  have hl : (9150724548891589 / 31250000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 13 ∧ 11416334 / 100000 * Real.log 13 ≤ (292823185614947231 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_13_eq : (11416334 / 100000 * Real.log 13) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 + π) + ((46 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_13_cos_r : (396502993540309 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) ≤ (793006037733501 / 1000000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (327534403 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) (327534403 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 - (327534403 / 500000000 : ℝ)| ≤ (2531992317771 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 - (327534403 / 500000000 : ℝ))]

theorem thL_13_sin_r : (609213783022573 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) ≤ (609213833663077 / 1000000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (327534403 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186) (327534403 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 - (327534403 / 500000000 : ℝ)| ≤ (2531992317771 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 13) 186 - (327534403 / 500000000 : ℝ))]

theorem thL_13_cos : (-793006037733501 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 13) ∧ Real.cos (11416334 / 100000 * Real.log 13) ≤ (-396502993540309 / 500000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_13_sin : (-609213833663077 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 13) ∧ Real.sin (11416334 / 100000 * Real.log 13) ≤ (-609213783022573 / 1000000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_13 : (-793006037733501 / 1000000000000000 : ℝ) ≤ cCG cZ 13 ∧ cCG cZ 13 ≤ (-396502993540309 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_cos

theorem sCB_13 : (-609213833663077 / 1000000000000000 : ℝ) ≤ sCG cZ 13 ∧ sCG cZ 13 ≤ (-609213783022573 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_sin

theorem thL_14_r_bounds : (-966548619989846541 / 3125000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 ≤ (-966548461260153459 / 3125000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_14
  have hl : (1506417995931117 / 5000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 14 ∧ 11416334 / 100000 * Real.log 14 ≤ (301283599236669767 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_14_eq : (11416334 / 100000 * Real.log 14) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) + ((48 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_14_cos_r : (238137052976139 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) ≤ (952548262698061 / 1000000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(309295533 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) (-(309295533 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 - (-(309295533 / 1000000000 : ℝ))| ≤ (79364846541 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 - (-(309295533 / 1000000000 : ℝ)))]

theorem thL_14_sin_r : (-60877539725283 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) ≤ (-19024227989557 / 62500000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (309295533 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7800116759114058281741433801458608320370397090966116033286351274598561856003980973590166275129392155174831486527423524751791 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(309295533 / 1000000000 : ℝ)) ∧ Real.sin (-(309295533 / 1000000000 : ℝ)) ≤ -((150002245367578025118996316939640774530577285957105523545922432073308013289014740396667557967695990309243 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192) (-(309295533 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 - (-(309295533 / 1000000000 : ℝ))| ≤ (79364846541 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 14) 192 - (-(309295533 / 1000000000 : ℝ)))]

theorem thL_14_cos : (238137052976139 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 14) ∧ Real.cos (11416334 / 100000 * Real.log 14) ≤ (952548262698061 / 1000000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_14_sin : (-60877539725283 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 14) ∧ Real.sin (11416334 / 100000 * Real.log 14) ≤ (-19024227989557 / 62500000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_14 : (238137052976139 / 250000000000000 : ℝ) ≤ cCG cZ 14 ∧ cCG cZ 14 ≤ (952548262698061 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_cos

theorem sCB_14 : (-60877539725283 / 200000000000000 : ℝ) ≤ sCG cZ 14 ∧ sCG cZ 14 ≤ (-19024227989557 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_sin

theorem thL_16_r_bounds : (-77286905066712808547 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 ≤ (-77286899133287191453 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_16
  have hl : (316527988961901989 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 16 ∧ 11416334 / 100000 * Real.log 16 ≤ (15826399451033587 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_16_eq : (11416334 / 100000 * Real.log 16) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 + π) + ((50 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_16_cos_r : (715910461310411 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) ≤ (89488815092437 / 125000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(772869021 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) (-(772869021 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 - (-(772869021 / 1000000000 : ℝ))| ≤ (2966712808547 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 - (-(772869021 / 1000000000 : ℝ)))]

theorem thL_16_sin_r : (-2727312895373 / 3906250000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) ≤ (-698192041875593 / 1000000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (772869021 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((17891590748669631530015599063603739234946395173665581329419482852480417020896820667169051221093356624630827269749068662619327 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(772869021 / 1000000000 : ℝ)) ∧ Real.sin (-(772869021 / 1000000000 : ℝ)) ≤ -((344069052856253152721789188930541718569259468659772505719353380712110408847498857153511907713563015174059 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202) (-(772869021 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 - (-(772869021 / 1000000000 : ℝ))| ≤ (2966712808547 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 16) 202 - (-(772869021 / 1000000000 : ℝ)))]

theorem thL_16_cos : (-89488815092437 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 16) ∧ Real.cos (11416334 / 100000 * Real.log 16) ≤ (-715910461310411 / 1000000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_16_sin : (698192041875593 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 16) ∧ Real.sin (11416334 / 100000 * Real.log 16) ≤ (2727312895373 / 3906250000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_16 : (-89488815092437 / 125000000000000 : ℝ) ≤ cCG cZ 16 ∧ cCG cZ 16 ≤ (-715910461310411 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_cos

theorem sCB_16 : (698192041875593 / 1000000000000000 : ℝ) ≤ sCG cZ 16 ∧ sCG cZ 16 ≤ (2727312895373 / 3906250000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_sin

theorem thL_17_r_bounds : (-6747252316029571931 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 ≤ (-6747249083970428069 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_17
  have hl : (323449098273937159 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 17 ∧ 11416334 / 100000 * Real.log 17 ≤ (64689819667613859 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_17_eq : (11416334 / 100000 * Real.log 17) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 + π) + ((51 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_17_cos_r : (495454348984409 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) ≤ (495454381305001 / 500000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(67472507 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) (-(67472507 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 - (-(67472507 / 500000000 : ℝ))| ≤ (1616029571931 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 - (-(67472507 / 500000000 : ℝ)))]

theorem thL_17_sin_r : (-67267928711953 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) ≤ (-67267896391361 / 500000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (67472507 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((102265305330016843094887900863636277342395359937576236043164997526855417036240647653472211739927796123892007473789554652907 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(67472507 / 500000000 : ℝ)) ∧ Real.sin (-(67472507 / 500000000 : ℝ)) ≤ -((2622187316154278028058646481714333083443101649073244289618802908418946970485888257305611919280121745757 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206) (-(67472507 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 - (-(67472507 / 500000000 : ℝ))| ≤ (1616029571931 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 17) 206 - (-(67472507 / 500000000 : ℝ)))]

theorem thL_17_cos : (-495454381305001 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 17) ∧ Real.cos (11416334 / 100000 * Real.log 17) ≤ (-495454348984409 / 500000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_17_sin : (67267896391361 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 17) ∧ Real.sin (11416334 / 100000 * Real.log 17) ≤ (67267928711953 / 500000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_17 : (-495454381305001 / 500000000000000 : ℝ) ≤ cCG cZ 17 ∧ cCG cZ 17 ≤ (-495454348984409 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_cos

theorem sCB_17 : (67267896391361 / 500000000000000 : ℝ) ≤ sCG cZ 17 ∧ sCG cZ 17 ≤ (67267928711953 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_sin

theorem thL_18_r_bounds : (1072650787438380383 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 ≤ (1072651472561619617 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_18
  have hl : (164987246853250313 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 18 ∧ 11416334 / 100000 * Real.log 18 ≤ (82493623443546113 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_18_eq : (11416334 / 100000 * Real.log 18) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 + π) + ((52 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_18_cos_r : (994252577375979 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) ≤ (62140790368019 / 62500000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (107265113 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) (107265113 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 - (107265113 / 1000000000 : ℝ)| ≤ (342561619617 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 - (107265113 / 1000000000 : ℝ))]

theorem thL_18_sin_r : (53529750904917 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) ≤ (107059570322159 / 1000000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (107265113 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210) (107265113 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 - (107265113 / 1000000000 : ℝ)| ≤ (342561619617 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 18) 210 - (107265113 / 1000000000 : ℝ))]

theorem thL_18_cos : (-62140790368019 / 62500000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 18) ∧ Real.cos (11416334 / 100000 * Real.log 18) ≤ (-994252577375979 / 1000000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_18_sin : (-107059570322159 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 18) ∧ Real.sin (11416334 / 100000 * Real.log 18) ≤ (-53529750904917 / 500000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_18 : (-62140790368019 / 62500000000000 : ℝ) ≤ cCG cZ 18 ∧ cCG cZ 18 ≤ (-994252577375979 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_cos

theorem sCB_18 : (-107059570322159 / 1000000000000000 : ℝ) ≤ sCG cZ 18 ∧ sCG cZ 18 ≤ (-53529750904917 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_sin

theorem thL_19_r_bounds : (-342566321731651629 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 ≤ (-342559278268348371 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_19
  have hl : (1050459338346533 / 3125000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 19 ∧ 11416334 / 100000 * Real.log 19 ≤ (84036747085245327 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_19_eq : (11416334 / 100000 * Real.log 19) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 + π) + ((53 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_19_cos_r : (124999262165603 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) ≤ (499997083879729 / 500000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(856407 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) (-(856407 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 - (-(856407 / 250000000 : ℝ))| ≤ (3521731651629 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 - (-(856407 / 250000000 : ℝ)))]

theorem thL_19_sin_r : (-685131303481 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) ≤ (-3425586082771 / 1000000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (856407 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((186868227353131796241494087821313143685339664631214387070761906804510845961916195040075926589433029112895360121707 / 54550170898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(856407 / 250000000 : ℝ)) ∧ Real.sin (-(856407 / 250000000 : ℝ)) ≤ -((402485412760591561135525727615136001783639715963933688090488752200189728394288463520608954041897 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214) (-(856407 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 - (-(856407 / 250000000 : ℝ))| ≤ (3521731651629 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 19) 214 - (-(856407 / 250000000 : ℝ)))]

theorem thL_19_cos : (-499997083879729 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 19) ∧ Real.cos (11416334 / 100000 * Real.log 19) ≤ (-124999262165603 / 125000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_19_sin : (3425586082771 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 19) ∧ Real.sin (11416334 / 100000 * Real.log 19) ≤ (685131303481 / 200000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_19 : (-499997083879729 / 500000000000000 : ℝ) ≤ cCG cZ 19 ∧ cCG cZ 19 ≤ (-124999262165603 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_cos

theorem sCB_19 : (3425586082771 / 1000000000000000 : ℝ) ≤ sCG cZ 19 ∧ sCG cZ 19 ≤ (685131303481 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_sin

theorem thL_21_r_bounds : (85372391285948829813 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 ≤ (85372405914051170187 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_21
  have hl : (347572850178101897 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 21 ∧ 11416334 / 100000 * Real.log 21 ≤ (347572850251030633 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_21_eq : (11416334 / 100000 * Real.log 21) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 + π / 2) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_21_cos_r : (227567344781153 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) ≤ (910269452265201 / 1000000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (426861993 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) (426861993 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 - (426861993 / 1000000000 : ℝ)| ≤ (7314051170187 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 - (426861993 / 1000000000 : ℝ))]

theorem thL_21_sin_r : (207008188587439 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) ≤ (207008225157697 / 500000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (426861993 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221) (426861993 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 - (426861993 / 1000000000 : ℝ)| ≤ (7314051170187 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 21) 221 - (426861993 / 1000000000 : ℝ))]

theorem thL_21_cos : (-207008225157697 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 21) ∧ Real.cos (11416334 / 100000 * Real.log 21) ≤ (-207008188587439 / 500000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_21_sin : (227567344781153 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 21) ∧ Real.sin (11416334 / 100000 * Real.log 21) ≤ (910269452265201 / 1000000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_21 : (-207008225157697 / 500000000000000 : ℝ) ≤ cCG cZ 21 ∧ cCG cZ 21 ≤ (-207008188587439 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_cos

theorem sCB_21 : (227567344781153 / 250000000000000 : ℝ) ≤ sCG cZ 21 ∧ sCG cZ 21 ≤ (910269452265201 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_sin

theorem thL_22_r_bounds : (-4363543913106426623 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 ≤ (-4363543318893573377 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_22
  have hl : (88220932634928359 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 22 ∧ 11416334 / 100000 * Real.log 22 ≤ (352883730613482623 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_22_eq : (11416334 / 100000 * Real.log 22) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 + π / 2) + ((56 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_22_cos_r : (106862191928439 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) ≤ (854897609705567 / 1000000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(68180369 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) (-(68180369 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 - (-(68180369 / 125000000 : ℝ))| ≤ (297106426623 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 - (-(68180369 / 125000000 : ℝ)))]

theorem thL_22_sin_r : (-506637555777 / 976562500000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) ≤ (-25939839141949 / 50000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (68180369 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((5876351840875538221709094958883038264532636066629580219586407095646439838407585624773570722897999303139189599574609 / 11326884850859642028808593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(68180369 / 125000000 : ℝ)) ∧ Real.sin (-(68180369 / 125000000 : ℝ)) ≤ -((2410811011640964204519839532160875036750733179820243119787952489822023630264390885905210311700431 / 4646927118301391601562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225) (-(68180369 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 - (-(68180369 / 125000000 : ℝ))| ≤ (297106426623 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 22) 225 - (-(68180369 / 125000000 : ℝ)))]

theorem thL_22_cos : (25939839141949 / 50000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 22) ∧ Real.cos (11416334 / 100000 * Real.log 22) ≤ (506637555777 / 976562500000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_22_sin : (106862191928439 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 22) ∧ Real.sin (11416334 / 100000 * Real.log 22) ≤ (854897609705567 / 1000000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_22 : (25939839141949 / 50000000000000 : ℝ) ≤ cCG cZ 22 ∧ cCG cZ 22 ≤ (506637555777 / 976562500000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_cos

theorem sCB_22 : (106862191928439 / 125000000000000 : ℝ) ≤ sCG cZ 22 ∧ sCG cZ 22 ≤ (854897609705567 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_sin

theorem thL_23_r_bounds : (-9153514281847009279 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 ≤ (-9153510518152990721 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_23
  have hl : (357958492223599489 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 23 ∧ 11416334 / 100000 * Real.log 23 ≤ (357958492297980017 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_23_eq : (11416334 / 100000 * Real.log 23) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_23_cos_r : (196657870753067 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) ≤ (61455589314951 / 62500000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(22883781 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) (-(22883781 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 - (-(22883781 / 125000000 : ℝ))| ≤ (1881847009279 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 - (-(22883781 / 125000000 : ℝ)))]

theorem thL_23_sin_r : (-22756175830457 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) ≤ (-91024665684887 / 500000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (22883781 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1212258812410768828047493335886220719422452725225293459257047054362552715671947211039671512971398006251922566641 / 6658956408500671386718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(22883781 / 125000000 : ℝ)) ∧ Real.sin (-(22883781 / 125000000 : ℝ)) ≤ -((10444075922308162208480526720446497063295261331396050111346375513277540482079419681842119616499 / 57369470596313476562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228) (-(22883781 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 - (-(22883781 / 125000000 : ℝ))| ≤ (1881847009279 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 23) 228 - (-(22883781 / 125000000 : ℝ)))]

theorem thL_23_cos : (196657870753067 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 23) ∧ Real.cos (11416334 / 100000 * Real.log 23) ≤ (61455589314951 / 62500000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_23_sin : (-22756175830457 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 23) ∧ Real.sin (11416334 / 100000 * Real.log 23) ≤ (-91024665684887 / 500000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_23 : (196657870753067 / 200000000000000 : ℝ) ≤ cCG cZ 23 ∧ cCG cZ 23 ≤ (61455589314951 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_cos

theorem sCB_23 : (-22756175830457 / 125000000000000 : ℝ) ≤ sCG cZ 23 ∧ sCG cZ 23 ≤ (-91024665684887 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_sin

theorem thL_24_r_bounds : (-3671153590728095787 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 ≤ (-3671146009271904213 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_24
  have hl : (72563447990939397 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 24 ∧ 11416334 / 100000 * Real.log 24 ≤ (907043100073821 / 2500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_24_eq : (11416334 / 100000 * Real.log 24) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 + π + π / 2) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_24_cos_r : (199865234145883 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) ≤ (499663123271989 / 500000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(18355749 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) (-(18355749 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 - (-(18355749 / 500000000 : ℝ))| ≤ (3790728095787 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 - (-(18355749 / 500000000 : ℝ)))]

theorem thL_24_sin_r : (-18351645120043 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) ≤ (-36703214425523 / 1000000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (18355749 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((114812361203554004442230551206635198591425116024225094172901153147508342441726340924061727974495826756762197368184505143 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(18355749 / 500000000 : ℝ)) ∧ Real.sin (-(18355749 / 500000000 : ℝ)) ≤ -((8831720092581077264786965468932128510545173910316140755555775256872447567723018498650382667642063571 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231) (-(18355749 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 - (-(18355749 / 500000000 : ℝ))| ≤ (3790728095787 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 24) 231 - (-(18355749 / 500000000 : ℝ)))]

theorem thL_24_cos : (-18351645120043 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 24) ∧ Real.cos (11416334 / 100000 * Real.log 24) ≤ (-36703214425523 / 1000000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_24_sin : (-499663123271989 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 24) ∧ Real.sin (11416334 / 100000 * Real.log 24) ≤ (-199865234145883 / 200000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_24 : (-18351645120043 / 500000000000000 : ℝ) ≤ cCG cZ 24 ∧ cCG cZ 24 ≤ (-36703214425523 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_cos

theorem sCB_24 : (-499663123271989 / 500000000000000 : ℝ) ≤ sCG cZ 24 ∧ sCG cZ 24 ≤ (-199865234145883 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_sin

theorem thL_26_r_bounds : (-64709329024686551739 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 ≤ (-64709313775313448261 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_26
  have hl : (185977591402633533 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 26 ∧ 11416334 / 100000 * Real.log 26 ≤ (185977591440344901 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_26_eq : (11416334 / 100000 * Real.log 26) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 + π / 2) + ((59 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_26_cos_r : (189622753679359 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) ≤ (59257115290229 / 62500000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(323546607 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) (-(323546607 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 - (-(323546607 / 1000000000 : ℝ))| ≤ (7624686551739 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 - (-(323546607 / 1000000000 : ℝ)))]

theorem thL_26_sin_r : (-15896558914351 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) ≤ (-158965551020077 / 500000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (323546607 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((8147176225376013465451979416154730663227806467615662367559735936204763797977371058261407598576552153935757244106794199560149 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(323546607 / 1000000000 : ℝ)) ∧ Real.sin (-(323546607 / 1000000000 : ℝ)) ≤ -((156676465872615609871076264881924369942215955135436414300334709346397946975172480523042834597085121888097 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237) (-(323546607 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 - (-(323546607 / 1000000000 : ℝ))| ≤ (7624686551739 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 26) 237 - (-(323546607 / 1000000000 : ℝ)))]

theorem thL_26_cos : (158965551020077 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 26) ∧ Real.cos (11416334 / 100000 * Real.log 26) ≤ (15896558914351 / 50000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_26_sin : (189622753679359 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 26) ∧ Real.sin (11416334 / 100000 * Real.log 26) ≤ (59257115290229 / 62500000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_26 : (158965551020077 / 500000000000000 : ℝ) ≤ cCG cZ 26 ∧ cCG cZ 26 ≤ (15896558914351 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_cos

theorem sCB_26 : (189622753679359 / 200000000000000 : ℝ) ≤ sCG cZ 26 ∧ sCG cZ 26 ≤ (59257115290229 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_sin

theorem thL_27_r_bounds : (-909217164123195481 / 1250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 ≤ (-909217068376804519 / 1250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_27
  have hl : (376263744700456571 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 27 ∧ 11416334 / 100000 * Real.log 27 ≤ (75252748955214749 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_27_eq : (11416334 / 100000 * Real.log 27) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_27_cos_r : (186730799115833 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) ≤ (373461636553117 / 500000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(727373693 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) (-(727373693 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 - (-(727373693 / 1000000000 : ℝ))| ≤ (47873195481 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 - (-(727373693 / 1000000000 : ℝ)))]

theorem thL_27_sin_r : (-332455159470737 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) ≤ (-332455121170899 / 500000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (727373693 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((591487163956754583617587984047548198846100087040779172495165875120839755367208518381165693233182686933896983267918266484701099 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(727373693 / 1000000000 : ℝ)) ∧ Real.sin (-(727373693 / 1000000000 : ℝ)) ≤ -((26541090690264928550049864353209360851073366672713209569690180514624632573103701617846835850614862493912443 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240) (-(727373693 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 - (-(727373693 / 1000000000 : ℝ))| ≤ (47873195481 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 27) 240 - (-(727373693 / 1000000000 : ℝ)))]

theorem thL_27_cos : (186730799115833 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 27) ∧ Real.cos (11416334 / 100000 * Real.log 27) ≤ (373461636553117 / 500000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_27_sin : (-332455159470737 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 27) ∧ Real.sin (11416334 / 100000 * Real.log 27) ≤ (-332455121170899 / 500000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_27 : (186730799115833 / 250000000000000 : ℝ) ≤ cCG cZ 27 ∧ cCG cZ 27 ≤ (373461636553117 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_cos

theorem sCB_27 : (-332455159470737 / 500000000000000 : ℝ) ≤ sCG cZ 27 ∧ sCG cZ 27 ≤ (-332455121170899 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_sin

theorem thL_28_r_bounds : (14144267084201992683 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 ≤ (14144270915798007317 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_28
  have hl : (23775974776682109 / 62500000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 28 ∧ 11416334 / 100000 * Real.log 28 ≤ (190207798251340471 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_28_eq : (11416334 / 100000 * Real.log 28) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 + π) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_28_cos_r : (960254009448767 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) ≤ (960254086080689 / 1000000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (14144269 / 50000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) (14144269 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 - (14144269 / 50000000 : ℝ)| ≤ (1915798007317 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 - (14144269 / 50000000 : ℝ))]

theorem thL_28_sin_r : (279127466153691 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) ≤ (69781885696403 / 250000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (14144269 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242) (14144269 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 - (14144269 / 50000000 : ℝ)| ≤ (1915798007317 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 28) 242 - (14144269 / 50000000 : ℝ))]

theorem thL_28_cos : (-960254086080689 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 28) ∧ Real.cos (11416334 / 100000 * Real.log 28) ≤ (-960254009448767 / 1000000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_28_sin : (-69781885696403 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 28) ∧ Real.sin (11416334 / 100000 * Real.log 28) ≤ (-279127466153691 / 1000000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_28 : (-960254086080689 / 1000000000000000 : ℝ) ≤ cCG cZ 28 ∧ cCG cZ 28 ≤ (-960254009448767 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_cos

theorem sCB_28 : (-69781885696403 / 250000000000000 : ℝ) ≤ sCG cZ 28 ∧ sCG cZ 28 ≤ (-279127466153691 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_sin

theorem thL_29_r_bounds : (-16934454527594108503 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 ≤ (-16934451472405891497 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_29
  have hl : (384421738701559819 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 29 ∧ 11416334 / 100000 * Real.log 29 ≤ (384421738777443851 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_29_eq : (11416334 / 100000 * Real.log 29) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 + π / 2) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_29_cos_r : (911713131033021 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) ≤ (911713207412797 / 1000000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(16934453 / 40000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) (-(16934453 / 40000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 - (-(16934453 / 40000000 : ℝ))| ≤ (1527594108503 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 - (-(16934453 / 40000000 : ℝ)))]

theorem thL_29_sin_r : (-410827370612437 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) ≤ (-51353411779091 / 125000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (16934453 / 40000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1716799322498556050299843972905086105264008164150244350071524217251813582584870972382971080652919832787111173 / 4178882919923712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(16934453 / 40000000 : ℝ)) ∧ Real.sin (-(16934453 / 40000000 : ℝ)) ≤ -((6878202413856356694135624096257275929156995008360660448458340503978653821980652755042566803 / 16742319390720000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245) (-(16934453 / 40000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 - (-(16934453 / 40000000 : ℝ))| ≤ (1527594108503 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 29) 245 - (-(16934453 / 40000000 : ℝ)))]

theorem thL_29_cos : (51353411779091 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 29) ∧ Real.cos (11416334 / 100000 * Real.log 29) ≤ (410827370612437 / 1000000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_29_sin : (911713131033021 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 29) ∧ Real.sin (11416334 / 100000 * Real.log 29) ≤ (911713207412797 / 1000000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_29 : (51353411779091 / 125000000000000 : ℝ) ≤ cCG cZ 29 ∧ cCG cZ 29 ≤ (410827370612437 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_cos

theorem sCB_29 : (911713131033021 / 1000000000000000 : ℝ) ≤ sCG cZ 29 ∧ sCG cZ 29 ≤ (911713207412797 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_sin

theorem thL_31_r_bounds : (-530906348182864647 / 800000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 ≤ (-530906287017135353 / 800000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_31
  have hl : (196017724381747787 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 31 ∧ 11416334 / 100000 * Real.log 31 ≤ (392035448839544051 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_31_eq : (11416334 / 100000 * Real.log 31) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 + π) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_31_cos_r : (15755191893027 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) ≤ (393879835561873 / 500000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(663632897 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) (-(663632897 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 - (-(663632897 / 1000000000 : ℝ))| ≤ (30582864647 / 800000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 - (-(663632897 / 1000000000 : ℝ)))]

theorem thL_31_sin_r : (-615982798361473 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) ≤ (-153995680475883 / 250000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (663632897 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((547962494255560608354396442694046843249876778888848051948947993178686179614636135904309065573664422717528536095525951801065911 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(663632897 / 1000000000 : ℝ)) ∧ Real.sin (-(663632897 / 1000000000 : ℝ)) ≤ -((24588060639641550223248590639698597483616170780223157069234458794076761854958633315760034749772875646594047 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250) (-(663632897 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 - (-(663632897 / 1000000000 : ℝ))| ≤ (30582864647 / 800000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 31) 250 - (-(663632897 / 1000000000 : ℝ)))]

theorem thL_31_cos : (-393879835561873 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 31) ∧ Real.cos (11416334 / 100000 * Real.log 31) ≤ (-15755191893027 / 20000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_31_sin : (153995680475883 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 31) ∧ Real.sin (11416334 / 100000 * Real.log 31) ≤ (615982798361473 / 1000000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_31 : (-393879835561873 / 500000000000000 : ℝ) ≤ cCG cZ 31 ∧ cCG cZ 31 ≤ (-15755191893027 / 20000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_cos

theorem sCB_31 : (153995680475883 / 250000000000000 : ℝ) ≤ sCG cZ 31 ∧ sCG cZ 31 ≤ (615982798361473 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_sin

theorem thL_32_r_bounds : (-4517203738116473851 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 ≤ (-4517201811883526149 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_32
  have hl : (7913199724074643 / 20000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 32 ∧ 11416334 / 100000 * Real.log 32 ≤ (395659986279838607 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_32_eq : (11416334 / 100000 * Real.log 32) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_32_cos_r : (983720229130999 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) ≤ (491860153090159 / 500000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(180688111 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) (-(180688111 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 - (-(180688111 / 1000000000 : ℝ))| ≤ (963116473851 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 - (-(180688111 / 1000000000 : ℝ)))]

theorem thL_32_sin_r : (-179706563179387 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) ≤ (-44926621532517 / 250000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (180688111 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1119036266920702998036430399278283366820197893394093572751576903315877097693131745509709714296273961583186506097491647929885231 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(180688111 / 1000000000 : ℝ)) ∧ Real.sin (-(180688111 / 1000000000 : ℝ)) ≤ -((7173309403337839729600074752734090508568833343250585840878071236487942280106404615771622806329968757850289 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252) (-(180688111 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 - (-(180688111 / 1000000000 : ℝ))| ≤ (963116473851 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 32) 252 - (-(180688111 / 1000000000 : ℝ)))]

theorem thL_32_cos : (983720229130999 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 32) ∧ Real.cos (11416334 / 100000 * Real.log 32) ≤ (491860153090159 / 500000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_32_sin : (-179706563179387 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 32) ∧ Real.sin (11416334 / 100000 * Real.log 32) ≤ (-44926621532517 / 250000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_32 : (983720229130999 / 1000000000000000 : ℝ) ≤ cCG cZ 32 ∧ cCG cZ 32 ≤ (491860153090159 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_cos

theorem sCB_32 : (-179706563179387 / 1000000000000000 : ℝ) ≤ sCG cZ 32 ∧ sCG cZ 32 ≤ (-44926621532517 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_sin

theorem thL_33_r_bounds : (19071452855830171431 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 ≤ (19071460544169828569 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_33
  have hl : (399172981534462043 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 33 ∧ 11416334 / 100000 * Real.log 33 ≤ (399172981610615087 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_33_eq : (11416334 / 100000 * Real.log 33) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 + π) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_33_cos_r : (490934496822217 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) ≤ (122733633815979 / 125000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (190714567 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) (190714567 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 - (190714567 / 1000000000 : ℝ)| ≤ (3844169828569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 - (190714567 / 1000000000 : ℝ))]

theorem thL_33_sin_r : (189560516079121 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) ≤ (94780296481259 / 500000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (190714567 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254) (190714567 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 - (190714567 / 1000000000 : ℝ)| ≤ (3844169828569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 33) 254 - (190714567 / 1000000000 : ℝ))]

theorem thL_33_cos : (-122733633815979 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 33) ∧ Real.cos (11416334 / 100000 * Real.log 33) ≤ (-490934496822217 / 500000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_33_sin : (-94780296481259 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 33) ∧ Real.sin (11416334 / 100000 * Real.log 33) ≤ (-189560516079121 / 1000000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_33 : (-122733633815979 / 125000000000000 : ℝ) ≤ cCG cZ 33 ∧ cCG cZ 33 ≤ (-490934496822217 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_cos

theorem sCB_33 : (-94780296481259 / 500000000000000 : ℝ) ≤ sCG cZ 33 ∧ sCG cZ 33 ≤ (-189560516079121 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_sin

theorem thL_34_r_bounds : (1428862052442586009 / 3125000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 ≤ (1428862291307413991 / 3125000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_34
  have hl : (402581095516521181 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 34 ∧ 11416334 / 100000 * Real.log 34 ≤ (402581095592711907 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_34_eq : (11416334 / 100000 * Real.log 34) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) + ((64 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_34_cos_r : (112159519235547 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) ≤ (56079764395081 / 62500000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (91447179 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) (91447179 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 - (91447179 / 200000000 : ℝ)| ≤ (119432413991 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 - (91447179 / 200000000 : ℝ))]

theorem thL_34_sin_r : (220734796385149 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) ≤ (8829393384141 / 20000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (91447179 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256) (91447179 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 - (91447179 / 200000000 : ℝ)| ≤ (119432413991 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 34) 256 - (91447179 / 200000000 : ℝ))]

theorem thL_34_cos : (112159519235547 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 34) ∧ Real.cos (11416334 / 100000 * Real.log 34) ≤ (56079764395081 / 62500000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_34_sin : (220734796385149 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 34) ∧ Real.sin (11416334 / 100000 * Real.log 34) ≤ (8829393384141 / 20000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_34 : (112159519235547 / 125000000000000 : ℝ) ≤ cCG cZ 34 ∧ cCG cZ 34 ≤ (56079764395081 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_cos

theorem sCB_34 : (220734796385149 / 500000000000000 : ℝ) ≤ sCG cZ 34 ∧ sCG cZ 34 ≤ (8829393384141 / 20000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_sin

theorem thL_36_r_bounds : (3497229914213224999 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 ≤ (3497230295786775001 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_36
  have hl : (409106490949583971 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 36 ∧ 11416334 / 100000 * Real.log 36 ≤ (102276622756457619 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_36_eq : (11416334 / 100000 * Real.log 36) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) + ((65 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_36_cos_r : (9564986434853 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) ≤ (765198991131573 / 1000000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (699446021 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) (699446021 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 - (699446021 / 1000000000 : ℝ)| ≤ (190786775001 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 - (699446021 / 1000000000 : ℝ))]

theorem thL_36_sin_r : (643793843737541 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) ≤ (20118560001681 / 31250000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (699446021 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260) (699446021 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 - (699446021 / 1000000000 : ℝ)| ≤ (190786775001 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 36) 260 - (699446021 / 1000000000 : ℝ))]

theorem thL_36_cos : (9564986434853 / 12500000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 36) ∧ Real.cos (11416334 / 100000 * Real.log 36) ≤ (765198991131573 / 1000000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_36_sin : (643793843737541 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 36) ∧ Real.sin (11416334 / 100000 * Real.log 36) ≤ (20118560001681 / 31250000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_36 : (9564986434853 / 12500000000000 : ℝ) ≤ cCG cZ 36 ∧ cCG cZ 36 ≤ (765198991131573 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_cos

theorem sCB_36 : (643793843737541 / 1000000000000000 : ℝ) ≤ sCG cZ 36 ∧ sCG cZ 36 ≤ (20118560001681 / 31250000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_sin

theorem thL_37_r_bounds : (34290586726289311913 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 ≤ (34290590573710688087 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_37
  have hl : (3220581635589609 / 7812500000000 : ℝ) ≤ 11416334 / 100000 * Real.log 37 ∧ 11416334 / 100000 * Real.log 37 ≤ (51529306178967141 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_37_eq : (11416334 / 100000 * Real.log 37) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 + π) + ((65 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_37_cos_r : (773905166621473 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) ≤ (386952621796251 / 500000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (685811773 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) (685811773 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 - (685811773 / 1000000000 : ℝ)| ≤ (1923710688087 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 - (685811773 / 1000000000 : ℝ))]

theorem thL_37_sin_r : (39581338561693 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) ≤ (633301493936709 / 1000000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (685811773 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262) (685811773 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 - (685811773 / 1000000000 : ℝ)| ≤ (1923710688087 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 37) 262 - (685811773 / 1000000000 : ℝ))]

theorem thL_37_cos : (-386952621796251 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 37) ∧ Real.cos (11416334 / 100000 * Real.log 37) ≤ (-773905166621473 / 1000000000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_37_sin : (-633301493936709 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 37) ∧ Real.sin (11416334 / 100000 * Real.log 37) ≤ (-39581338561693 / 62500000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_37 : (-386952621796251 / 500000000000000 : ℝ) ≤ cCG cZ 37 ∧ cCG cZ 37 ≤ (-773905166621473 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_cos

theorem sCB_37 : (-633301493936709 / 1000000000000000 : ℝ) ≤ sCG cZ 37 ∧ sCG cZ 37 ≤ (-39581338561693 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_sin

theorem thL_38_r_bounds : (14718881011489788049 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 ≤ (14718882938510211951 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_38
  have hl : (415278985514312299 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 38 ∧ 11416334 / 100000 * Real.log 38 ≤ (51909873198824573 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_38_eq : (11416334 / 100000 * Real.log 38) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) + ((66 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_38_cos_r : (207908127731347 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) ≤ (831632588009827 / 1000000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (588755279 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) (588755279 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 - (588755279 / 1000000000 : ℝ)| ≤ (963510211951 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 - (588755279 / 1000000000 : ℝ))]

theorem thL_38_sin_r : (277663132166399 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) ≤ (27766317070689 / 50000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (588755279 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264) (588755279 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 - (588755279 / 1000000000 : ℝ)| ≤ (963510211951 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 38) 264 - (588755279 / 1000000000 : ℝ))]

theorem thL_38_cos : (207908127731347 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 38) ∧ Real.cos (11416334 / 100000 * Real.log 38) ≤ (831632588009827 / 1000000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_38_sin : (277663132166399 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 38) ∧ Real.sin (11416334 / 100000 * Real.log 38) ≤ (27766317070689 / 50000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_38 : (207908127731347 / 250000000000000 : ℝ) ≤ cCG cZ 38 ∧ cCG cZ 38 ≤ (831632588009827 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_cos

theorem sCB_38 : (277663132166399 / 500000000000000 : ℝ) ≤ sCG cZ 38 ∧ sCG cZ 38 ≤ (27766317070689 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_sin

theorem thL_39_r_bounds : (41261087278858928349 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 ≤ (41261094921141071651 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_39
  have hl : (41824443380023109 / 100000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 39 ∧ 11416334 / 100000 * Real.log 39 ≤ (104561108469132401 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_39_eq : (11416334 / 100000 * Real.log 39) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 + π) + ((66 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_39_cos_r : (916076926369797 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) ≤ (91607700279267 / 100000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (412610911 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) (412610911 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 - (412610911 / 1000000000 : ℝ)| ≤ (3821141071651 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 - (412610911 / 1000000000 : ℝ))]

theorem thL_39_sin_r : (200501224633321 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) ≤ (200501262844733 / 500000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (412610911 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266) (412610911 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 - (412610911 / 1000000000 : ℝ)| ≤ (3821141071651 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 39) 266 - (412610911 / 1000000000 : ℝ))]

theorem thL_39_cos : (-91607700279267 / 100000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 39) ∧ Real.cos (11416334 / 100000 * Real.log 39) ≤ (-916076926369797 / 1000000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_39_sin : (-200501262844733 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 39) ∧ Real.sin (11416334 / 100000 * Real.log 39) ≤ (-200501224633321 / 500000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_39 : (-91607700279267 / 100000000000000 : ℝ) ≤ cCG cZ 39 ∧ cCG cZ 39 ≤ (-916076926369797 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_cos

theorem sCB_39 : (-200501262844733 / 500000000000000 : ℝ) ≤ sCG cZ 39 ∧ sCG cZ 39 ≤ (-200501224633321 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_sin

theorem thL_41_r_bounds : (-1612177875343278079 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 ≤ (-1612177104656721921 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_41
  have hl : (423953790447836027 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 41 ∧ 11416334 / 100000 * Real.log 41 ≤ (84790758104831283 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_41_eq : (11416334 / 100000 * Real.log 41) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 + π) + ((67 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_41_cos_r : (987032503316651 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) ≤ (987032580385307 / 1000000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(161217749 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) (-(161217749 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 - (-(161217749 / 1000000000 : ℝ))| ≤ (385343278079 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 - (-(161217749 / 1000000000 : ℝ)))]

theorem thL_41_sin_r : (-160520321761077 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) ≤ (-8026012234621 / 50000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (161217749 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((12981339512660465044537167091112590808283017631638364720002789448890726092128869890694189735091218994502966271238850559687737 / 80870400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(161217749 / 1000000000 : ℝ)) ∧ Real.sin (-(161217749 / 1000000000 : ℝ)) ≤ -((83213714824746570794177542576893993335790612507301392438650440734865249683894721503268452081803882411263 / 518400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270) (-(161217749 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 - (-(161217749 / 1000000000 : ℝ))| ≤ (385343278079 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 41) 270 - (-(161217749 / 1000000000 : ℝ)))]

theorem thL_41_cos : (-987032580385307 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 41) ∧ Real.cos (11416334 / 100000 * Real.log 41) ≤ (-987032503316651 / 1000000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_41_sin : (8026012234621 / 50000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 41) ∧ Real.sin (11416334 / 100000 * Real.log 41) ≤ (160520321761077 / 1000000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_41 : (-987032580385307 / 1000000000000000 : ℝ) ≤ cCG cZ 41 ∧ cCG cZ 41 ≤ (-987032503316651 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_cos

theorem sCB_41 : (8026012234621 / 50000000000000 : ℝ) ≤ sCG cZ 41 ∧ sCG cZ 41 ≤ (160520321761077 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_sin

theorem thL_42_r_bounds : (-6896918328615430399 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 ≤ (-6896917371384569601 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_42
  have hl : (213352423710961323 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 42 ∧ 11416334 / 100000 * Real.log 42 ≤ (8534096949965029 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_42_eq : (11416334 / 100000 * Real.log 42) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) + ((68 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_42_cos_r : (106450834908581 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) ≤ (42580337792439 / 50000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(137938357 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) (-(137938357 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 - (-(137938357 / 250000000 : ℝ))| ≤ (478615430399 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 - (-(137938357 / 250000000 : ℝ)))]

theorem thL_42_sin_r : (-524181303318291 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) ≤ (-524181226739751 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (137938357 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((48638696079049209666781679098464206530836663080239078853245703551446917668190773055452155363108667828363553088011533957 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(137938357 / 250000000 : ℝ)) ∧ Real.sin (-(137938357 / 250000000 : ℝ)) ≤ -((4988584213235145100238064419554662122436309795279135660969055301020541277452349365366944818310745107 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272) (-(137938357 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 - (-(137938357 / 250000000 : ℝ))| ≤ (478615430399 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 42) 272 - (-(137938357 / 250000000 : ℝ)))]

theorem thL_42_cos : (106450834908581 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 42) ∧ Real.cos (11416334 / 100000 * Real.log 42) ≤ (42580337792439 / 50000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_42_sin : (-524181303318291 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 42) ∧ Real.sin (11416334 / 100000 * Real.log 42) ≤ (-524181226739751 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_42 : (106450834908581 / 125000000000000 : ℝ) ≤ cCG cZ 42 ∧ cCG cZ 42 ≤ (42580337792439 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_cos

theorem sCB_42 : (-524181303318291 / 1000000000000000 : ℝ) ≤ sCG cZ 42 ∧ sCG cZ 42 ≤ (-524181226739751 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_sin

theorem thL_43_r_bounds : (56377038254011104979 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 ≤ (56377045945988895021 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_43
  have hl : (429391167598130739 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 43 ∧ 11416334 / 100000 * Real.log 43 ≤ (214695583837233333 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_43_eq : (11416334 / 100000 * Real.log 43) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 + π / 2) + ((68 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_43_cos_r : (845246259387377 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) ≤ (211311584077327 / 250000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (563770421 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) (563770421 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 - (563770421 / 1000000000 : ℝ)| ≤ (3845988895021 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 - (563770421 / 1000000000 : ℝ))]

theorem thL_43_sin_r : (13359422116703 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) ≤ (534376961587993 / 1000000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (563770421 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273) (563770421 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 - (563770421 / 1000000000 : ℝ)| ≤ (3845988895021 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 43) 273 - (563770421 / 1000000000 : ℝ))]

theorem thL_43_cos : (-534376961587993 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 43) ∧ Real.cos (11416334 / 100000 * Real.log 43) ≤ (-13359422116703 / 25000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_43_sin : (845246259387377 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 43) ∧ Real.sin (11416334 / 100000 * Real.log 43) ≤ (211311584077327 / 250000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_43 : (-534376961587993 / 1000000000000000 : ℝ) ≤ cCG cZ 43 ∧ cCG cZ 43 ≤ (-13359422116703 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_cos

theorem sCB_43 : (845246259387377 / 1000000000000000 : ℝ) ≤ sCG cZ 43 ∧ sCG cZ 43 ≤ (211311584077327 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_sin

theorem thL_44_r_bounds : (186951658408949153 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 ≤ (186951965591050847 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_44
  have hl : (432015727783652353 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 44 ∧ 11416334 / 100000 * Real.log 44 ≤ (432015727859994333 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_44_eq : (11416334 / 100000 * Real.log 44) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 + π + π / 2) + ((68 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_44_cos_r : (998907942285851 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) ≤ (998908019081377 / 1000000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (46737953 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) (46737953 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 - (46737953 / 1000000000 : ℝ)| ≤ (153591050847 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 - (46737953 / 1000000000 : ℝ))]

theorem thL_44_sin_r : (11680225111881 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) ≤ (46720977243051 / 1000000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (46737953 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275) (46737953 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 - (46737953 / 1000000000 : ℝ)| ≤ (153591050847 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 44) 275 - (46737953 / 1000000000 : ℝ))]

theorem thL_44_cos : (11680225111881 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 44) ∧ Real.cos (11416334 / 100000 * Real.log 44) ≤ (46720977243051 / 1000000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_44_sin : (-998908019081377 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 44) ∧ Real.sin (11416334 / 100000 * Real.log 44) ≤ (-998907942285851 / 1000000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_44 : (11680225111881 / 250000000000000 : ℝ) ≤ cCG cZ 44 ∧ cCG cZ 44 ≤ (46720977243051 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_cos

theorem sCB_44 : (-998908019081377 / 1000000000000000 : ℝ) ≤ sCG cZ 44 ∧ sCG cZ 44 ≤ (-998907942285851 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_sin

theorem thL_46_r_bounds : (40911061864310085267 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 ≤ (40911069535689914733 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_46
  have hl : (437090489467624361 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 46 ∧ 11416334 / 100000 * Real.log 46 ≤ (437090489543975923 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_46_eq : (11416334 / 100000 * Real.log 46) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 + π) + ((69 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_46_cos_r : (917474922138899 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) ≤ (114684374856593 / 125000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (409110657 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) (409110657 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 - (409110657 / 1000000000 : ℝ)| ≤ (3835689914733 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 - (409110657 / 1000000000 : ℝ))]

theorem thL_46_sin_r : (397793497114893 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) ≤ (198896786914347 / 500000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (409110657 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278) (409110657 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 - (409110657 / 1000000000 : ℝ)| ≤ (3835689914733 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 46) 278 - (409110657 / 1000000000 : ℝ))]

theorem thL_46_cos : (-114684374856593 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 46) ∧ Real.cos (11416334 / 100000 * Real.log 46) ≤ (-917474922138899 / 1000000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_46_sin : (-198896786914347 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 46) ∧ Real.sin (11416334 / 100000 * Real.log 46) ≤ (-397793497114893 / 1000000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_46 : (-114684374856593 / 125000000000000 : ℝ) ≤ cCG cZ 46 ∧ cCG cZ 46 ≤ (-917474922138899 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_cos

theorem sCB_46 : (-198896786914347 / 500000000000000 : ℝ) ≤ sCG cZ 46 ∧ sCG cZ 46 ≤ (-397793497114893 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_sin

theorem thL_47_r_bounds : (-1386309080982966929 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 ≤ (-1386308699017033071 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_47
  have hl : (21977285484318723 / 50000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 47 ∧ 11416334 / 100000 * Real.log 47 ≤ (439545709762729817 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_47_eq : (11416334 / 100000 * Real.log 47) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) + ((70 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_47_cos_r : (480904259679043 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) ≤ (38472343830051 / 40000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(138630889 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) (-(138630889 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 - (-(138630889 / 500000000 : ℝ))| ≤ (190982966929 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 - (-(138630889 / 500000000 : ℝ)))]

theorem thL_47_sin_r : (-273723070867549 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) ≤ (-273722994474361 / 1000000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (138630889 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((29723755194634400489383079415499508842576838300526469118613406700524406084839666557823039029452013207463226466813304785967 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(138630889 / 500000000 : ℝ)) ∧ Real.sin (-(138630889 / 500000000 : ℝ)) ≤ -((5335032983652328113857980989283178059475842070356486060692498363405109687388620607434694977805224240711 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280) (-(138630889 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 - (-(138630889 / 500000000 : ℝ))| ≤ (190982966929 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 47) 280 - (-(138630889 / 500000000 : ℝ)))]

theorem thL_47_cos : (480904259679043 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 47) ∧ Real.cos (11416334 / 100000 * Real.log 47) ≤ (38472343830051 / 40000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_47_sin : (-273723070867549 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 47) ∧ Real.sin (11416334 / 100000 * Real.log 47) ≤ (-273722994474361 / 1000000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_47 : (480904259679043 / 500000000000000 : ℝ) ≤ cCG cZ 47 ∧ cCG cZ 47 ≤ (38472343830051 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_cos

theorem sCB_47 : (-273723070867549 / 1000000000000000 : ℝ) ≤ sCG cZ 47 ∧ sCG cZ 47 ≤ (-273722994474361 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_sin

theorem thL_48_r_bounds : (111093873883860798993 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 ≤ (111093889316139201007 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_48
  have hl : (220974618599392627 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 48 ∧ 11416334 / 100000 * Real.log 48 ≤ (441949237275143881 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_48_eq : (11416334 / 100000 * Real.log 48) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 + π / 2) + ((70 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_48_cos_r : (106206619582573 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) ≤ (424826516911889 / 500000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (17358419 / 31250000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) (17358419 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 - (17358419 / 31250000 : ℝ)| ≤ (7716139201007 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 - (17358419 / 31250000 : ℝ))]

theorem thL_48_sin_r : (527342153619381 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) ≤ (527342230780851 / 1000000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (17358419 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281) (17358419 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 - (17358419 / 31250000 : ℝ)| ≤ (7716139201007 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 48) 281 - (17358419 / 31250000 : ℝ))]

theorem thL_48_cos : (-527342230780851 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 48) ∧ Real.cos (11416334 / 100000 * Real.log 48) ≤ (-527342153619381 / 1000000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_48_sin : (106206619582573 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 48) ∧ Real.sin (11416334 / 100000 * Real.log 48) ≤ (424826516911889 / 500000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_48 : (-527342230780851 / 1000000000000000 : ℝ) ≤ cCG cZ 48 ∧ cCG cZ 48 ≤ (-527342153619381 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_cos

theorem sCB_48 : (106206619582573 / 125000000000000 : ℝ) ≤ sCG cZ 48 ∧ sCG cZ 48 ≤ (424826516911889 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_sin

theorem thL_49_r_bounds : (-23215658967412275791 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 ≤ (-23215651232587724209 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_49
  have hl : (444303203894268413 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 49 ∧ 11416334 / 100000 * Real.log 49 ≤ (222151601985314933 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_49_eq : (11416334 / 100000 * Real.log 49) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 + π + π / 2) + ((70 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_49_cos_r : (243293111858939 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) ≤ (973172524784003 / 1000000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(232156551 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) (-(232156551 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 - (-(232156551 / 1000000000 : ℝ))| ≤ (3867412275791 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 - (-(232156551 / 1000000000 : ℝ)))]

theorem thL_49_sin_r : (-115038395845421 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) ≤ (-46015342868519 / 200000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (232156551 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((76569543403963905539568607526223736960105670454372531905456847124971535517909632613670301485022851329627014737788223733041 / 332800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(232156551 / 1000000000 : ℝ)) ∧ Real.sin (-(232156551 / 1000000000 : ℝ)) ≤ -((10307438535148987243232497347243184057589149569541289263744967204284849726076263432684219745088633077739 / 44800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283) (-(232156551 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 - (-(232156551 / 1000000000 : ℝ))| ≤ (3867412275791 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 49) 283 - (-(232156551 / 1000000000 : ℝ)))]

theorem thL_49_cos : (-115038395845421 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 49) ∧ Real.cos (11416334 / 100000 * Real.log 49) ≤ (-46015342868519 / 200000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_49_sin : (-973172524784003 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 49) ∧ Real.sin (11416334 / 100000 * Real.log 49) ≤ (-243293111858939 / 250000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_49 : (-115038395845421 / 500000000000000 : ℝ) ≤ cCG cZ 49 ∧ cCG cZ 49 ≤ (-46015342868519 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_cos

theorem sCB_49 : (-973172524784003 / 1000000000000000 : ℝ) ≤ sCG cZ 49 ∧ sCG cZ 49 ≤ (-243293111858939 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_sin

theorem thL_51_r_bounds : (-18870147630543195011 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 ≤ (-18870143769456804989 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_51
  have hl : (89774069302317053 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 51 ∧ 11416334 / 100000 * Real.log 51 ≤ (448870346587951297 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_51_eq : (11416334 / 100000 * Real.log 51) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 + π) + ((71 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_51_cos_r : (464812388194119 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) ≤ (1815673542207 / 1953125000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(188701457 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) (-(188701457 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 - (-(188701457 / 500000000 : ℝ))| ≤ (1930543195011 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 - (-(188701457 / 500000000 : ℝ)))]

theorem thL_51_sin_r : (-368507437909511 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) ≤ (-368507360687781 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (188701457 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40016448806964554089590844690078639720892286156435023996740586342304687630827289688071525068250493125983164076230901947751 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(188701457 / 500000000 : ℝ)) ∧ Real.sin (-(188701457 / 500000000 : ℝ)) ≤ -((1026062789922166644564150968344027330819502891760238582728419427797402872199468059070989827344082580601 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286) (-(188701457 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 - (-(188701457 / 500000000 : ℝ))| ≤ (1930543195011 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 51) 286 - (-(188701457 / 500000000 : ℝ)))]

theorem thL_51_cos : (-1815673542207 / 1953125000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 51) ∧ Real.cos (11416334 / 100000 * Real.log 51) ≤ (-464812388194119 / 500000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_51_sin : (368507360687781 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 51) ∧ Real.sin (11416334 / 100000 * Real.log 51) ≤ (368507437909511 / 1000000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_51 : (-1815673542207 / 1953125000000 : ℝ) ≤ cCG cZ 51 ∧ cCG cZ 51 ≤ (-464812388194119 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_cos

theorem sCB_51 : (368507360687781 / 1000000000000000 : ℝ) ≤ sCG cZ 51 ∧ sCG cZ 51 ≤ (368507437909511 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_sin

theorem thL_52_r_bounds : (26863425832896171901 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 ≤ (26863433567103828099 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_52
  have hl : (451087180049438479 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 52 ∧ 11416334 / 100000 * Real.log 52 ≤ (14096474378931449 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_52_eq : (11416334 / 100000 * Real.log 52) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 + π + π / 2) + ((71 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_52_cos_r : (964134234718951 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) ≤ (964134312061029 / 1000000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (268634297 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) (268634297 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 - (268634297 / 1000000000 : ℝ)| ≤ (3867103828099 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 - (268634297 / 1000000000 : ℝ))]

theorem thL_52_sin_r : (265414924876149 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) ≤ (265415002218227 / 1000000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (268634297 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287) (268634297 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 - (268634297 / 1000000000 : ℝ)| ≤ (3867103828099 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 52) 287 - (268634297 / 1000000000 : ℝ))]

theorem thL_52_cos : (265414924876149 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 52) ∧ Real.cos (11416334 / 100000 * Real.log 52) ≤ (265415002218227 / 1000000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_52_sin : (-964134312061029 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 52) ∧ Real.sin (11416334 / 100000 * Real.log 52) ≤ (-964134234718951 / 1000000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_52 : (265414924876149 / 1000000000000000 : ℝ) ≤ cCG cZ 52 ∧ cCG cZ 52 ≤ (265415002218227 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_cos

theorem sCB_52 : (-964134312061029 / 1000000000000000 : ℝ) ≤ sCG cZ 52 ∧ sCG cZ 52 ≤ (-964134234718951 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_sin

theorem thL_53_r_bounds : (-139670567092238391783 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 ≤ (-139670551707761608217 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_53
  have hl : (453261785608263931 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 53 ∧ 11416334 / 100000 * Real.log 53 ≤ (453261785684633443 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_53_eq : (11416334 / 100000 * Real.log 53) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 + π / 2) + ((72 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_53_cos_r : (765902268008083 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) ≤ (382951172479279 / 500000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(698352797 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) (-(698352797 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 - (-(698352797 / 1000000000 : ℝ))| ≤ (7692238391783 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 - (-(698352797 / 1000000000 : ℝ)))]

theorem thL_53_sin_r : (-321478500976317 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) ≤ (-32147846251437 / 50000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (698352797 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4003706385166045723719109061848105030799944192117319940321234556326460068842414121727670970350601589258417604409509584267968077 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(698352797 / 1000000000 : ℝ)) ∧ Real.sin (-(698352797 / 1000000000 : ℝ)) ≤ -((25664784520234929911361940727777374539653274507312267247650385359670069167177407136394676584551580950417947 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289) (-(698352797 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 - (-(698352797 / 1000000000 : ℝ))| ≤ (7692238391783 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 53) 289 - (-(698352797 / 1000000000 : ℝ)))]

theorem thL_53_cos : (32147846251437 / 50000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 53) ∧ Real.cos (11416334 / 100000 * Real.log 53) ≤ (321478500976317 / 500000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_53_sin : (765902268008083 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 53) ∧ Real.sin (11416334 / 100000 * Real.log 53) ≤ (382951172479279 / 500000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_53 : (32147846251437 / 50000000000000 : ℝ) ≤ cCG cZ 53 ∧ cCG cZ 53 ≤ (321478500976317 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_cos

theorem sCB_53 : (765902268008083 / 1000000000000000 : ℝ) ≤ sCG cZ 53 ∧ sCG cZ 53 ≤ (382951172479279 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_sin

theorem thL_54_r_bounds : (-1351928265062384233 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 ≤ (-1351927494937615767 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_54
  have hl : (113848935486163831 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 54 ∧ 11416334 / 100000 * Real.log 54 ≤ (227697871010513129 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_54_eq : (11416334 / 100000 * Real.log 54) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 + π) + ((72 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_54_cos_r : (990875326887071 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) ≤ (990875403899549 / 1000000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(33798197 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) (-(33798197 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 - (-(33798197 / 250000000 : ℝ))| ≤ (385062384233 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 - (-(33798197 / 250000000 : ℝ)))]

theorem thL_54_sin_r : (-134781380897071 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) ≤ (-134781303884593 / 1000000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (33798197 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1786619898505789017061152924946124885567902005715958403630308989913842284335892892032282637273037759180559618768606611 / 13255691528320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(33798197 / 250000000 : ℝ)) ∧ Real.sin (-(33798197 / 250000000 : ℝ)) ≤ -((1282701465593899807113125602672999368206048541846618801216065647440976087849730504110087860141747347 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290) (-(33798197 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 - (-(33798197 / 250000000 : ℝ))| ≤ (385062384233 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 54) 290 - (-(33798197 / 250000000 : ℝ)))]

theorem thL_54_cos : (-990875403899549 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 54) ∧ Real.cos (11416334 / 100000 * Real.log 54) ≤ (-990875326887071 / 1000000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_54_sin : (134781303884593 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 54) ∧ Real.sin (11416334 / 100000 * Real.log 54) ≤ (134781380897071 / 1000000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_54 : (-990875403899549 / 1000000000000000 : ℝ) ≤ cCG cZ 54 ∧ cCG cZ 54 ≤ (-990875326887071 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_cos

theorem sCB_54 : (134781303884593 / 1000000000000000 : ℝ) ≤ sCG cZ 54 ∧ sCG cZ 54 ≤ (134781380897071 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_sin

theorem thL_56_r_bounds : (-69573008060216556561 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 ≤ (-69573000339783443439 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_56
  have hl : (57443449208891699 / 125000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 56 ∧ 11416334 / 100000 * Real.log 56 ≤ (735276149996011 / 1600000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_56_eq : (11416334 / 100000 * Real.log 56) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 + π / 2) + ((73 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_56_cos_r : (153517190053231 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) ≤ (383793013748669 / 500000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(347865021 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) (-(347865021 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 - (-(347865021 / 500000000 : ℝ))| ≤ (3860216556561 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 - (-(347865021 / 500000000 : ℝ)))]

theorem thL_56_sin_r : (-320473009446873 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) ≤ (-640945941687977 / 1000000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (347865021 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((286422734942799865726904580079937287981604631258678371080988052644861009186666261864542611824109845762692187986237870761 / 446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(347865021 / 500000000 : ℝ)) ∧ Real.sin (-(347865021 / 500000000 : ℝ)) ≤ -((22032518072473670543498695492564888498912517253754993394157980270321091948740878462707529595179585437 / 34375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293) (-(347865021 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 - (-(347865021 / 500000000 : ℝ))| ≤ (3860216556561 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 56) 293 - (-(347865021 / 500000000 : ℝ)))]

theorem thL_56_cos : (640945941687977 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 56) ∧ Real.cos (11416334 / 100000 * Real.log 56) ≤ (320473009446873 / 500000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_56_sin : (153517190053231 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 56) ∧ Real.sin (11416334 / 100000 * Real.log 56) ≤ (383793013748669 / 500000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_56 : (640945941687977 / 1000000000000000 : ℝ) ≤ cCG cZ 56 ∧ cCG cZ 56 ≤ (320473009446873 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_cos

theorem sCB_56 : (153517190053231 / 200000000000000 : ℝ) ≤ sCG cZ 56 ∧ sCG cZ 56 ≤ (383793013748669 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_sin

theorem thL_57_r_bounds : (-24588356831103205509 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 ≤ (-24588349168896794491 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_57
  have hl : (230784118254694287 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 57 ∧ 11416334 / 100000 * Real.log 57 ≤ (115392059146440707 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_57_eq : (11416334 / 100000 * Real.log 57) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 + π) + ((73 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_57_cos_r : (484961301121509 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) ≤ (969922678865083 / 1000000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(24588353 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) (-(24588353 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 - (-(24588353 / 100000000 : ℝ))| ≤ (3831103205509 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 - (-(24588353 / 100000000 : ℝ)))]

theorem thL_57_sin_r : (-60853353436507 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) ≤ (-243413337123963 / 1000000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (24588353 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((21653430740456121339096325735062184216077252278704985076131311386571253599662833656387782126608926179195839262839 / 88957440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(24588353 / 100000000 : ℝ)) ∧ Real.sin (-(24588353 / 100000000 : ℝ)) ≤ -((97162830245636441136436544484392598700552858426263175965644766324583033347954174337880792464703 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294) (-(24588353 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 - (-(24588353 / 100000000 : ℝ))| ≤ (3831103205509 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 57) 294 - (-(24588353 / 100000000 : ℝ)))]

theorem thL_57_cos : (-969922678865083 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 57) ∧ Real.cos (11416334 / 100000 * Real.log 57) ≤ (-484961301121509 / 500000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_57_sin : (243413337123963 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 57) ∧ Real.sin (11416334 / 100000 * Real.log 57) ≤ (60853353436507 / 250000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_57 : (-969922678865083 / 1000000000000000 : ℝ) ≤ cCG cZ 57 ∧ cCG cZ 57 ≤ (-484961301121509 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_cos

theorem sCB_57 : (243413337123963 / 1000000000000000 : ℝ) ≤ sCG cZ 57 ∧ sCG cZ 57 ≤ (60853353436507 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_sin

theorem thL_58_r_bounds : (6752781561248733027 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 ≤ (6752785078751266973 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_58
  have hl : (463553735943525721 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 58 ∧ 11416334 / 100000 * Real.log 58 ≤ (14486054250976647 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_58_eq : (11416334 / 100000 * Real.log 58) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 + π + π / 2) + ((73 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_58_cos_r : (246445935491563 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) ≤ (123222978737977 / 125000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (168819583 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) (168819583 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 - (168819583 / 1000000000 : ℝ)| ≤ (1758751266973 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 - (168819583 / 1000000000 : ℝ))]

theorem thL_58_sin_r : (16801878648659 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) ≤ (84009437212077 / 500000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (168819583 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295) (168819583 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 - (168819583 / 1000000000 : ℝ)| ≤ (1758751266973 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 58) 295 - (168819583 / 1000000000 : ℝ))]

theorem thL_58_cos : (16801878648659 / 100000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 58) ∧ Real.cos (11416334 / 100000 * Real.log 58) ≤ (84009437212077 / 500000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_58_sin : (-123222978737977 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 58) ∧ Real.sin (11416334 / 100000 * Real.log 58) ≤ (-246445935491563 / 250000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_58 : (16801878648659 / 100000000000000 : ℝ) ≤ cCG cZ 58 ∧ cCG cZ 58 ≤ (84009437212077 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_cos

theorem sCB_58 : (-123222978737977 / 125000000000000 : ℝ) ≤ sCG cZ 58 ∧ sCG cZ 58 ≤ (-246445935491563 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_sin

theorem thL_59_r_bounds : (13739520446462167661 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 ≤ (13739522903537832339 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_59
  have hl : (232752646774573943 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 59 ∧ 11416334 / 100000 * Real.log 59 ≤ (93101058729457973 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_59_eq : (11416334 / 100000 * Real.log 59) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) + ((74 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_59_cos_r : (34109738939751 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) ≤ (852743571778387 / 1000000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (549580867 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) (549580867 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 - (549580867 / 1000000000 : ℝ)| ≤ (1228537832339 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 - (549580867 / 1000000000 : ℝ))]

theorem thL_59_sin_r : (261164906364079 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) ≤ (522329911011253 / 1000000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (549580867 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296) (549580867 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 - (549580867 / 1000000000 : ℝ)| ≤ (1228537832339 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 59) 296 - (549580867 / 1000000000 : ℝ))]

theorem thL_59_cos : (34109738939751 / 40000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 59) ∧ Real.cos (11416334 / 100000 * Real.log 59) ≤ (852743571778387 / 1000000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_59_sin : (261164906364079 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 59) ∧ Real.sin (11416334 / 100000 * Real.log 59) ≤ (522329911011253 / 1000000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_59 : (34109738939751 / 40000000000000 : ℝ) ≤ cCG cZ 59 ∧ cCG cZ 59 ≤ (852743571778387 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_cos

theorem sCB_59 : (261164906364079 / 500000000000000 : ℝ) ≤ sCG cZ 59 ∧ sCG cZ 59 ≤ (522329911011253 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_sin

theorem thL_61_r_bounds : (-35701108570564185023 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 ≤ (-35701096829435814977 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_61
  have hl : (234655545313432739 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 61 ∧ 11416334 / 100000 * Real.log 61 ≤ (469311090743379731 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_61_eq : (11416334 / 100000 * Real.log 61) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 + π + π / 2) + ((74 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_61_cos_r : (93694552094723 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) ≤ (234236409589631 / 250000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(357011027 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) (-(357011027 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 - (-(357011027 / 1000000000 : ℝ))| ≤ (5870564185023 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 - (-(357011027 / 1000000000 : ℝ)))]

theorem thL_61_sin_r : (-13979014088341 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) ≤ (-8736880869931 / 25000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (357011027 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2176189921728557119167547652767193523113086935264458224169659500866503394834178093524401837704260369687223165653923880528279267 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(357011027 / 1000000000 : ℝ)) ∧ Real.sin (-(357011027 / 1000000000 : ℝ)) ≤ -((13949935395695869157495895167312837875324716170429326843668397422595938820629108094560384798236475872915477 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299) (-(357011027 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 - (-(357011027 / 1000000000 : ℝ))| ≤ (5870564185023 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 61) 299 - (-(357011027 / 1000000000 : ℝ)))]

theorem thL_61_cos : (-13979014088341 / 40000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 61) ∧ Real.cos (11416334 / 100000 * Real.log 61) ≤ (-8736880869931 / 25000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_61_sin : (-234236409589631 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 61) ∧ Real.sin (11416334 / 100000 * Real.log 61) ≤ (-93694552094723 / 100000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_61 : (-13979014088341 / 40000000000000 : ℝ) ≤ cCG cZ 61 ∧ cCG cZ 61 ≤ (-8736880869931 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_cos

theorem sCB_61 : (-234236409589631 / 250000000000000 : ℝ) ≤ sCG cZ 61 ∧ sCG cZ 61 ≤ (-93694552094723 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_sin

theorem thL_62_r_bounds : (-142904080726943541 / 2000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 ≤ (-142903831273056459 / 2000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_62
  have hl : (235583722999052757 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 62 ∧ 11416334 / 100000 * Real.log 62 ≤ (94233489224546099 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_62_eq : (11416334 / 100000 * Real.log 62) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) + ((75 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_62_cos_r : (62340520681973 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) ≤ (997448455638513 / 1000000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(35725989 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) (-(35725989 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 - (-(35725989 / 500000000 : ℝ))| ≤ (124726943541 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 - (-(35725989 / 500000000 : ℝ)))]

theorem thL_62_sin_r : (-71391257570169 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) ≤ (-8923891605403 / 125000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (35725989 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2454072335230189684448869825049559405202146645788676169939764597192476001981288475205526963186454389567921859229088213 / 34375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(35725989 / 500000000 : ℝ)) ∧ Real.sin (-(35725989 / 500000000 : ℝ)) ≤ -((17178506346611327791142039882451546902656841069175604474957502876075940850435493175912253214622754131 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300) (-(35725989 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 - (-(35725989 / 500000000 : ℝ))| ≤ (124726943541 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 62) 300 - (-(35725989 / 500000000 : ℝ)))]

theorem thL_62_cos : (62340520681973 / 62500000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 62) ∧ Real.cos (11416334 / 100000 * Real.log 62) ≤ (997448455638513 / 1000000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_62_sin : (-71391257570169 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 62) ∧ Real.sin (11416334 / 100000 * Real.log 62) ≤ (-8923891605403 / 125000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_62 : (62340520681973 / 62500000000000 : ℝ) ≤ cCG cZ 62 ∧ cCG cZ 62 ≤ (997448455638513 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_cos

theorem sCB_62 : (-71391257570169 / 1000000000000000 : ℝ) ≤ sCG cZ 62 ∧ sCG cZ 62 ≤ (-8923891605403 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_sin

theorem thL_63_r_bounds : (36880808119003722053 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 ≤ (36880834680996277947 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_63
  have hl : (472994098405858901 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 63 ∧ 11416334 / 100000 * Real.log 63 ≤ (472994098537966169 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_63_eq : (11416334 / 100000 * Real.log 63) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 + π / 2) + ((75 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_63_cos_r : (30720175692369 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) ≤ (245761438741443 / 250000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (184404107 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) (184404107 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 - (184404107 / 1000000000 : ℝ)| ≤ (13280996277947 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 - (184404107 / 1000000000 : ℝ))]

theorem thL_63_sin_r : (183360709667881 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) ≤ (36672168495569 / 200000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (184404107 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301) (184404107 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 - (184404107 / 1000000000 : ℝ)| ≤ (13280996277947 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 63) 301 - (184404107 / 1000000000 : ℝ))]

theorem thL_63_cos : (-36672168495569 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 63) ∧ Real.cos (11416334 / 100000 * Real.log 63) ≤ (-183360709667881 / 1000000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_63_sin : (30720175692369 / 31250000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 63) ∧ Real.sin (11416334 / 100000 * Real.log 63) ≤ (245761438741443 / 250000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_63 : (-36672168495569 / 200000000000000 : ℝ) ≤ cCG cZ 63 ∧ cCG cZ 63 ≤ (-183360709667881 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_cos

theorem sCB_63 : (30720175692369 / 31250000000000 : ℝ) ≤ sCG cZ 63 ∧ sCG cZ 63 ≤ (245761438741443 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_sin

theorem thL_64_r_bounds : (41149274341291099103 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 ≤ (41149288258708900897 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_64
  have hl : (47479198343547169 / 100000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 64 ∧ 11416334 / 100000 * Real.log 64 ≤ (474791983574490341 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_64_eq : (11416334 / 100000 * Real.log 64) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 + π) + ((75 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_64_cos_r : (916524682366339 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) ≤ (114565602692571 / 125000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (411492813 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) (411492813 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 - (411492813 / 1000000000 : ℝ)| ≤ (6958708900897 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 - (411492813 / 1000000000 : ℝ))]

theorem thL_64_sin_r : (99994475906801 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) ≤ (79995608560277 / 200000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (411492813 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302) (411492813 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 - (411492813 / 1000000000 : ℝ)| ≤ (6958708900897 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 64) 302 - (411492813 / 1000000000 : ℝ))]

theorem thL_64_cos : (-114565602692571 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 64) ∧ Real.cos (11416334 / 100000 * Real.log 64) ≤ (-916524682366339 / 1000000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_64_sin : (-79995608560277 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 64) ∧ Real.sin (11416334 / 100000 * Real.log 64) ≤ (-99994475906801 / 250000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_64 : (-114565602692571 / 125000000000000 : ℝ) ≤ cCG cZ 64 ∧ cCG cZ 64 ≤ (-916524682366339 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_cos

theorem sCB_64 : (-79995608560277 / 200000000000000 : ℝ) ≤ sCG cZ 64 ∧ sCG cZ 64 ≤ (-99994475906801 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_sin

theorem thL_66_r_bounds : (9786192726219709407 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 ≤ (9786194623780290593 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_66
  have hl : (478304978763746149 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 66 ∧ 11416334 / 100000 * Real.log 66 ≤ (119576244728768863 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_66_eq : (11416334 / 100000 * Real.log 66) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) + ((76 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_66_cos_r : (354437071699777 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) ≤ (708874295315091 / 1000000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (391447747 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) (391447747 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 - (391447747 / 500000000 : ℝ)| ≤ (948780290593 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 - (391447747 / 500000000 : ℝ))]

theorem thL_66_sin_r : (352667419096937 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) ≤ (176333747501347 / 250000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (391447747 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304) (391447747 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 - (391447747 / 500000000 : ℝ)| ≤ (948780290593 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 66) 304 - (391447747 / 500000000 : ℝ))]

theorem thL_66_cos : (354437071699777 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 66) ∧ Real.cos (11416334 / 100000 * Real.log 66) ≤ (708874295315091 / 1000000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_66_sin : (352667419096937 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 66) ∧ Real.sin (11416334 / 100000 * Real.log 66) ≤ (176333747501347 / 250000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_66 : (354437071699777 / 500000000000000 : ℝ) ≤ cCG cZ 66 ∧ cCG cZ 66 ≤ (708874295315091 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_cos

theorem sCB_66 : (352667419096937 / 500000000000000 : ℝ) ≤ sCG cZ 66 ∧ sCG cZ 66 ≤ (176333747501347 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_sin

theorem thL_67_r_bounds : (-32096146533646275781 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 ≤ (-32096138666353724219 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_67
  have hl : (24001087653454757 / 50000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 67 ∧ 11416334 / 100000 * Real.log 67 ≤ (480021753225911291 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_67_eq : (11416334 / 100000 * Real.log 67) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 + π) + ((76 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_67_cos_r : (6407567029137 / 8000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) ≤ (800946035998197 / 1000000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(160480713 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) (-(160480713 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 - (-(160480713 / 250000000 : ℝ))| ≤ (3933646275781 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 - (-(160480713 / 250000000 : ℝ)))]

theorem thL_67_sin_r : (-9355261351473 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) ≤ (-149684142286979 / 250000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (160480713 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((32661186461812030231970129374420050089306418950260001991948173845100010729458996978367307850095439450536632838019253 / 54550170898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(160480713 / 250000000 : ℝ)) ∧ Real.sin (-(160480713 / 250000000 : ℝ)) ≤ -((70347170840766617732498091426577158224672083666615377080534510507279007674212870822383092914472823 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306) (-(160480713 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 - (-(160480713 / 250000000 : ℝ))| ≤ (3933646275781 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 67) 306 - (-(160480713 / 250000000 : ℝ)))]

theorem thL_67_cos : (-800946035998197 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 67) ∧ Real.cos (11416334 / 100000 * Real.log 67) ≤ (-6407567029137 / 8000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_67_sin : (149684142286979 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 67) ∧ Real.sin (11416334 / 100000 * Real.log 67) ≤ (9355261351473 / 15625000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_67 : (-800946035998197 / 1000000000000000 : ℝ) ≤ cCG cZ 67 ∧ cCG cZ 67 ≤ (-6407567029137 / 8000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_cos

theorem sCB_67 : (149684142286979 / 250000000000000 : ℝ) ≤ sCG cZ 67 ∧ sCG cZ 67 ≤ (9355261351473 / 15625000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_sin

theorem thL_68_r_bounds : (-104275916467676621029 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 ≤ (-104275883932323378971 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_68
  have hl : (481713092743694879 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 68 ∧ 11416334 / 100000 * Real.log 68 ≤ (481713092905603303 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_68_eq : (11416334 / 100000 * Real.log 68) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 + π + π / 2) + ((76 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_68_cos_r : (867132826168991 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) ≤ (4335664944233 / 5000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(521379501 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) (-(521379501 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 - (-(521379501 / 1000000000 : ℝ))| ≤ (16267676621029 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 - (-(521379501 / 1000000000 : ℝ)))]

theorem thL_68_sin_r : (-498076903441509 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) ≤ (-124519185191177 / 250000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (521379501 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((12763517412485858747372809231485743112539247754972102089092965550703060004288349320419099855847402889228521986570451827602607 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(521379501 / 1000000000 : ℝ)) ∧ Real.sin (-(521379501 / 1000000000 : ℝ)) ≤ -((245452257932403711388143401223038087380889690215884253166731151101446021800428526094877721960408009581179 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307) (-(521379501 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 - (-(521379501 / 1000000000 : ℝ))| ≤ (16267676621029 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 68) 307 - (-(521379501 / 1000000000 : ℝ)))]

theorem thL_68_cos : (-498076903441509 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 68) ∧ Real.cos (11416334 / 100000 * Real.log 68) ≤ (-124519185191177 / 250000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_68_sin : (-4335664944233 / 5000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 68) ∧ Real.sin (11416334 / 100000 * Real.log 68) ≤ (-867132826168991 / 1000000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_68 : (-498076903441509 / 1000000000000000 : ℝ) ≤ cCG cZ 68 ∧ cCG cZ 68 ≤ (-124519185191177 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_cos

theorem sCB_68 : (-4335664944233 / 5000000000000 : ℝ) ≤ sCG cZ 68 ∧ sCG cZ 68 ≤ (-867132826168991 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_sin

theorem thL_69_r_bounds : (-10638205211725631929 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 ≤ (-10638201038274368071 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_69
  have hl : (241689870222328749 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 69 ∧ 11416334 / 100000 * Real.log 69 ≤ (15105616894103037 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_69_eq : (11416334 / 100000 * Real.log 69) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) + ((77 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_69_cos_r : (182164153106111 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) ≤ (22770523311717 / 25000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(136169 / 320000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) (-(136169 / 320000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 - (-(136169 / 320000 : ℝ))| ≤ (2086725631929 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 - (-(136169 / 320000 : ℝ)))]

theorem thL_69_sin_r : (-103200487504873 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) ≤ (-206400891540719 / 500000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (136169 / 320000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((86214239525111852516162938929042140313178979854394540899302151250863151751805819 / 208851380071392929220919296000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(136169 / 320000 : ℝ)) ∧ Real.sin (-(136169 / 320000 : ℝ)) ≤ -((5397025210656509756276080530417827864621068595745784812375575322421 / 13074129862241644707840000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308) (-(136169 / 320000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 - (-(136169 / 320000 : ℝ))| ≤ (2086725631929 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 69) 308 - (-(136169 / 320000 : ℝ)))]

theorem thL_69_cos : (182164153106111 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 69) ∧ Real.cos (11416334 / 100000 * Real.log 69) ≤ (22770523311717 / 25000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_69_sin : (-103200487504873 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 69) ∧ Real.sin (11416334 / 100000 * Real.log 69) ≤ (-206400891540719 / 500000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_69 : (182164153106111 / 200000000000000 : ℝ) ≤ cCG cZ 69 ∧ cCG cZ 69 ≤ (22770523311717 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_cos

theorem sCB_69 : (-103200487504873 / 250000000000000 : ℝ) ≤ sCG cZ 69 ∧ sCG cZ 69 ≤ (-206400891540719 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_sin

theorem thL_71_r_bounds : (-3050892309548110387 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 ≤ (-3050890550451889613 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_71
  have hl : (97328354415247077 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 71 ∧ 11416334 / 100000 * Real.log 71 ≤ (486641772251372763 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_71_eq : (11416334 / 100000 * Real.log 71) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 + π) + ((77 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_71_cos_r : (238455022947143 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) ≤ (238455066924549 / 250000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(305089143 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) (-(305089143 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 - (-(305089143 / 1000000000 : ℝ))| ≤ (879548110387 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 - (-(305089143 / 1000000000 : ℝ)))]

theorem thL_71_sin_r : (-300378290749717 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) ≤ (-150189057420047 / 500000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (305089143 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7697371673541133875450748542931573440869150195815110194709862307613657780953289422764980447109646500241019507085134910993101 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(305089143 / 1000000000 : ℝ)) ∧ Real.sin (-(305089143 / 1000000000 : ℝ)) ≤ -((148026378337329481903429540101936100744886425139728367135417253195980378733859079894293416005832695070153 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310) (-(305089143 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 - (-(305089143 / 1000000000 : ℝ))| ≤ (879548110387 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 71) 310 - (-(305089143 / 1000000000 : ℝ)))]

theorem thL_71_cos : (-238455066924549 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 71) ∧ Real.cos (11416334 / 100000 * Real.log 71) ≤ (-238455022947143 / 250000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_71_sin : (150189057420047 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 71) ∧ Real.sin (11416334 / 100000 * Real.log 71) ≤ (300378290749717 / 1000000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_71 : (-238455066924549 / 250000000000000 : ℝ) ≤ cCG cZ 71 ∧ cCG cZ 71 ≤ (-238455022947143 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_cos

theorem sCB_71 : (150189057420047 / 500000000000000 : ℝ) ≤ sCG cZ 71 ∧ sCG cZ 71 ≤ (300378290749717 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_sin

theorem thL_72_r_bounds : (-55833891971331916417 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 ≤ (-55833856028668083583 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_72
  have hl : (488238488173356189 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 72 ∧ 11416334 / 100000 * Real.log 72 ≤ (488238488352312109 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_72_eq : (11416334 / 100000 * Real.log 72) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 + π + π / 2) + ((77 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_72_cos_r : (240321141545457 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) ≤ (240321186473787 / 250000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(27916937 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) (-(27916937 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 - (-(27916937 / 100000000 : ℝ))| ≤ (17971331916417 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 - (-(27916937 / 100000000 : ℝ)))]

theorem thL_72_sin_r : (-137778680849293 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) ≤ (-137778590992633 / 500000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (27916937 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((24512869476441820582380147630566270202724374937115381637622737352241268656370862887648493926952109816844856825871 / 88957440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(27916937 / 100000000 : ℝ)) ∧ Real.sin (-(27916937 / 100000000 : ℝ)) ≤ -((109993645086597908859543767042854764579094427999354449667872808942798622089633707006882690960487 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311) (-(27916937 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 - (-(27916937 / 100000000 : ℝ))| ≤ (17971331916417 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 72) 311 - (-(27916937 / 100000000 : ℝ)))]

theorem thL_72_cos : (-137778680849293 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 72) ∧ Real.cos (11416334 / 100000 * Real.log 72) ≤ (-137778590992633 / 500000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_72_sin : (-240321186473787 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 72) ∧ Real.sin (11416334 / 100000 * Real.log 72) ≤ (-240321141545457 / 250000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_72 : (-137778680849293 / 500000000000000 : ℝ) ≤ cCG cZ 72 ∧ cCG cZ 72 ≤ (-137778590992633 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_cos

theorem sCB_72 : (-240321186473787 / 250000000000000 : ℝ) ≤ sCG cZ 72 ∧ sCG cZ 72 ≤ (-240321141545457 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_sin

theorem thL_73_r_bounds : (-3440925793470472503 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 ≤ (-3440923506529527497 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_73
  have hl : (244906589948483553 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 73 ∧ 11416334 / 100000 * Real.log 73 ≤ (489813180079485383 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_73_eq : (11416334 / 100000 * Real.log 73) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) + ((78 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_73_cos_r : (192470134754797 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) ≤ (481175428364631 / 500000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(68818493 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) (-(68818493 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 - (-(68818493 / 250000000 : ℝ))| ≤ (1143470472503 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 - (-(68818493 / 250000000 : ℝ)))]

theorem thL_73_sin_r : (-271810695795451 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) ≤ (-10872420513607 / 40000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (68818493 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((25221262674742823951871149207267358455394365424525733895306162834437959075264752622592818956979327775359091805350730093 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(68818493 / 250000000 : ℝ)) ∧ Real.sin (-(68818493 / 250000000 : ℝ)) ≤ -((2586796171768494684648757333623428586649870526478072481548864167347893964458106590251003872462205243 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312) (-(68818493 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 - (-(68818493 / 250000000 : ℝ))| ≤ (1143470472503 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 73) 312 - (-(68818493 / 250000000 : ℝ)))]

theorem thL_73_cos : (192470134754797 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 73) ∧ Real.cos (11416334 / 100000 * Real.log 73) ≤ (481175428364631 / 500000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_73_sin : (-271810695795451 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 73) ∧ Real.sin (11416334 / 100000 * Real.log 73) ≤ (-10872420513607 / 40000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_73 : (192470134754797 / 200000000000000 : ℝ) ≤ cCG cZ 73 ∧ cCG cZ 73 ≤ (481175428364631 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_cos

theorem sCB_73 : (-271810695795451 / 1000000000000000 : ℝ) ≤ sCG cZ 73 ∧ sCG cZ 73 ≤ (-10872420513607 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_sin

theorem thL_74_r_bounds : (-58560741787055364111 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 ≤ (-58560704612944635889 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_74
  have hl : (98273289315573473 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 74 ∧ 11416334 / 100000 * Real.log 74 ≤ (491366446763712161 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_74_eq : (11416334 / 100000 * Real.log 74) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 + π / 2) + ((78 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_74_cos_r : (239359579343081 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) ≤ (957438503242879 / 1000000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(9150113 / 31250000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) (-(9150113 / 31250000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 - (-(9150113 / 31250000 : ℝ))| ≤ (18587055364111 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 - (-(9150113 / 31250000 : ℝ)))]

theorem thL_74_sin_r : (-288637738552843 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) ≤ (-288637552682289 / 1000000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (9150113 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((6959620066058218750138211747544021915169135398707938583210353098408348101202698238709356260409441417661079 / 24111962426687227889487985521554946899414062500000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(9150113 / 31250000 : ℝ)) ∧ Real.sin (-(9150113 / 31250000 : ℝ)) ≤ -((45683659920792407301883493166773316788984157701196704626436394389942013620731632403796009 / 158273394390562316402792930603027343750000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313) (-(9150113 / 31250000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 - (-(9150113 / 31250000 : ℝ))| ≤ (18587055364111 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 74) 313 - (-(9150113 / 31250000 : ℝ)))]

theorem thL_74_cos : (288637552682289 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 74) ∧ Real.cos (11416334 / 100000 * Real.log 74) ≤ (288637738552843 / 1000000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_74_sin : (239359579343081 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 74) ∧ Real.sin (11416334 / 100000 * Real.log 74) ≤ (957438503242879 / 1000000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_74 : (288637552682289 / 1000000000000000 : ℝ) ≤ cCG cZ 74 ∧ cCG cZ 74 ≤ (288637738552843 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_cos

theorem sCB_74 : (239359579343081 / 250000000000000 : ℝ) ≤ sCG cZ 74 ∧ sCG cZ 74 ≤ (957438503242879 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_sin

theorem thL_76_r_bounds : (-7797204099575778851 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 ≤ (-7797200260424221149 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_76
  have hl : (3862585802621161 / 7812500000000 : ℝ) ≤ 11416334 / 100000 * Real.log 76 ∧ 11416334 / 100000 * Real.log 76 ≤ (61801372865921403 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_76_eq : (11416334 / 100000 * Real.log 76) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 + π + π / 2) + ((78 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_76_cos_r : (57810133735369 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) ≤ (924962331723509 / 1000000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(389860109 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) (-(389860109 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 - (-(389860109 / 1000000000 : ℝ))| ≤ (1919575778851 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 - (-(389860109 / 1000000000 : ℝ)))]

theorem thL_76_sin_r : (-380059120929033 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) ≤ (-190029464485727 / 500000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (389860109 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2366635453592887658762935919711934605524549619886654978380502603070290525631837869469073939017307830798522729264010309162853629 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(389860109 / 1000000000 : ℝ)) ∧ Real.sin (-(389860109 / 1000000000 : ℝ)) ≤ -((15170740087133864438615025838728416945218326228833334769361119452817565418826959214735468478112267669689291 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315) (-(389860109 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 - (-(389860109 / 1000000000 : ℝ))| ≤ (1919575778851 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 76) 315 - (-(389860109 / 1000000000 : ℝ)))]

theorem thL_76_cos : (-380059120929033 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 76) ∧ Real.cos (11416334 / 100000 * Real.log 76) ≤ (-190029464485727 / 500000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_76_sin : (-924962331723509 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 76) ∧ Real.sin (11416334 / 100000 * Real.log 76) ≤ (-57810133735369 / 62500000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_76 : (-380059120929033 / 1000000000000000 : ℝ) ≤ cCG cZ 76 ∧ cCG cZ 76 ≤ (-190029464485727 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_cos

theorem sCB_76 : (-924962331723509 / 1000000000000000 : ℝ) ≤ sCG cZ 76 ∧ sCG cZ 76 ≤ (-57810133735369 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_sin

theorem thL_77_r_bounds : (-23415201987098933913 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 ≤ (-23415192212901066087 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_77
  have hl : (495903335227445353 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 77 ∧ 11416334 / 100000 * Real.log 77 ≤ (495903335422031411 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_77_eq : (11416334 / 100000 * Real.log 77) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) + ((79 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_77_cos_r : (44616751457211 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) ≤ (892335224628411 / 1000000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(234151971 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) (-(234151971 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 - (-(234151971 / 500000000 : ℝ))| ≤ (4887098933913 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 - (-(234151971 / 500000000 : ℝ)))]

theorem thL_77_sin_r : (-225686790464607 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) ≤ (-451373385445247 / 1000000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (234151971 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1411952677095067630157208120086817555830979417428735482099624297923114733169140212230363231196160105574656996600254075777 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(234151971 / 500000000 : ℝ)) ∧ Real.sin (-(234151971 / 500000000 : ℝ)) ≤ -((108611744391926265880219201695440604670556725779451072665936403556753531863382306200343690587285625109 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316) (-(234151971 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 - (-(234151971 / 500000000 : ℝ))| ≤ (4887098933913 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 77) 316 - (-(234151971 / 500000000 : ℝ)))]

theorem thL_77_cos : (44616751457211 / 50000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 77) ∧ Real.cos (11416334 / 100000 * Real.log 77) ≤ (892335224628411 / 1000000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_77_sin : (-225686790464607 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 77) ∧ Real.sin (11416334 / 100000 * Real.log 77) ≤ (-451373385445247 / 1000000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_77 : (44616751457211 / 50000000000000 : ℝ) ≤ cCG cZ 77 ∧ cCG cZ 77 ≤ (892335224628411 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_cos

theorem sCB_77 : (-225686790464607 / 500000000000000 : ℝ) ≤ sCG cZ 77 ∧ sCG cZ 77 ≤ (-451373385445247 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_sin

theorem thL_78_r_bounds : (-113200914721582859499 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 ≤ (-113200875278417140501 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_78
  have hl : (248688215510187157 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 78 ∧ 11416334 / 100000 * Real.log 78 ≤ (497376431217512581 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_78_eq : (11416334 / 100000 * Real.log 78) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 + π / 2) + ((79 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_78_cos_r : (422025132009791 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) ≤ (211012615309417 / 250000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(22640179 / 40000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) (-(22640179 / 40000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 - (-(22640179 / 40000000 : ℝ))| ≤ (19721582859499 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 - (-(22640179 / 40000000 : ℝ)))]

theorem thL_78_sin_r : (-536264012501613 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) ≤ (-268131907642843 / 500000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (22640179 / 40000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2240984110341817548847460252280169378974867940022347001587722443175270153708740046614476062686149072875747139 / 4178882919923712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(22640179 / 40000000 : ℝ)) ∧ Real.sin (-(22640179 / 40000000 : ℝ)) ≤ -((8978301724124226485209684098979557426714615124860069834629139588756118237362702922609660021 / 16742319390720000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317) (-(22640179 / 40000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 - (-(22640179 / 40000000 : ℝ))| ≤ (19721582859499 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 78) 317 - (-(22640179 / 40000000 : ℝ)))]

theorem thL_78_cos : (268131907642843 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 78) ∧ Real.cos (11416334 / 100000 * Real.log 78) ≤ (536264012501613 / 1000000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_78_sin : (422025132009791 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 78) ∧ Real.sin (11416334 / 100000 * Real.log 78) ≤ (211012615309417 / 250000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_78 : (268131907642843 / 500000000000000 : ℝ) ≤ cCG cZ 78 ∧ cCG cZ 78 ≤ (536264012501613 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_cos

theorem sCB_78 : (422025132009791 / 500000000000000 : ℝ) ≤ sCG cZ 78 ∧ sCG cZ 78 ≤ (211012615309417 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_sin

theorem thL_79_r_bounds : (-68247116978407491673 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 ≤ (-68247097021592508327 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_79
  have hl : (9976615215019861 / 20000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 79 ∧ 11416334 / 100000 * Real.log 79 ≤ (124707690237631263 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_79_eq : (11416334 / 100000 * Real.log 79) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 + π) + ((79 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_79_cos_r : (776016454948037 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) ≤ (388008327268751 / 500000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(68247107 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) (-(68247107 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 - (-(68247107 / 100000000 : ℝ))| ≤ (9978407491673 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 - (-(68247107 / 100000000 : ℝ)))]

theorem thL_79_sin_r : (-630712638702329 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) ≤ (-630712439133059 / 1000000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (68247107 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((392746009866477276719485875992684645515169130828194017294843182479485434325513867663543595630040723632567675922707 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(68247107 / 100000000 : ℝ)) ∧ Real.sin (-(68247107 / 100000000 : ℝ)) ≤ -((251760262734474677871948089952240965912925773781251387925120371541288580799804624159800313516357 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318) (-(68247107 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 - (-(68247107 / 100000000 : ℝ))| ≤ (9978407491673 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 79) 318 - (-(68247107 / 100000000 : ℝ)))]

theorem thL_79_cos : (-388008327268751 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 79) ∧ Real.cos (11416334 / 100000 * Real.log 79) ≤ (-776016454948037 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_79_sin : (630712439133059 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 79) ∧ Real.sin (11416334 / 100000 * Real.log 79) ≤ (630712638702329 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_79 : (-388008327268751 / 500000000000000 : ℝ) ≤ cCG cZ 79 ∧ cCG cZ 79 ≤ (-776016454948037 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_cos

theorem sCB_79 : (630712439133059 / 1000000000000000 : ℝ) ≤ sCG cZ 79 ∧ sCG cZ 79 ≤ (630712638702329 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_sin

theorem thL_81_r_bounds : (120192933333859692807 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 ≤ (120192974266140307193 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_81
  have hl : (12542124822856033 / 25000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 81 ∧ 11416334 / 100000 * Real.log 81 ≤ (50168499311813103 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_81_eq : (11416334 / 100000 * Real.log 81) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 + π + π / 2) + ((79 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_81_cos_r : (824790379001853 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) ≤ (82479058366789 / 100000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (600964769 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) (600964769 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 - (600964769 / 1000000000 : ℝ)| ≤ (20466140307193 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 - (600964769 / 1000000000 : ℝ))]

theorem thL_81_sin_r : (70679795797217 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) ≤ (282719285519677 / 500000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (600964769 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319) (600964769 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 - (600964769 / 1000000000 : ℝ)| ≤ (20466140307193 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 81) 319 - (600964769 / 1000000000 : ℝ))]

theorem thL_81_cos : (70679795797217 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 81) ∧ Real.cos (11416334 / 100000 * Real.log 81) ≤ (282719285519677 / 500000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_81_sin : (-82479058366789 / 100000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 81) ∧ Real.sin (11416334 / 100000 * Real.log 81) ≤ (-824790379001853 / 1000000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_81 : (70679795797217 / 125000000000000 : ℝ) ≤ cCG cZ 81 ∧ cCG cZ 81 ≤ (282719285519677 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_cos

theorem sCB_81 : (-82479058366789 / 100000000000000 : ℝ) ≤ sCG cZ 81 ∧ sCG cZ 81 ≤ (-824790379001853 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_sin

theorem thL_82_r_bounds : (269351932417689903 / 625000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 ≤ (269352061332310097 / 625000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_82
  have hl : (251542893833117611 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 82 ∧ 11416334 / 100000 * Real.log 82 ≤ (251542893936054679 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_82_eq : (11416334 / 100000 * Real.log 82) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) + ((80 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_82_cos_r : (908563697088639 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) ≤ (454281951676059 / 500000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (86192639 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) (86192639 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 - (86192639 / 200000000 : ℝ)| ≤ (64457310097 / 625000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 - (86192639 / 200000000 : ℝ))]

theorem thL_82_sin_r : (41774601705259 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) ≤ (208873111657993 / 500000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (86192639 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320) (86192639 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 - (86192639 / 200000000 : ℝ)| ≤ (64457310097 / 625000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 82) 320 - (86192639 / 200000000 : ℝ))]

theorem thL_82_cos : (908563697088639 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 82) ∧ Real.cos (11416334 / 100000 * Real.log 82) ≤ (454281951676059 / 500000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_82_sin : (41774601705259 / 100000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 82) ∧ Real.sin (11416334 / 100000 * Real.log 82) ≤ (208873111657993 / 500000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_82 : (908563697088639 / 1000000000000000 : ℝ) ≤ cCG cZ 82 ∧ cCG cZ 82 ≤ (454281951676059 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_cos

theorem sCB_82 : (41774601705259 / 100000000000000 : ℝ) ≤ sCG cZ 82 ∧ sCG cZ 82 ≤ (208873111657993 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_sin

theorem thL_83_r_bounds : (24398176784216177283 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 ≤ (24398197615783822717 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_83
  have hl : (6305870033369731 / 12500000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 83 ∧ 11416334 / 100000 * Real.log 83 ≤ (504469602877319653 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_83_eq : (11416334 / 100000 * Real.log 83) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 + π / 2) + ((80 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_83_cos_r : (485191835671651 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) ≤ (48519193982949 / 50000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (15248867 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) (15248867 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 - (15248867 / 62500000 : ℝ)| ≤ (10415783822717 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 - (15248867 / 62500000 : ℝ))]

theorem thL_83_sin_r : (241568371111909 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) ≤ (241568579427587 / 1000000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (15248867 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321) (15248867 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 - (15248867 / 62500000 : ℝ)| ≤ (10415783822717 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 83) 321 - (15248867 / 62500000 : ℝ))]

theorem thL_83_cos : (-241568579427587 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 83) ∧ Real.cos (11416334 / 100000 * Real.log 83) ≤ (-241568371111909 / 1000000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_83_sin : (485191835671651 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 83) ∧ Real.sin (11416334 / 100000 * Real.log 83) ≤ (48519193982949 / 50000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_83 : (-241568579427587 / 1000000000000000 : ℝ) ≤ cCG cZ 83 ∧ cCG cZ 83 ≤ (-241568371111909 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_cos

theorem sCB_83 : (485191835671651 / 500000000000000 : ℝ) ≤ sCG cZ 83 ∧ sCG cZ 83 ≤ (48519193982949 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_sin

theorem thL_84_r_bounds : (2021370542979469603 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 ≤ (2021381057020530397 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_84
  have hl : (252918422319799033 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 84 ∧ 11416334 / 100000 * Real.log 84 ≤ (252918422424548561 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_84_eq : (11416334 / 100000 * Real.log 84) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 + π) + ((80 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_84_cos_r : (249795703532257 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) ≤ (19983660488197 / 20000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (10106879 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) (10106879 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 - (10106879 / 250000000 : ℝ)| ≤ (5257020530397 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 - (10106879 / 250000000 : ℝ))]

theorem thL_84_sin_r : (20208199705793 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) ≤ (5052076211551 / 125000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (10106879 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322) (10106879 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 - (10106879 / 250000000 : ℝ)| ≤ (5257020530397 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 84) 322 - (10106879 / 250000000 : ℝ))]

theorem thL_84_cos : (-19983660488197 / 20000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 84) ∧ Real.cos (11416334 / 100000 * Real.log 84) ≤ (-249795703532257 / 250000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_84_sin : (-5052076211551 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 84) ∧ Real.sin (11416334 / 100000 * Real.log 84) ≤ (-20208199705793 / 500000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_84 : (-19983660488197 / 20000000000000 : ℝ) ≤ cCG cZ 84 ∧ cCG cZ 84 ≤ (-249795703532257 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_cos

theorem sCB_84 : (-5052076211551 / 125000000000000 : ℝ) ≤ sCG cZ 84 ∧ sCG cZ 84 ≤ (-20208199705793 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_sin

theorem thL_86_r_bounds : (-20742253319145781607 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 ≤ (-20742242680854218393 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_86
  have hl : (508523164815163589 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 86 ∧ 11416334 / 100000 * Real.log 86 ≤ (254261582513940309 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_86_eq : (11416334 / 100000 * Real.log 86) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) + ((81 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_86_cos_r : (915178713679709 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) ≤ (183035785289119 / 200000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(2592781 / 6250000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) (-(2592781 / 6250000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 - (-(2592781 / 6250000 : ℝ))| ≤ (5319145781607 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 - (-(2592781 / 6250000 : ℝ)))]

theorem thL_86_sin_r : (-403048152288963 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) ≤ (-403047939523129 / 1000000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (2592781 / 6250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((55728501041769760035035785203137194768720789896358862296080736304581929313092412068582770447993341 / 138267637339595239609479904174804687500000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(2592781 / 6250000 : ℝ)) ∧ Real.sin (-(2592781 / 6250000 : ℝ)) ≤ -((9145189914546793145072040571275451428825126740174939937429539013156708945172937419 / 22690073819831013679504394531250000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324) (-(2592781 / 6250000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 - (-(2592781 / 6250000 : ℝ))| ≤ (5319145781607 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 86) 324 - (-(2592781 / 6250000 : ℝ)))]

theorem thL_86_cos : (915178713679709 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 86) ∧ Real.cos (11416334 / 100000 * Real.log 86) ≤ (183035785289119 / 200000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_86_sin : (-403048152288963 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 86) ∧ Real.sin (11416334 / 100000 * Real.log 86) ≤ (-403047939523129 / 1000000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_86 : (915178713679709 / 1000000000000000 : ℝ) ≤ cCG cZ 86 ∧ cCG cZ 86 ≤ (183035785289119 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_cos

theorem sCB_86 : (-403048152288963 / 1000000000000000 : ℝ) ≤ sCG cZ 86 ∧ sCG cZ 86 ≤ (-403047939523129 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_sin

theorem thL_87_r_bounds : (-2663277180686591001 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 ≤ (-2663276323313408999 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_87
  have hl : (63730373364165319 / 125000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 87 ∧ 11416334 / 100000 * Real.log 87 ≤ (509842987127513049 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_87_eq : (11416334 / 100000 * Real.log 87) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 + π / 2) + ((81 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_87_cos_r : (39320546326149 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) ≤ (786411140882123 / 1000000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(166454797 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) (-(166454797 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 - (-(166454797 / 250000000 : ℝ))| ≤ (428686591001 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 - (-(166454797 / 250000000 : ℝ)))]

theorem thL_87_sin_r : (-154425916392601 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) ≤ (-77212931403287 / 125000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (166454797 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((57316614782557875650275303567460394071323830734830511106160149488514332686558331387732624461604419316795889289919534077 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(166454797 / 250000000 : ℝ)) ∧ Real.sin (-(166454797 / 250000000 : ℝ)) ≤ -((5878627157177699050778737477796580941433811419720972975064245737760849690856744740520571408233439947 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325) (-(166454797 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 - (-(166454797 / 250000000 : ℝ))| ≤ (428686591001 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 87) 325 - (-(166454797 / 250000000 : ℝ)))]

theorem thL_87_cos : (77212931403287 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 87) ∧ Real.cos (11416334 / 100000 * Real.log 87) ≤ (154425916392601 / 250000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_87_sin : (39320546326149 / 50000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 87) ∧ Real.sin (11416334 / 100000 * Real.log 87) ≤ (786411140882123 / 1000000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_87 : (77212931403287 / 125000000000000 : ℝ) ≤ cCG cZ 87 ∧ cCG cZ 87 ≤ (154425916392601 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_cos

theorem sCB_87 : (39320546326149 / 50000000000000 : ℝ) ≤ sCG cZ 87 ∧ sCG cZ 87 ≤ (786411140882123 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_sin

theorem thL_88_r_bounds : (5111350334173949989 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 ≤ (5111352065826050011 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_88
  have hl : (102229545000022629 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 88 ∧ 11416334 / 100000 * Real.log 88 ≤ (511147725215694813 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_88_eq : (11416334 / 100000 * Real.log 88) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 + π / 2) + ((81 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_88_cos_r : (100342601097089 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) ≤ (802741025242887 / 1000000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (6389189 / 10000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) (6389189 / 10000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 - (6389189 / 10000000 : ℝ)| ≤ (865826050011 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 - (6389189 / 10000000 : ℝ))]

theorem thL_88_sin_r : (74540979823069 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) ≤ (596328055041541 / 1000000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (6389189 / 10000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325) (6389189 / 10000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 - (6389189 / 10000000 : ℝ)| ≤ (865826050011 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 88) 325 - (6389189 / 10000000 : ℝ))]

theorem thL_88_cos : (-596328055041541 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 88) ∧ Real.cos (11416334 / 100000 * Real.log 88) ≤ (-74540979823069 / 125000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_88_sin : (100342601097089 / 125000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 88) ∧ Real.sin (11416334 / 100000 * Real.log 88) ≤ (802741025242887 / 1000000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_88 : (-596328055041541 / 1000000000000000 : ℝ) ≤ cCG cZ 88 ∧ cCG cZ 88 ≤ (-74540979823069 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_cos

theorem sCB_88 : (100342601097089 / 125000000000000 : ℝ) ≤ sCG cZ 88 ∧ sCG cZ 88 ≤ (802741025242887 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_sin

theorem thL_89_r_bounds : (17905871604321893449 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 ≤ (17905882495678106551 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_89
  have hl : (512437719968153863 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 89 ∧ 11416334 / 100000 * Real.log 89 ≤ (25621886009252493 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_89_eq : (11416334 / 100000 * Real.log 89) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 + π) + ((81 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_89_cos_r : (46827909896391 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) ≤ (468279207877477 / 500000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (358117541 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) (358117541 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 - (358117541 / 1000000000 : ℝ)| ≤ (5445678106551 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 - (358117541 / 1000000000 : ℝ))]

theorem thL_89_sin_r : (43813964229351 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) ≤ (175255965830967 / 500000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (358117541 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326) (358117541 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 - (358117541 / 1000000000 : ℝ)| ≤ (5445678106551 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 89) 326 - (358117541 / 1000000000 : ℝ))]

theorem thL_89_cos : (-468279207877477 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 89) ∧ Real.cos (11416334 / 100000 * Real.log 89) ≤ (-46827909896391 / 50000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_89_sin : (-175255965830967 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 89) ∧ Real.sin (11416334 / 100000 * Real.log 89) ≤ (-43813964229351 / 125000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_89 : (-468279207877477 / 500000000000000 : ℝ) ≤ cCG cZ 89 ∧ cCG cZ 89 ≤ (-46827909896391 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_cos

theorem sCB_89 : (-175255965830967 / 500000000000000 : ℝ) ≤ sCG cZ 89 ∧ sCG cZ 89 ≤ (-43813964229351 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_sin

theorem thL_91_r_bounds : (-3080096260968398657 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 ≤ (-3080093514031601343 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_91
  have hl : (4023240527252263 / 7812500000000 : ℝ) ≤ 11416334 / 100000 * Real.log 91 ∧ 11416334 / 100000 * Real.log 91 ≤ (514974787707603563 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_91_eq : (11416334 / 100000 * Real.log 91) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_91_cos_r : (242448708508933 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) ≤ (969795053790677 / 1000000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(246407591 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) (-(246407591 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 - (-(246407591 / 1000000000 : ℝ))| ≤ (1373468398657 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 - (-(246407591 / 1000000000 : ℝ)))]

theorem thL_91_sin_r : (-121960875246309 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) ≤ (-243921530737673 / 1000000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (246407591 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((216986447097233365504393620078491488111334142173639771927671982446815172500262868238330031684127639812408463729900204002596353 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(246407591 / 1000000000 : ℝ)) ∧ Real.sin (-(246407591 / 1000000000 : ℝ)) ≤ -((9736571344106625296060350724040139003337922201336151068360445291258418419150043937304578229458142949936009 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328) (-(246407591 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 - (-(246407591 / 1000000000 : ℝ))| ≤ (1373468398657 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 91) 328 - (-(246407591 / 1000000000 : ℝ)))]

theorem thL_91_cos : (242448708508933 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 91) ∧ Real.cos (11416334 / 100000 * Real.log 91) ≤ (969795053790677 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_91_sin : (-121960875246309 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 91) ∧ Real.sin (11416334 / 100000 * Real.log 91) ≤ (-243921530737673 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_91 : (242448708508933 / 250000000000000 : ℝ) ≤ cCG cZ 91 ∧ cCG cZ 91 ≤ (969795053790677 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_cos

theorem sCB_91 : (-121960875246309 / 500000000000000 : ℝ) ≤ sCG cZ 91 ∧ sCG cZ 91 ≤ (-243921530737673 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_sin

theorem thL_92_r_bounds : (-113900966480682145663 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 ≤ (-113900922319317854337 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_92
  have hl : (516222486683117577 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 92 ∧ 11416334 / 100000 * Real.log 92 ≤ (516222486903544013 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_92_eq : (11416334 / 100000 * Real.log 92) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 + π / 2) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_92_cos_r : (42108401468403 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) ≤ (842168250177313 / 1000000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(284752361 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) (-(284752361 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 - (-(284752361 / 500000000 : ℝ))| ≤ (22080682145663 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 - (-(284752361 / 500000000 : ℝ)))]

theorem thL_92_sin_r : (-269607558968651 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) ≤ (-539214897130373 / 1000000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (284752361 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((58553694677484899845758306721630954340095097534802199530850825745913014825121035043063806851903273465300649373354387860783 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(284752361 / 500000000 : ℝ)) ∧ Real.sin (-(284752361 / 500000000 : ℝ)) ≤ -((10509637506213163469067620328977602728017573088450402793831394376515376700107665314513608876729623156039 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329) (-(284752361 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 - (-(284752361 / 500000000 : ℝ))| ≤ (22080682145663 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 92) 329 - (-(284752361 / 500000000 : ℝ)))]

theorem thL_92_cos : (539214897130373 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 92) ∧ Real.cos (11416334 / 100000 * Real.log 92) ≤ (269607558968651 / 500000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_92_sin : (42108401468403 / 50000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 92) ∧ Real.sin (11416334 / 100000 * Real.log 92) ≤ (842168250177313 / 1000000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_92 : (539214897130373 / 1000000000000000 : ℝ) ≤ cCG cZ 92 ∧ cCG cZ 92 ≤ (269607558968651 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_cos

theorem sCB_92 : (42108401468403 / 50000000000000 : ℝ) ≤ sCG cZ 92 ∧ sCG cZ 92 ≤ (842168250177313 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_sin

theorem thL_93_r_bounds : (66470545821698172667 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 ≤ (66470567978301827333 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_93
  have hl : (258728348486911943 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 93 ∧ 11416334 / 100000 * Real.log 93 ≤ (258728348597652003 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_93_eq : (11416334 / 100000 * Real.log 93) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 + π / 2) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_93_cos_r : (787098321556043 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) ≤ (787098543137613 / 1000000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (664705569 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) (664705569 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 - (664705569 / 1000000000 : ℝ)| ≤ (11078301827333 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 - (664705569 / 1000000000 : ℝ))]

theorem thL_93_sin_r : (77103412813169 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) ≤ (77103440509023 / 125000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (664705569 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329) (664705569 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 - (664705569 / 1000000000 : ℝ)| ≤ (11078301827333 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 93) 329 - (664705569 / 1000000000 : ℝ))]

theorem thL_93_cos : (-77103440509023 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 93) ∧ Real.cos (11416334 / 100000 * Real.log 93) ≤ (-77103412813169 / 125000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_93_sin : (787098321556043 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 93) ∧ Real.sin (11416334 / 100000 * Real.log 93) ≤ (787098543137613 / 1000000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_93 : (-77103440509023 / 125000000000000 : ℝ) ≤ cCG cZ 93 ∧ cCG cZ 93 ≤ (-77103412813169 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_cos

theorem sCB_93 : (787098321556043 / 1000000000000000 : ℝ) ≤ sCG cZ 93 ∧ sCG cZ 93 ≤ (787098543137613 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_sin

theorem thL_94_r_bounds : (3149190583794553459 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 ≤ (3149192816205446541 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_94
  have hl : (518677706901457779 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 94 ∧ 11416334 / 100000 * Real.log 94 ≤ (518677707123936429 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_94_eq : (11416334 / 100000 * Real.log 94) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 + π) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_94_cos_r : (950821306652839 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) ≤ (237705382473483 / 250000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (31491917 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) (31491917 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 - (31491917 / 100000000 : ℝ)| ≤ (1116205446541 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 - (31491917 / 100000000 : ℝ))]

theorem thL_94_sin_r : (154869752861871 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) ≤ (309739728964833 / 1000000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (31491917 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330) (31491917 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 - (31491917 / 100000000 : ℝ)| ≤ (1116205446541 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 94) 330 - (31491917 / 100000000 : ℝ))]

theorem thL_94_cos : (-237705382473483 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 94) ∧ Real.cos (11416334 / 100000 * Real.log 94) ≤ (-950821306652839 / 1000000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_94_sin : (-309739728964833 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 94) ∧ Real.sin (11416334 / 100000 * Real.log 94) ≤ (-154869752861871 / 500000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_94 : (-237705382473483 / 250000000000000 : ℝ) ≤ cCG cZ 94 ∧ cCG cZ 94 ≤ (-950821306652839 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_cos

theorem sCB_94 : (-309739728964833 / 1000000000000000 : ℝ) ≤ sCG cZ 94 ∧ sCG cZ 94 ≤ (-154869752861871 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_sin

theorem thL_96_r_bounds : (-21157304120282379301 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 ≤ (-21157292879717620699 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_96
  have hl : (52108123441350003 / 100000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 96 ∧ 11416334 / 100000 * Real.log 96 ≤ (521081234637823743 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_96_eq : (11416334 / 100000 * Real.log 96) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_96_cos_r : (455900754697551 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) ≤ (911801734206467 / 1000000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(42314597 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) (-(42314597 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 - (-(42314597 / 100000000 : ℝ))| ≤ (5620282379301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 - (-(42314597 / 100000000 : ℝ)))]

theorem thL_96_sin_r : (-205315546656781 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) ≤ (-51328858562783 / 125000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (42314597 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((19669289686446043898820680538566744589224100631311925933247695411003002651806671518818240999039459141342043326729 / 47900160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(42314597 / 100000000 : ℝ)) ∧ Real.sin (-(42314597 / 100000000 : ℝ)) ≤ -((163910747387049472007516500915403408923789450006211931931404128694629519014183440532237132607747 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332) (-(42314597 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 - (-(42314597 / 100000000 : ℝ))| ≤ (5620282379301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 96) 332 - (-(42314597 / 100000000 : ℝ)))]

theorem thL_96_cos : (455900754697551 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 96) ∧ Real.cos (11416334 / 100000 * Real.log 96) ≤ (911801734206467 / 1000000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_96_sin : (-205315546656781 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 96) ∧ Real.sin (11416334 / 100000 * Real.log 96) ≤ (-51328858562783 / 125000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_96 : (455900754697551 / 500000000000000 : ℝ) ≤ cCG cZ 96 ∧ cCG cZ 96 ≤ (911801734206467 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_cos

theorem sCB_96 : (-205315546656781 / 500000000000000 : ℝ) ≤ sCG cZ 96 ∧ sCG cZ 96 ≤ (-51328858562783 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_sin

theorem thL_97_r_bounds : (37995214855525820699 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 ≤ (37995226144474179301 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_97
  have hl : (261132142396508097 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 97 ∧ 11416334 / 100000 * Real.log 97 ≤ (261132142509096289 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_97_eq : (11416334 / 100000 * Real.log 97) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_97_cos_r : (724901748463523 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) ≤ (90612746789987 / 125000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (75990441 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) (75990441 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 - (75990441 / 100000000 : ℝ)| ≤ (5644474179301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 - (75990441 / 100000000 : ℝ))]

theorem thL_97_sin_r : (344426020997451 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) ≤ (137770453555679 / 200000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (75990441 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332) (75990441 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 - (75990441 / 100000000 : ℝ)| ≤ (5644474179301 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 97) 332 - (75990441 / 100000000 : ℝ))]

theorem thL_97_cos : (724901748463523 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 97) ∧ Real.cos (11416334 / 100000 * Real.log 97) ≤ (90612746789987 / 125000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_97_sin : (344426020997451 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 97) ∧ Real.sin (11416334 / 100000 * Real.log 97) ≤ (137770453555679 / 200000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_97 : (724901748463523 / 1000000000000000 : ℝ) ≤ cCG cZ 97 ∧ cCG cZ 97 ≤ (90612746789987 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_cos

theorem sCB_97 : (344426020997451 / 500000000000000 : ℝ) ≤ sCG cZ 97 ∧ sCG cZ 97 ≤ (137770453555679 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_sin

theorem thL_98_r_bounds : (72004857190104158949 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 ≤ (72004902409895841051 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_98
  have hl : (104687040221730219 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 98 ∧ 11416334 / 100000 * Real.log 98 ≤ (523435201334637311 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_98_eq : (11416334 / 100000 * Real.log 98) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 + π / 2) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_98_cos_r : (467944057605427 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) ≤ (935888341309823 / 1000000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (360024399 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) (360024399 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 - (360024399 / 1000000000 : ℝ)| ≤ (22609895841051 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 - (360024399 / 1000000000 : ℝ))]

theorem thL_98_sin_r : (44037119383419 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) ≤ (44037147645789 / 125000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (360024399 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333) (360024399 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 - (360024399 / 1000000000 : ℝ)| ≤ (22609895841051 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 98) 333 - (360024399 / 1000000000 : ℝ))]

theorem thL_98_cos : (-44037147645789 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 98) ∧ Real.cos (11416334 / 100000 * Real.log 98) ≤ (-44037119383419 / 125000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_98_sin : (467944057605427 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 98) ∧ Real.sin (11416334 / 100000 * Real.log 98) ≤ (935888341309823 / 1000000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_98 : (-44037147645789 / 125000000000000 : ℝ) ≤ cCG cZ 98 ∧ cCG cZ 98 ≤ (-44037119383419 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_cos

theorem sCB_98 : (467944057605427 / 500000000000000 : ℝ) ≤ sCG cZ 98 ∧ sCG cZ 98 ≤ (935888341309823 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_sin

theorem thL_99_r_bounds : (-5174340574529982449 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 ≤ (-5174317825470017551 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_99
  have hl : (524594229743750171 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 99 ∧ 11416334 / 100000 * Real.log 99 ≤ (524594229970505937 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_99_eq : (11416334 / 100000 * Real.log 99) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 + π) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_99_cos_r : (249665375193437 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) ≤ (998661728264349 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(12935823 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) (-(12935823 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 - (-(12935823 / 250000000 : ℝ))| ≤ (11374529982449 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 - (-(12935823 / 250000000 : ℝ)))]

theorem thL_99_sin_r : (-51720319528027 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) ≤ (-51720092037427 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (12935823 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((19749422450450743201893613344269079453048988361911953426568901356050447066764946014607165660843715489108646305577781 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(12935823 / 250000000 : ℝ)) ∧ Real.sin (-(12935823 / 250000000 : ℝ)) ≤ -((6076745369369459446736496054010059459267593487128342428541423256316609536364669848228083430511233 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334) (-(12935823 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 - (-(12935823 / 250000000 : ℝ))| ≤ (11374529982449 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 99) 334 - (-(12935823 / 250000000 : ℝ)))]

theorem thL_99_cos : (-998661728264349 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 99) ∧ Real.cos (11416334 / 100000 * Real.log 99) ≤ (-249665375193437 / 250000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_99_sin : (51720092037427 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 99) ∧ Real.sin (11416334 / 100000 * Real.log 99) ≤ (51720319528027 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_99 : (-998661728264349 / 1000000000000000 : ℝ) ≤ cCG cZ 99 ∧ cCG cZ 99 ≤ (-249665375193437 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_cos

theorem sCB_99 : (51720092037427 / 1000000000000000 : ℝ) ≤ sCG cZ 99 ∧ sCG cZ 99 ≤ (51720319528027 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_sin

theorem thL_101_r_bounds : (26432127225379062251 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 ≤ (26432136374620937749 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_101
  have hl : (131719393164231211 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 101 ∧ 11416334 / 100000 * Real.log 101 ≤ (263438786442554111 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_101_eq : (11416334 / 100000 * Real.log 101) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 + π + π / 2) + ((83 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_101_cos_r : (394749674292279 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) ≤ (394749788665039 / 500000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (132160659 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) (132160659 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 - (132160659 / 200000000 : ℝ)| ≤ (4574620937749 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 - (132160659 / 200000000 : ℝ))]

theorem thL_101_sin_r : (613751136531641 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) ≤ (24550054610537 / 40000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (132160659 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335) (132160659 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 - (132160659 / 200000000 : ℝ)| ≤ (4574620937749 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 101) 335 - (132160659 / 200000000 : ℝ))]

theorem thL_101_cos : (613751136531641 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 101) ∧ Real.cos (11416334 / 100000 * Real.log 101) ≤ (24550054610537 / 40000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_101_sin : (-394749788665039 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 101) ∧ Real.sin (11416334 / 100000 * Real.log 101) ≤ (-394749674292279 / 500000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_101 : (613751136531641 / 1000000000000000 : ℝ) ≤ cCG cZ 101 ∧ cCG cZ 101 ≤ (24550054610537 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_cos

theorem sCB_101 : (-394749788665039 / 500000000000000 : ℝ) ≤ sCG cZ 101 ∧ sCG cZ 101 ≤ (-394749674292279 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_sin

theorem thL_102_r_bounds : (2684724028892974213 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 ≤ (2684726896107025787 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_102
  have hl : (264001171862698351 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 102 ∧ 11416334 / 100000 * Real.log 102 ≤ (52800234395424243 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_102_eq : (11416334 / 100000 * Real.log 102) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) + ((84 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_102_cos_r : (977023610686511 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) ≤ (244255960015909 / 250000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (214778037 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) (214778037 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 - (214778037 / 1000000000 : ℝ)| ≤ (1433607025787 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 - (214778037 / 1000000000 : ℝ))]

theorem thL_102_sin_r : (106565227873529 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) ≤ (213130685124183 / 1000000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (214778037 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336) (214778037 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 - (214778037 / 1000000000 : ℝ)| ≤ (1433607025787 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 102) 336 - (214778037 / 1000000000 : ℝ))]

theorem thL_102_cos : (977023610686511 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 102) ∧ Real.cos (11416334 / 100000 * Real.log 102) ≤ (244255960015909 / 250000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_102_sin : (106565227873529 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 102) ∧ Real.sin (11416334 / 100000 * Real.log 102) ≤ (213130685124183 / 1000000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_102 : (977023610686511 / 1000000000000000 : ℝ) ≤ cCG cZ 102 ∧ cCG cZ 102 ≤ (244255960015909 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_cos

theorem sCB_102 : (106565227873529 / 500000000000000 : ℝ) ≤ sCG cZ 102 ∧ sCG cZ 102 ≤ (213130685124183 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_sin

theorem thL_103_r_bounds : (-48444177444487936439 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 ≤ (-48444131355512063561 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_103
  have hl : (529116141242657721 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 103 ∧ 11416334 / 100000 * Real.log 103 ≤ (16534879421004191 / 31250000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_103_eq : (11416334 / 100000 * Real.log 103) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 + π / 2) + ((84 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_103_cos_r : (485403790745669 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) ≤ (485403905968109 / 500000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(60555193 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) (-(60555193 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 - (-(60555193 / 250000000 : ℝ))| ≤ (23044487936439 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 - (-(60555193 / 250000000 : ℝ)))]

theorem thL_103_sin_r : (-119929636949773 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) ≤ (-119929521727333 / 500000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (60555193 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3179499017666149274828822048400204298434961523278086432663705906196657421540679421472010909049143768574010527204109599 / 13255691528320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(60555193 / 250000000 : ℝ)) ∧ Real.sin (-(60555193 / 250000000 : ℝ)) ≤ -((2282717243452619977085263254242903710572444506969628900177194286200701317819897783386541921507033943 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337) (-(60555193 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 - (-(60555193 / 250000000 : ℝ))| ≤ (23044487936439 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 103) 337 - (-(60555193 / 250000000 : ℝ)))]

theorem thL_103_cos : (119929521727333 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 103) ∧ Real.cos (11416334 / 100000 * Real.log 103) ≤ (119929636949773 / 500000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_103_sin : (485403790745669 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 103) ∧ Real.sin (11416334 / 100000 * Real.log 103) ≤ (485403905968109 / 500000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_103 : (119929521727333 / 500000000000000 : ℝ) ≤ cCG cZ 103 ∧ cCG cZ 103 ≤ (119929636949773 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_cos

theorem sCB_103 : (485403790745669 / 500000000000000 : ℝ) ≤ sCG cZ 103 ∧ sCG cZ 103 ≤ (485403905968109 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_sin

theorem thL_104_r_bounds : (-35499059720300435013 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 ≤ (-35499048179699564987 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_104
  have hl : (106043835452600779 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 104 ∧ 11416334 / 100000 * Real.log 104 ≤ (265109588746540533 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_104_eq : (11416334 / 100000 * Real.log 104) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 + π) + ((84 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_104_cos_r : (758374093761379 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) ≤ (189593581151911 / 250000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(709981079 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) (-(709981079 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 - (-(709981079 / 1000000000 : ℝ))| ≤ (5770300435013 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 - (-(709981079 / 1000000000 : ℝ)))]

theorem thL_104_sin_r : (-81477442168227 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) ≤ (-651819306531927 / 1000000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (709981079 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((579841871180450447969832134896772360092009483107665920279459174709407093641598221611056768957436424574349063544025744887600977 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(709981079 / 1000000000 : ℝ)) ∧ Real.sin (-(709981079 / 1000000000 : ℝ)) ≤ -((26018545501612219850875206781099273870701869416747396980209311099797472314698792526439402217452554989080121 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338) (-(709981079 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 - (-(709981079 / 1000000000 : ℝ))| ≤ (5770300435013 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 104) 338 - (-(709981079 / 1000000000 : ℝ)))]

theorem thL_104_cos : (-189593581151911 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 104) ∧ Real.cos (11416334 / 100000 * Real.log 104) ≤ (-758374093761379 / 1000000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_104_sin : (651819306531927 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 104) ∧ Real.sin (11416334 / 100000 * Real.log 104) ≤ (81477442168227 / 125000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_104 : (-189593581151911 / 250000000000000 : ℝ) ≤ cCG cZ 104 ∧ cCG cZ 104 ≤ (-758374093761379 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_cos

theorem sCB_104 : (651819306531927 / 1000000000000000 : ℝ) ≤ sCG cZ 104 ∧ sCG cZ 104 ≤ (81477442168227 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_sin

theorem thL_106_r_bounds : (-21234392372815984133 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 ≤ (-21234346027184015867 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_106
  have hl : (266196891410802937 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 106 ∧ 11416334 / 100000 * Real.log 106 ≤ (21295751322112063 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_106_eq : (11416334 / 100000 * Real.log 106) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 + π + π / 2) + ((84 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_106_cos_r : (994368946220987 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) ≤ (248592294487287 / 250000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(53085923 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) (-(53085923 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 - (-(53085923 / 500000000 : ℝ))| ≤ (23172815984133 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 - (-(53085923 / 500000000 : ℝ)))]

theorem thL_106_sin_r : (-26493151149031 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) ≤ (-105972372867963 / 1000000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (53085923 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1046147162201642217452744729997206409568465263663608959362641488452246774132329436947431855400858138392394143576571166079 / 9871875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(53085923 / 500000000 : ℝ)) ∧ Real.sin (-(53085923 / 500000000 : ℝ)) ≤ -((187770003472089628773507583642592283779860344241998751672512926699545079453395663395070563420710590543 / 1771875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339) (-(53085923 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 - (-(53085923 / 500000000 : ℝ))| ≤ (23172815984133 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 106) 339 - (-(53085923 / 500000000 : ℝ)))]

theorem thL_106_cos : (-26493151149031 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 106) ∧ Real.cos (11416334 / 100000 * Real.log 106) ≤ (-105972372867963 / 1000000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_106_sin : (-248592294487287 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 106) ∧ Real.sin (11416334 / 100000 * Real.log 106) ≤ (-994368946220987 / 1000000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_106 : (-26493151149031 / 250000000000000 : ℝ) ≤ cCG cZ 106 ∧ cCG cZ 106 ≤ (-105972372867963 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_cos

theorem sCB_106 : (-248592294487287 / 250000000000000 : ℝ) ≤ sCG cZ 106 ∧ sCG cZ 106 ≤ (-994368946220987 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_sin

theorem thL_107_r_bounds : (-3025020845118772309 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 ≤ (-3025019684881227691 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_107
  have hl : (133366436735393027 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 107 ∧ 11416334 / 100000 * Real.log 107 ≤ (106693149434657721 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_107_eq : (11416334 / 100000 * Real.log 107) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_107_cos_r : (205624919101041 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) ≤ (411249954228347 / 500000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(605004053 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) (-(605004053 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 - (-(605004053 / 1000000000 : ℝ))| ≤ (580118772309 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 - (-(605004053 / 1000000000 : ℝ)))]

theorem thL_107_sin_r : (-284382762939493 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) ≤ (-284382646915621 / 500000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (605004053 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((505959148212720913698465745322165118567069314701807714268621910688053768769753865226687762180804131779691872160365009578361139 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(605004053 / 1000000000 : ℝ)) ∧ Real.sin (-(605004053 / 1000000000 : ℝ)) ≤ -((22703295112099944959278784576314264129628816093542420418065944315931179876029786569623702294981009918652403 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340) (-(605004053 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 - (-(605004053 / 1000000000 : ℝ))| ≤ (580118772309 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 107) 340 - (-(605004053 / 1000000000 : ℝ)))]

theorem thL_107_cos : (205624919101041 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 107) ∧ Real.cos (11416334 / 100000 * Real.log 107) ≤ (411249954228347 / 500000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_107_sin : (-284382762939493 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 107) ∧ Real.sin (11416334 / 100000 * Real.log 107) ≤ (-284382646915621 / 500000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_107 : (205624919101041 / 250000000000000 : ℝ) ≤ cCG cZ 107 ∧ cCG cZ 107 ≤ (411249954228347 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_cos

theorem sCB_107 : (-284382762939493 / 500000000000000 : ℝ) ≤ sCG cZ 107 ∧ sCG cZ 107 ≤ (-284382646915621 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_sin

theorem thL_108_r_bounds : (4569880475290574601 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 ≤ (4569882804709425399 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_108
  have hl : (133631934789448477 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 108 ∧ 11416334 / 100000 * Real.log 108 ≤ (21381109575600297 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_108_eq : (11416334 / 100000 * Real.log 108) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_108_cos_r : (112173176726329 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) ≤ (897385646752691 / 1000000000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (114247041 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) (114247041 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 - (114247041 / 250000000 : ℝ)| ≤ (1164709425399 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 - (114247041 / 250000000 : ℝ))]

theorem thL_108_sin_r : (441247217845017 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) ≤ (441247450786909 / 1000000000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (114247041 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340) (114247041 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 - (114247041 / 250000000 : ℝ)| ≤ (1164709425399 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 108) 340 - (114247041 / 250000000 : ℝ))]

theorem thL_108_cos : (112173176726329 / 125000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 108) ∧ Real.cos (11416334 / 100000 * Real.log 108) ≤ (897385646752691 / 1000000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_108_sin : (441247217845017 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 108) ∧ Real.sin (11416334 / 100000 * Real.log 108) ≤ (441247450786909 / 1000000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_108 : (112173176726329 / 125000000000000 : ℝ) ≤ cCG cZ 108 ∧ cCG cZ 108 ≤ (897385646752691 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_cos

theorem sCB_108 : (441247217845017 / 1000000000000000 : ℝ) ≤ sCG cZ 108 ∧ sCG cZ 108 ≤ (441247450786909 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_sin

theorem thL_109_r_bounds : (-6160414973348084257 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 ≤ (-6160391626651915743 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_109
  have hl : (535579943288105177 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 109 ∧ 11416334 / 100000 * Real.log 109 ≤ (133894985880198307 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_109_eq : (11416334 / 100000 * Real.log 109) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 + π / 2) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_109_cos_r : (998102954852041 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) ≤ (249525797079751 / 250000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(61604033 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) (-(61604033 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 - (-(61604033 / 1000000000 : ℝ))| ≤ (11673348084257 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 - (-(61604033 / 1000000000 : ℝ)))]

theorem thL_109_sin_r : (-61565191991661 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) ≤ (-30782479262349 / 500000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (61604033 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((383367004186247451036138140582361695699449333901191691265485552096726865014647508884151093163489655108307306868695801851275713 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(61604033 / 1000000000 : ℝ)) ∧ Real.sin (-(61604033 / 1000000000 : ℝ)) ≤ -((2457480796065688788693192029099616248048700014212599570351900795648144314714823007009349422560160568117183 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341) (-(61604033 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 - (-(61604033 / 1000000000 : ℝ))| ≤ (11673348084257 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 109) 341 - (-(61604033 / 1000000000 : ℝ)))]

theorem thL_109_cos : (30782479262349 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 109) ∧ Real.cos (11416334 / 100000 * Real.log 109) ≤ (61565191991661 / 1000000000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_109_sin : (998102954852041 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 109) ∧ Real.sin (11416334 / 100000 * Real.log 109) ≤ (249525797079751 / 250000000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_109 : (30782479262349 / 500000000000000 : ℝ) ≤ cCG cZ 109 ∧ cCG cZ 109 ≤ (61565191991661 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_cos

theorem sCB_109 : (998102954852041 / 1000000000000000 : ℝ) ≤ sCG cZ 109 ∧ sCG cZ 109 ≤ (249525797079751 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_sin

theorem thL_111_r_bounds : (22167689943477888833 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 ≤ (22167701656522111167 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_111
  have hl : (537655697563410661 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 111 ∧ 11416334 / 100000 * Real.log 111 ≤ (268827848898492543 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_111_eq : (11416334 / 100000 * Real.log 111) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 + π) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_111_cos_r : (903317894921733 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) ≤ (903318129182739 / 1000000000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (110838479 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) (110838479 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 - (110838479 / 250000000 : ℝ)| ≤ (5856522111167 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 - (110838479 / 250000000 : ℝ))]

theorem thL_111_sin_r : (428971407684299 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) ≤ (428971641945189 / 1000000000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (110838479 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342) (110838479 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 - (110838479 / 250000000 : ℝ)| ≤ (5856522111167 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 111) 342 - (110838479 / 250000000 : ℝ))]

theorem thL_111_cos : (-903318129182739 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 111) ∧ Real.cos (11416334 / 100000 * Real.log 111) ≤ (-903317894921733 / 1000000000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_111_sin : (-428971641945189 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 111) ∧ Real.sin (11416334 / 100000 * Real.log 111) ≤ (-428971407684299 / 1000000000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_111 : (-903318129182739 / 1000000000000000 : ℝ) ≤ cCG cZ 111 ∧ cCG cZ 111 ≤ (-903317894921733 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_cos

theorem sCB_111 : (-428971641945189 / 1000000000000000 : ℝ) ≤ sCG cZ 111 ∧ sCG cZ 111 ≤ (-428971407684299 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_sin

theorem thL_112_r_bounds : (-10354920725644760411 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 ≤ (-10354897274355239589 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_112
  have hl : (134669897720979381 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 112 ∧ 11416334 / 100000 * Real.log 112 ≤ (134669897779476497 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_112_eq : (11416334 / 100000 * Real.log 112) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 + π + π / 2) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_112_cos_r : (497321732217627 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) ≤ (19892873978963 / 20000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(10354909 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) (-(10354909 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 - (-(10354909 / 100000000 : ℝ))| ≤ (11725644760411 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 - (-(10354909 / 100000000 : ℝ)))]

theorem thL_112_sin_r : (-51682128535259 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) ≤ (-103364022557621 / 1000000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (10354909 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((64365064859631867443933524202605094694537959609816323830955545513007522878850202624180370087546531742999975238029 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(10354909 / 100000000 : ℝ)) ∧ Real.sin (-(10354909 / 100000000 : ℝ)) ≤ -((41259656961302479130716530727711347920394641340240998269915472728820675987580206500340001926491 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343) (-(10354909 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 - (-(10354909 / 100000000 : ℝ))| ≤ (11725644760411 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 112) 343 - (-(10354909 / 100000000 : ℝ)))]

theorem thL_112_cos : (-51682128535259 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 112) ∧ Real.cos (11416334 / 100000 * Real.log 112) ≤ (-103364022557621 / 1000000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_112_sin : (-19892873978963 / 20000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 112) ∧ Real.sin (11416334 / 100000 * Real.log 112) ≤ (-497321732217627 / 500000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_112 : (-51682128535259 / 500000000000000 : ℝ) ≤ cCG cZ 112 ∧ cCG cZ 112 ≤ (-103364022557621 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_cos

theorem sCB_112 : (-19892873978963 / 20000000000000 : ℝ) ≤ sCG cZ 112 ∧ sCG cZ 112 ≤ (-497321732217627 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_sin

theorem thL_113_r_bounds : (-16488840184223125421 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 ≤ (-16488834315776874579 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_113
  have hl : (67461797851259439 / 125000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 113 ∧ 11416334 / 100000 * Real.log 113 ≤ (539694383044459937 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_113_eq : (11416334 / 100000 * Real.log 113) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_113_cos_r : (197566449539991 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) ≤ (395133016455981 / 500000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(65955349 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) (-(65955349 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 - (-(65955349 / 100000000 : ℝ))| ≤ (2934223125421 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 - (-(65955349 / 100000000 : ℝ)))]

theorem thL_113_sin_r : (-306382084401941 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) ≤ (-612763934065313 / 1000000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (65955349 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((381569449377774244128241560140206704311955726365281786422763653533088971584565700965373160323878292353511385864549 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(65955349 / 100000000 : ℝ)) ∧ Real.sin (-(65955349 / 100000000 : ℝ)) ≤ -((244595800882902117324481722980413084314976763697356960905589600475171468935874796821462974353651 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344) (-(65955349 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 - (-(65955349 / 100000000 : ℝ))| ≤ (2934223125421 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 113) 344 - (-(65955349 / 100000000 : ℝ)))]

theorem thL_113_cos : (197566449539991 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 113) ∧ Real.cos (11416334 / 100000 * Real.log 113) ≤ (395133016455981 / 500000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_113_sin : (-306382084401941 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 113) ∧ Real.sin (11416334 / 100000 * Real.log 113) ≤ (-612763934065313 / 1000000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_113 : (197566449539991 / 250000000000000 : ℝ) ≤ cCG cZ 113 ∧ cCG cZ 113 ≤ (395133016455981 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_cos

theorem sCB_113 : (-306382084401941 / 500000000000000 : ℝ) ≤ sCG cZ 113 ∧ sCG cZ 113 ≤ (-612763934065313 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_sin

theorem thL_114_r_bounds : (8657432614331299579 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 ≤ (8657438485668700421 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_114
  have hl : (540700233722017689 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 114 ∧ 11416334 / 100000 * Real.log 114 ≤ (540700233956780937 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_114_eq : (11416334 / 100000 * Real.log 114) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_114_cos_r : (470317879717809 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) ≤ (940635994289121 / 1000000000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (173148711 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) (173148711 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 - (173148711 / 500000000 : ℝ)| ≤ (2935668700421 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 - (173148711 / 500000000 : ℝ))]

theorem thL_114_sin_r : (169708623415263 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) ≤ (339417481684023 / 1000000000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (173148711 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344) (173148711 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 - (173148711 / 500000000 : ℝ)| ≤ (2935668700421 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 114) 344 - (173148711 / 500000000 : ℝ))]

theorem thL_114_cos : (470317879717809 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 114) ∧ Real.cos (11416334 / 100000 * Real.log 114) ≤ (940635994289121 / 1000000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_114_sin : (169708623415263 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 114) ∧ Real.sin (11416334 / 100000 * Real.log 114) ≤ (339417481684023 / 1000000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_114 : (470317879717809 / 500000000000000 : ℝ) ≤ cCG cZ 114 ∧ cCG cZ 114 ≤ (940635994289121 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_cos

theorem sCB_114 : (169708623415263 / 500000000000000 : ℝ) ≤ sCG cZ 114 ∧ sCG cZ 114 ≤ (339417481684023 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_sin

theorem thL_116_r_bounds : (30440016561762334557 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 ≤ (30440025998237665443 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_116
  have hl : (4239732290299089 / 7812500000000 : ℝ) ≤ 11416334 / 100000 * Real.log 116 ∧ 11416334 / 100000 * Real.log 116 ≤ (542685733393756347 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_116_eq : (11416334 / 100000 * Real.log 116) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 + π / 2) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_116_cos_r : (724146242066451 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) ≤ (724146478057091 / 1000000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (190250133 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) (190250133 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 - (190250133 / 250000000 : ℝ)| ≤ (4718237665443 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 - (190250133 / 250000000 : ℝ))]

theorem thL_116_sin_r : (344823101912607 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) ≤ (172411609935427 / 250000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (190250133 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345) (190250133 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 - (190250133 / 250000000 : ℝ)| ≤ (4718237665443 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 116) 345 - (190250133 / 250000000 : ℝ))]

theorem thL_116_cos : (-172411609935427 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 116) ∧ Real.cos (11416334 / 100000 * Real.log 116) ≤ (-344823101912607 / 500000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_116_sin : (724146242066451 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 116) ∧ Real.sin (11416334 / 100000 * Real.log 116) ≤ (724146478057091 / 1000000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_116 : (-172411609935427 / 250000000000000 : ℝ) ≤ cCG cZ 116 ∧ cCG cZ 116 ≤ (-344823101912607 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_cos

theorem sCB_116 : (724146242066451 / 1000000000000000 : ℝ) ≤ sCG cZ 116 ∧ sCG cZ 116 ≤ (724146478057091 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_sin

theorem thL_117_r_bounds : (17015293669584274469 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 ≤ (17015317330415725531 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_117
  have hl : (543665682007730073 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 117 ∧ 11416334 / 100000 * Real.log 117 ≤ (543665682243535523 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_117_eq : (11416334 / 100000 * Real.log 117) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 + π) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_117_cos_r : (246389685714249 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) ≤ (985558979465311 / 1000000000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (34030611 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) (34030611 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 - (34030611 / 200000000 : ℝ)| ≤ (11830415725531 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 - (34030611 / 200000000 : ℝ))]

theorem thL_117_sin_r : (16933307745713 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) ≤ (33866662813089 / 200000000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (34030611 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346) (34030611 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 - (34030611 / 200000000 : ℝ)| ≤ (11830415725531 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 117) 346 - (34030611 / 200000000 : ℝ))]

theorem thL_117_cos : (-985558979465311 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 117) ∧ Real.cos (11416334 / 100000 * Real.log 117) ≤ (-246389685714249 / 250000000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_117_sin : (-33866662813089 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 117) ∧ Real.sin (11416334 / 100000 * Real.log 117) ≤ (-16933307745713 / 100000000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_117 : (-985558979465311 / 1000000000000000 : ℝ) ≤ cCG cZ 117 ∧ cCG cZ 117 ≤ (-246389685714249 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_cos

theorem sCB_117 : (-33866662813089 / 200000000000000 : ℝ) ≤ sCG cZ 117 ∧ sCG cZ 117 ≤ (-16933307745713 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_sin

theorem thL_118_r_bounds : (-42903463215320512719 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 ≤ (-42903439584679487281 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_118
  have hl : (272318645382929149 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 118 ∧ 11416334 / 100000 * Real.log 118 ≤ (136159322750495583 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_118_eq : (11416334 / 100000 * Real.log 118) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 + π + π / 2) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_118_cos_r : (909367690730437 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) ≤ (90936792703693 / 100000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(214517257 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) (-(214517257 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 - (-(214517257 / 500000000 : ℝ))| ≤ (11815320512719 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 - (-(214517257 / 500000000 : ℝ)))]

theorem thL_118_sin_r : (-41599313271717 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) ≤ (-103998224102689 / 250000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (214517257 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((316210590129945214078103891158652013319510684265680212485818501668398227311743113591687074119529453007096548524878781959657 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(214517257 / 500000000 : ℝ)) ∧ Real.sin (-(214517257 / 500000000 : ℝ)) ≤ -((8107963849485722487014088444496765762845321087802860430458386991600172225032030441887043502146938988007 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347) (-(214517257 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 - (-(214517257 / 500000000 : ℝ))| ≤ (11815320512719 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 118) 347 - (-(214517257 / 500000000 : ℝ)))]

theorem thL_118_cos : (-41599313271717 / 100000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 118) ∧ Real.cos (11416334 / 100000 * Real.log 118) ≤ (-103998224102689 / 250000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_118_sin : (-90936792703693 / 100000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 118) ∧ Real.sin (11416334 / 100000 * Real.log 118) ≤ (-909367690730437 / 1000000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_118 : (-41599313271717 / 100000000000000 : ℝ) ≤ cCG cZ 118 ∧ cCG cZ 118 ≤ (-103998224102689 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_cos

theorem sCB_118 : (-90936792703693 / 100000000000000 : ℝ) ≤ sCG cZ 118 ∧ sCG cZ 118 ≤ (-909367690730437 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_sin

theorem thL_119_r_bounds : (106874959680256225091 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 ≤ (106875007119743774909 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_119
  have hl : (68200087524528801 / 125000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 119 ∧ 11416334 / 100000 * Real.log 119 ≤ (545600700432659809 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_119_eq : (11416334 / 100000 * Real.log 119) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 + π + π / 2) + ((86 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_119_cos_r : (860587035554761 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) ≤ (215146818188333 / 250000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (534374917 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) (534374917 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 - (534374917 / 1000000000 : ℝ)| ≤ (23719743774909 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 - (534374917 / 1000000000 : ℝ))]

theorem thL_119_sin_r : (509303081964581 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) ≤ (254651659581033 / 500000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (534374917 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347) (534374917 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 - (534374917 / 1000000000 : ℝ)| ≤ (23719743774909 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 119) 347 - (534374917 / 1000000000 : ℝ))]

theorem thL_119_cos : (509303081964581 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 119) ∧ Real.cos (11416334 / 100000 * Real.log 119) ≤ (254651659581033 / 500000000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_119_sin : (-215146818188333 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 119) ∧ Real.sin (11416334 / 100000 * Real.log 119) ≤ (-860587035554761 / 1000000000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_119 : (509303081964581 / 1000000000000000 : ℝ) ≤ cCG cZ 119 ∧ cCG cZ 119 ≤ (254651659581033 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_cos

theorem sCB_119 : (-215146818188333 / 250000000000000 : ℝ) ≤ sCG cZ 119 ∧ sCG cZ 119 ≤ (-860587035554761 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_sin

theorem thL_121_r_bounds : (-140890295127234822603 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 ≤ (-140890247672765177397 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_121
  have hl : (273751733287891373 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 121 ∧ 11416334 / 100000 * Real.log 121 ≤ (547503466812785803 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_121_eq : (11416334 / 100000 * Real.log 121) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 + π / 2) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_121_cos_r : (190491714418819 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) ≤ (380983547489403 / 500000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(704451357 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) (-(704451357 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 - (-(704451357 / 1000000000 : ℝ))| ≤ (23727234822603 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 - (-(704451357 / 1000000000 : ℝ)))]

theorem thL_121_sin_r : (-80951999726763 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) ≤ (-323807880270033 / 500000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (704451357 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((16595545473461958556606312509940415348549463224943713113501647407582037300267598618222591273137210932439315427524344189742399 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(704451357 / 1000000000 : ℝ)) ∧ Real.sin (-(704451357 / 1000000000 : ℝ)) ≤ -((319145105258051185599353864321672172673381236278864681061021460569299282936974535158575998289086455810347 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349) (-(704451357 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 - (-(704451357 / 1000000000 : ℝ))| ≤ (23727234822603 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 121) 349 - (-(704451357 / 1000000000 : ℝ)))]

theorem thL_121_cos : (323807880270033 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 121) ∧ Real.cos (11416334 / 100000 * Real.log 121) ≤ (80951999726763 / 125000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_121_sin : (190491714418819 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 121) ∧ Real.sin (11416334 / 100000 * Real.log 121) ≤ (380983547489403 / 500000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_121 : (323807880270033 / 500000000000000 : ℝ) ≤ cCG cZ 121 ∧ cCG cZ 121 ≤ (80951999726763 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_cos

theorem sCB_121 : (190491714418819 / 250000000000000 : ℝ) ≤ sCG cZ 121 ∧ sCG cZ 121 ≤ (380983547489403 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_sin

theorem thL_122_r_bounds : (23516979534139511127 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 ≤ (23517003265860488873 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_122
  have hl : (137110771961768617 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 122 ∧ 11416334 / 100000 * Real.log 122 ≤ (21937723523363101 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_122_eq : (11416334 / 100000 * Real.log 122) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 + π / 2) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_122_cos_r : (97247464535257 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) ≤ (972474882669781 / 1000000000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (117584957 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) (117584957 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 - (117584957 / 500000000 : ℝ)| ≤ (11865860488873 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 - (117584957 / 500000000 : ℝ))]

theorem thL_122_sin_r : (3640751676463 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) ≤ (116504172305421 / 500000000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (117584957 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349) (117584957 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 - (117584957 / 500000000 : ℝ)| ≤ (11865860488873 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 122) 349 - (117584957 / 500000000 : ℝ))]

theorem thL_122_cos : (-116504172305421 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 122) ∧ Real.cos (11416334 / 100000 * Real.log 122) ≤ (-3640751676463 / 15625000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_122_sin : (97247464535257 / 100000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 122) ∧ Real.sin (11416334 / 100000 * Real.log 122) ≤ (972474882669781 / 1000000000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_122 : (-116504172305421 / 500000000000000 : ℝ) ≤ cCG cZ 122 ∧ cCG cZ 122 ≤ (-3640751676463 / 15625000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_cos

theorem sCB_122 : (97247464535257 / 100000000000000 : ℝ) ≤ sCG cZ 122 ∧ sCG cZ 122 ≤ (972474882669781 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_sin

theorem thL_123_r_bounds : (-807351447775710539 / 2000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 ≤ (-807350972224289461 / 2000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_123
  have hl : (109875007731019723 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 123 ∧ 11416334 / 100000 * Real.log 123 ≤ (68671879861512709 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_123_eq : (11416334 / 100000 * Real.log 123) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 + π) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_123_cos_r : (919623308538621 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) ≤ (229905886578593 / 250000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(80735121 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) (-(80735121 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 - (-(80735121 / 200000000 : ℝ))| ≤ (237775710539 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 - (-(80735121 / 200000000 : ℝ)))]

theorem thL_123_sin_r : (-392801279436431 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) ≤ (-196400520830359 / 500000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (80735121 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1177982147408874841287368130436445246532193613297593744182111710908531000648257242105280476469338402866661717984061 / 2998927360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(80735121 / 200000000 : ℝ)) ∧ Real.sin (-(80735121 / 200000000 : ℝ)) ≤ -((3964362996087547311832728587684766130140730624577803944153705241318074641113397280495830081404959 / 10092544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350) (-(80735121 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 - (-(80735121 / 200000000 : ℝ))| ≤ (237775710539 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 123) 350 - (-(80735121 / 200000000 : ℝ)))]

theorem thL_123_cos : (-229905886578593 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 123) ∧ Real.cos (11416334 / 100000 * Real.log 123) ≤ (-919623308538621 / 1000000000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_123_sin : (196400520830359 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 123) ∧ Real.sin (11416334 / 100000 * Real.log 123) ≤ (392801279436431 / 1000000000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_123 : (-229905886578593 / 250000000000000 : ℝ) ≤ cCG cZ 123 ∧ cCG cZ 123 ≤ (-919623308538621 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_cos

theorem sCB_123 : (196400520830359 / 500000000000000 : ℝ) ≤ sCG cZ 123 ∧ sCG cZ 123 ≤ (392801279436431 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_sin

theorem thL_124_r_bounds : (1041457682548281461 / 2000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 ≤ (1041458157451718539 / 2000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_124
  have hl : (550299443219936619 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 124 ∧ 11416334 / 100000 * Real.log 124 ≤ (137574860864234919 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_124_eq : (11416334 / 100000 * Real.log 124) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 + π) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_124_cos_r : (433728312332863 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) ≤ (34698274484731 / 40000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (813639 / 1562500 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) (813639 / 1562500 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 - (813639 / 1562500 : ℝ)| ≤ (237451718539 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 - (813639 / 1562500 : ℝ))]

theorem thL_124_sin_r : (497512492514291 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) ≤ (124378182491511 / 250000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (813639 / 1562500 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350) (813639 / 1562500 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 - (813639 / 1562500 : ℝ)| ≤ (237451718539 / 2000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 124) 350 - (813639 / 1562500 : ℝ))]

theorem thL_124_cos : (-34698274484731 / 40000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 124) ∧ Real.cos (11416334 / 100000 * Real.log 124) ≤ (-433728312332863 / 500000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_124_sin : (-124378182491511 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 124) ∧ Real.sin (11416334 / 100000 * Real.log 124) ≤ (-497512492514291 / 1000000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_124 : (-34698274484731 / 40000000000000 : ℝ) ≤ cCG cZ 124 ∧ cCG cZ 124 ≤ (-433728312332863 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_cos

theorem sCB_124 : (-124378182491511 / 250000000000000 : ℝ) ≤ sCG cZ 124 ∧ sCG cZ 124 ≤ (-497512492514291 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_sin

theorem thL_126_r_bounds : (155316984835544529703 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 ≤ (155317032364455470297 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_126
  have hl : (138031523907296609 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 126 ∧ 11416334 / 100000 * Real.log 126 ≤ (552126095866189493 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_126_eq : (11416334 / 100000 * Real.log 126) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 + π + π / 2) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_126_cos_r : (713310938089031 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) ≤ (44581948489627 / 62500000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (776585043 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) (776585043 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 - (776585043 / 1000000000 : ℝ)| ≤ (23764455470297 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 - (776585043 / 1000000000 : ℝ))]

theorem thL_126_sin_r : (14016949302673 / 20000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) ≤ (350423851392103 / 500000000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (776585043 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351) (776585043 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 - (776585043 / 1000000000 : ℝ)| ≤ (23764455470297 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 126) 351 - (776585043 / 1000000000 : ℝ))]

theorem thL_126_cos : (14016949302673 / 20000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 126) ∧ Real.cos (11416334 / 100000 * Real.log 126) ≤ (350423851392103 / 500000000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_126_sin : (-44581948489627 / 62500000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 126) ∧ Real.sin (11416334 / 100000 * Real.log 126) ≤ (-713310938089031 / 1000000000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_126 : (14016949302673 / 20000000000000 : ℝ) ≤ cCG cZ 126 ∧ cCG cZ 126 ≤ (350423851392103 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_cos

theorem sCB_126 : (-44581948489627 / 62500000000000 : ℝ) ≤ sCG cZ 126 ∧ sCG cZ 126 ≤ (-713310938089031 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_sin

theorem thL_127_r_bounds : (676689332590200183 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 ≤ (676690817409799817 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_127
  have hl : (276514288662509021 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 127 ∧ 11416334 / 100000 * Real.log 127 ≤ (276514288781010549 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_127_eq : (11416334 / 100000 * Real.log 127) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_127_cos_r : (994144363611387 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) ≤ (994144601182523 / 1000000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (27067603 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) (27067603 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 - (27067603 / 250000000 : ℝ)| ≤ (742409799817 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 - (27067603 / 250000000 : ℝ))]

theorem thL_127_sin_r : (108058884169717 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) ≤ (54029560870427 / 500000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (27067603 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352) (27067603 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 - (27067603 / 250000000 : ℝ)| ≤ (742409799817 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 127) 352 - (27067603 / 250000000 : ℝ))]

theorem thL_127_cos : (994144363611387 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 127) ∧ Real.cos (11416334 / 100000 * Real.log 127) ≤ (994144601182523 / 1000000000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_127_sin : (108058884169717 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 127) ∧ Real.sin (11416334 / 100000 * Real.log 127) ≤ (54029560870427 / 500000000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_127 : (994144363611387 / 1000000000000000 : ℝ) ≤ cCG cZ 127 ∧ cCG cZ 127 ≤ (994144601182523 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_cos

theorem sCB_127 : (108058884169717 / 1000000000000000 : ℝ) ≤ sCG cZ 127 ∧ sCG cZ 127 ≤ (54029560870427 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_sin

theorem thL_128_r_bounds : (-56712269858602741181 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 ≤ (-56712246141397258819 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_128
  have hl : (553923980660181477 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 128 ∧ 11416334 / 100000 * Real.log 128 ≤ (276961990448592267 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_128_eq : (11416334 / 100000 * Real.log 128) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_128_cos_r : (210862529301117 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) ≤ (421725177189417 / 500000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(28356129 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) (-(28356129 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 - (-(28356129 / 50000000 : ℝ))| ≤ (11858602741181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 - (-(28356129 / 50000000 : ℝ)))]

theorem thL_128_sin_r : (-53720743400631 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) ≤ (-537207196834153 / 1000000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (28356129 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((24006451907843841695014319034922468778609446551552458306487522112475862443192043527700190478981976909402189 / 44687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(28356129 / 50000000 : ℝ)) ∧ Real.sin (-(28356129 / 50000000 : ℝ)) ≤ -((1292655102729810431192857703604037152754818153623938070222687633771713889519681926635703791 / 2406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353) (-(28356129 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 - (-(28356129 / 50000000 : ℝ))| ≤ (11858602741181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 128) 353 - (-(28356129 / 50000000 : ℝ)))]

theorem thL_128_cos : (537207196834153 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 128) ∧ Real.cos (11416334 / 100000 * Real.log 128) ≤ (53720743400631 / 100000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_128_sin : (210862529301117 / 250000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 128) ∧ Real.sin (11416334 / 100000 * Real.log 128) ≤ (421725177189417 / 500000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_128 : (537207196834153 / 1000000000000000 : ℝ) ≤ cCG cZ 128 ∧ cCG cZ 128 ≤ (53720743400631 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_cos

theorem sCB_128 : (210862529301117 / 250000000000000 : ℝ) ≤ sCG cZ 128 ∧ sCG cZ 128 ≤ (421725177189417 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_sin

theorem thL_129_r_bounds : (32131244619990258819 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 ≤ (32131268380009741181 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_129
  have hl : (554812415805395547 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 129 ∧ 11416334 / 100000 * Real.log 129 ≤ (138703104010599651 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_129_eq : (11416334 / 100000 * Real.log 129) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_129_cos_r : (29650674770601 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) ≤ (948821830259431 / 1000000000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (64262513 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) (64262513 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 - (64262513 / 200000000 : ℝ)| ≤ (11880009741181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 - (64262513 / 200000000 : ℝ))]

theorem thL_129_sin_r : (315812103672977 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) ≤ (78953085318293 / 250000000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (64262513 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353) (64262513 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 - (64262513 / 200000000 : ℝ)| ≤ (11880009741181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 129) 353 - (64262513 / 200000000 : ℝ))]

theorem thL_129_cos : (-78953085318293 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 129) ∧ Real.cos (11416334 / 100000 * Real.log 129) ≤ (-315812103672977 / 1000000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_129_sin : (29650674770601 / 31250000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 129) ∧ Real.sin (11416334 / 100000 * Real.log 129) ≤ (948821830259431 / 1000000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_129 : (-78953085318293 / 250000000000000 : ℝ) ≤ cCG cZ 129 ∧ cCG cZ 129 ≤ (-315812103672977 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_cos

theorem sCB_129 : (29650674770601 / 31250000000000 : ℝ) ≤ sCG cZ 129 ∧ sCG cZ 129 ≤ (948821830259431 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_sin

theorem thL_131_r_bounds : (50690984034603879081 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 ≤ (50691007765396120919 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_131
  have hl : (278284404762869721 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 131 ∧ 11416334 / 100000 * Real.log 131 ≤ (556568809762742499 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_131_eq : (11416334 / 100000 * Real.log 131) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 + π) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_131_cos_r : (21856217691639 / 25000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) ≤ (174849788994817 / 200000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (506909959 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) (506909959 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 - (506909959 / 1000000000 : ℝ)| ≤ (11865396120919 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 - (506909959 / 1000000000 : ℝ))]

theorem thL_131_sin_r : (121369496391721 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) ≤ (485478222874831 / 1000000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (506909959 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354) (506909959 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 - (506909959 / 1000000000 : ℝ)| ≤ (11865396120919 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 131) 354 - (506909959 / 1000000000 : ℝ))]

theorem thL_131_cos : (-174849788994817 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 131) ∧ Real.cos (11416334 / 100000 * Real.log 131) ≤ (-21856217691639 / 25000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_131_sin : (-485478222874831 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 131) ∧ Real.sin (11416334 / 100000 * Real.log 131) ≤ (-121369496391721 / 250000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_131 : (-174849788994817 / 200000000000000 : ℝ) ≤ cCG cZ 131 ∧ cCG cZ 131 ≤ (-21856217691639 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_cos

theorem sCB_131 : (-485478222874831 / 1000000000000000 : ℝ) ≤ sCG cZ 131 ∧ sCG cZ 131 ≤ (-121369496391721 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_sin

theorem thL_132_r_bounds : (-3914400434655643467 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 ≤ (-3914395685344356533 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_132
  have hl : (22297479039636721 / 40000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 132 ∧ 11416334 / 100000 * Real.log 132 ≤ (278718488113960541 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_132_eq : (11416334 / 100000 * Real.log 132) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 + π + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_132_cos_r : (980907803499991 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) ≤ (980908040965557 / 1000000000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(195719903 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) (-(195719903 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 - (-(195719903 / 1000000000 : ℝ))| ≤ (2374655643467 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 - (-(195719903 / 1000000000 : ℝ)))]

theorem thL_132_sin_r : (-1944728625839 / 10000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) ≤ (-38894525023667 / 200000000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (195719903 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1210985820993980011142652510051068229475818192942440406317919323081388027547119957944953283353926265323074287854005098890141023 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(195719903 / 1000000000 : ℝ)) ∧ Real.sin (-(195719903 / 1000000000 : ℝ)) ≤ -((7762729621756282118745341539899959143360746361465438743858824791852605690237459628564581680205927391046753 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355) (-(195719903 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 - (-(195719903 / 1000000000 : ℝ))| ≤ (2374655643467 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 132) 355 - (-(195719903 / 1000000000 : ℝ)))]

theorem thL_132_cos : (-1944728625839 / 10000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 132) ∧ Real.cos (11416334 / 100000 * Real.log 132) ≤ (-38894525023667 / 200000000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_132_sin : (-980908040965557 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 132) ∧ Real.sin (11416334 / 100000 * Real.log 132) ≤ (-980907803499991 / 1000000000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_132 : (-1944728625839 / 10000000000000 : ℝ) ≤ cCG cZ 132 ∧ cCG cZ 132 ≤ (-38894525023667 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_cos

theorem sCB_132 : (-980908040965557 / 1000000000000000 : ℝ) ≤ sCG cZ 132 ∧ sCG cZ 132 ≤ (-980907803499991 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_sin

theorem thL_133_r_bounds : (13317883625301656533 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 ≤ (13317888374698343467 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_133
  have hl : (558298590193920161 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 133 ∧ 11416334 / 100000 * Real.log 133 ≤ (558298590430923217 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_133_eq : (11416334 / 100000 * Real.log 133) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 + π + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_133_cos_r : (786364515791663 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) ≤ (393182376638683 / 500000000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (6658943 / 10000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) (6658943 / 10000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 - (6658943 / 10000000 : ℝ)| ≤ (2374698343467 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 - (6658943 / 10000000 : ℝ))]

theorem thL_133_sin_r : (12355250136521 / 20000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) ≤ (308881372148349 / 500000000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (6658943 / 10000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355) (6658943 / 10000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 - (6658943 / 10000000 : ℝ)| ≤ (2374698343467 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 133) 355 - (6658943 / 10000000 : ℝ))]

theorem thL_133_cos : (12355250136521 / 20000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 133) ∧ Real.cos (11416334 / 100000 * Real.log 133) ≤ (308881372148349 / 500000000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_133_sin : (-393182376638683 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 133) ∧ Real.sin (11416334 / 100000 * Real.log 133) ≤ (-786364515791663 / 1000000000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_133 : (12355250136521 / 20000000000000 : ℝ) ≤ cCG cZ 133 ∧ cCG cZ 133 ≤ (308881372148349 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_cos

theorem sCB_133 : (-393182376638683 / 500000000000000 : ℝ) ≤ sCG cZ 133 ∧ sCG cZ 133 ≤ (-786364515791663 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_sin

theorem thL_134_r_bounds : (-2487102080941422383 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 ≤ (-2487090219058577617 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_134
  have hl : (34947109393585273 / 62500000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 134 ∧ 11416334 / 100000 * Real.log 134 ≤ (22366150021374697 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_134_eq : (11416334 / 100000 * Real.log 134) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_134_cos_r : (249690751747453 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) ≤ (99876324422747 / 100000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(49741923 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) (-(49741923 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 - (-(49741923 / 1000000000 : ℝ))| ≤ (5930941422383 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 - (-(49741923 / 1000000000 : ℝ)))]

theorem thL_134_sin_r : (-49721531757017 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) ≤ (-49721294519359 / 1000000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (49741923 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((16547286292388924972429205216541074255974969984432916682175154632762698865624828270929714571897908815699981930997221600453 / 332800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(49741923 / 1000000000 : ℝ)) ∧ Real.sin (-(49741923 / 1000000000 : ℝ)) ≤ -((318217044084402403315946242434384664821755132617537453099315244716939115858970059919502971376115980329 / 6400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356) (-(49741923 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 - (-(49741923 / 1000000000 : ℝ))| ≤ (5930941422383 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 134) 356 - (-(49741923 / 1000000000 : ℝ)))]

theorem thL_134_cos : (249690751747453 / 250000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 134) ∧ Real.cos (11416334 / 100000 * Real.log 134) ≤ (99876324422747 / 100000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_134_sin : (-49721531757017 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 134) ∧ Real.sin (11416334 / 100000 * Real.log 134) ≤ (-49721294519359 / 1000000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_134 : (249690751747453 / 250000000000000 : ℝ) ≤ cCG cZ 134 ∧ cCG cZ 134 ≤ (99876324422747 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_cos

theorem sCB_134 : (-49721531757017 / 1000000000000000 : ℝ) ≤ sCG cZ 134 ∧ sCG cZ 134 ≤ (-49721294519359 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_sin

theorem thL_136_r_bounds : (14160261440890586621 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 ≤ (14160308959109413379 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_136
  have hl : (280422544986491273 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 136 ∧ 11416334 / 100000 * Real.log 136 ≤ (560845090209985603 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_136_eq : (11416334 / 100000 * Real.log 136) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 + π / 2) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_136_cos_r : (997494507092039 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) ≤ (498747372341567 / 500000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (35400713 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) (35400713 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 - (35400713 / 500000000 : ℝ)| ≤ (23759109413379 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 - (35400713 / 500000000 : ℝ))]

theorem thL_136_sin_r : (35371084651381 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) ≤ (70742406893857 / 1000000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (35400713 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357) (35400713 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 - (35400713 / 500000000 : ℝ)| ≤ (23759109413379 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 136) 357 - (35400713 / 500000000 : ℝ))]

theorem thL_136_cos : (-70742406893857 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 136) ∧ Real.cos (11416334 / 100000 * Real.log 136) ≤ (-35371084651381 / 500000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_136_sin : (997494507092039 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 136) ∧ Real.sin (11416334 / 100000 * Real.log 136) ≤ (498747372341567 / 500000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_136 : (-70742406893857 / 1000000000000000 : ℝ) ≤ cCG cZ 136 ∧ cCG cZ 136 ≤ (-35371084651381 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_cos

theorem sCB_136 : (997494507092039 / 1000000000000000 : ℝ) ≤ sCG cZ 136 ∧ sCG cZ 136 ≤ (498747372341567 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_sin

theorem thL_137_r_bounds : (-66362981370549368613 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 ≤ (-66362957629450631387 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_137
  have hl : (70210181897358437 / 125000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 137 ∧ 11416334 / 100000 * Real.log 137 ≤ (561681455415870553 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_137_eq : (11416334 / 100000 * Real.log 137) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 + π) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_137_cos_r : (393880743273599 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) ≤ (787761723973419 / 1000000000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(132725939 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) (-(132725939 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 - (-(132725939 / 200000000 : ℝ))| ≤ (11870549368613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 - (-(132725939 / 200000000 : ℝ)))]

theorem thL_137_sin_r : (-615980356428883 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) ≤ (-615980119017117 / 1000000000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (132725939 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3142223259805685605071954105443604430198839465931318783582917966170196470492890151773316766589074080950604463905940419 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(132725939 / 200000000 : ℝ)) ∧ Real.sin (-(132725939 / 200000000 : ℝ)) ≤ -((503561419840019060966316093058542038099476072817662147015998540037678133280057509086444968712252661 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358) (-(132725939 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 - (-(132725939 / 200000000 : ℝ))| ≤ (11870549368613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 137) 358 - (-(132725939 / 200000000 : ℝ)))]

theorem thL_137_cos : (-787761723973419 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 137) ∧ Real.cos (11416334 / 100000 * Real.log 137) ≤ (-393880743273599 / 500000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_137_sin : (615980119017117 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 137) ∧ Real.sin (11416334 / 100000 * Real.log 137) ≤ (615980356428883 / 1000000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_137 : (-787761723973419 / 1000000000000000 : ℝ) ≤ cCG cZ 137 ∧ cCG cZ 137 ≤ (-393880743273599 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_cos

theorem sCB_137 : (615980119017117 / 1000000000000000 : ℝ) ≤ sCG cZ 137 ∧ sCG cZ 137 ≤ (615980356428883 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_sin

theorem thL_138_r_bounds : (16665268231841331387 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 ≤ (16665291968158668613 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_138
  have hl : (562511737674891403 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 138 ∧ 11416334 / 100000 * Real.log 138 ≤ (28125586895594723 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_138_eq : (11416334 / 100000 * Real.log 138) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 + π) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_138_cos_r : (986145413047019 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) ≤ (986145650410193 / 1000000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (166652801 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) (166652801 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 - (166652801 / 1000000000 : ℝ)| ≤ (11868158668613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 - (166652801 / 1000000000 : ℝ))]

theorem thL_138_sin_r : (165882340462547 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) ≤ (165882577825721 / 1000000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (166652801 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358) (166652801 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 - (166652801 / 1000000000 : ℝ)| ≤ (11868158668613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 138) 358 - (166652801 / 1000000000 : ℝ))]

theorem thL_138_cos : (-986145650410193 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 138) ∧ Real.cos (11416334 / 100000 * Real.log 138) ≤ (-986145413047019 / 1000000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_138_sin : (-165882577825721 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 138) ∧ Real.sin (11416334 / 100000 * Real.log 138) ≤ (-165882340462547 / 1000000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_138 : (-986145650410193 / 1000000000000000 : ℝ) ≤ cCG cZ 138 ∧ cCG cZ 138 ≤ (-986145413047019 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_cos

theorem sCB_138 : (-165882577825721 / 1000000000000000 : ℝ) ≤ sCG cZ 138 ∧ sCG cZ 138 ≤ (-165882340462547 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_sin

theorem thL_139_r_bounds : (-57985602080808769643 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 ≤ (-57985578319191230357 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_139
  have hl : (281668012649586459 / 500000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 139 ∧ 11416334 / 100000 * Real.log 139 ≤ (281668012768087987 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_139_eq : (11416334 / 100000 * Real.log 139) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 + π + π / 2) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_139_cos_r : (167308298314561 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) ≤ (418270864595999 / 500000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(289927951 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) (-(289927951 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 - (-(289927951 / 500000000 : ℝ))| ≤ (11880808769643 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 - (-(289927951 / 500000000 : ℝ)))]

theorem thL_139_sin_r : (-547903517315803 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) ≤ (-136975819924873 / 250000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (289927951 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((59497172483576829218825431776328002888303367806810055203500153599847944855219537062981950118382155696530081104668984051193 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(289927951 / 500000000 : ℝ)) ∧ Real.sin (-(289927951 / 500000000 : ℝ)) ≤ -((10678979676536808439669577288794117725278927576899598127346202924787153598785336119658659748412977780049 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359) (-(289927951 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 - (-(289927951 / 500000000 : ℝ))| ≤ (11880808769643 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 139) 359 - (-(289927951 / 500000000 : ℝ)))]

theorem thL_139_cos : (-547903517315803 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 139) ∧ Real.cos (11416334 / 100000 * Real.log 139) ≤ (-136975819924873 / 250000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_139_sin : (-418270864595999 / 500000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 139) ∧ Real.sin (11416334 / 100000 * Real.log 139) ≤ (-167308298314561 / 200000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_139 : (-547903517315803 / 1000000000000000 : ℝ) ≤ cCG cZ 139 ∧ cCG cZ 139 ≤ (-136975819924873 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_cos

theorem sCB_139 : (-418270864595999 / 500000000000000 : ℝ) ≤ sCG cZ 139 ∧ sCG cZ 139 ≤ (-167308298314561 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_sin

theorem thL_141_r_bounds : (-2598598762603694623 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 ≤ (-2598597577396305377 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_141
  have hl : (141241739473410511 / 250000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 141 ∧ 11416334 / 100000 * Real.log 141 ≤ (564966958130645101 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_141_eq : (11416334 / 100000 * Real.log 141) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) + ((90 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_141_cos_r : (867958335343499 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) ≤ (216989643096447 / 250000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(259859817 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) (-(259859817 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 - (-(259859817 / 500000000 : ℝ))| ≤ (592603694623 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 - (-(259859817 / 500000000 : ℝ)))]

theorem thL_141_sin_r : (-496636929846879 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) ≤ (-62079586600671 / 125000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (259859817 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((221934575061368789273339022965347199097940110005324280522150058593830268545689766915216932610796246667610599051825924437 / 446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(259859817 / 500000000 : ℝ)) ∧ Real.sin (-(259859817 / 500000000 : ℝ)) ≤ -((17071890389334946518856093888531523767389500891320502012104909555142425826763841890853813910868258801 / 34375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360) (-(259859817 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 - (-(259859817 / 500000000 : ℝ))| ≤ (592603694623 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 141) 360 - (-(259859817 / 500000000 : ℝ)))]

theorem thL_141_cos : (867958335343499 / 1000000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 141) ∧ Real.cos (11416334 / 100000 * Real.log 141) ≤ (216989643096447 / 250000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_141_sin : (-496636929846879 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 141) ∧ Real.sin (11416334 / 100000 * Real.log 141) ≤ (-62079586600671 / 125000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_141 : (867958335343499 / 1000000000000000 : ℝ) ≤ cCG cZ 141 ∧ cCG cZ 141 ≤ (216989643096447 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_cos

theorem sCB_141 : (-496636929846879 / 1000000000000000 : ℝ) ≤ sCG cZ 141 ∧ sCG cZ 141 ≤ (-62079586600671 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_sin

theorem thL_142_r_bounds : (1435458310030100377 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 ≤ (1435459499969899623 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_142
  have hl : (565773769308168803 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 142 ∧ 11416334 / 100000 * Real.log 142 ≤ (28288688477258593 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_142_eq : (11416334 / 100000 * Real.log 142) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) + ((90 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_142_cos_r : (191814262951151 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) ≤ (959071552743717 / 1000000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (287091781 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) (287091781 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 - (287091781 / 1000000000 : ℝ)| ≤ (594969899623 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 - (287091781 / 1000000000 : ℝ))]

theorem thL_142_sin_r : (56632823548031 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) ≤ (70791088932029 / 250000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (287091781 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360) (287091781 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 - (287091781 / 1000000000 : ℝ)| ≤ (594969899623 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 142) 360 - (287091781 / 1000000000 : ℝ))]

theorem thL_142_cos : (191814262951151 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 142) ∧ Real.cos (11416334 / 100000 * Real.log 142) ≤ (959071552743717 / 1000000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_142_sin : (56632823548031 / 200000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 142) ∧ Real.sin (11416334 / 100000 * Real.log 142) ≤ (70791088932029 / 250000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_142 : (191814262951151 / 200000000000000 : ℝ) ≤ cCG cZ 142 ∧ cCG cZ 142 ≤ (959071552743717 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_cos

theorem sCB_142 : (56632823548031 / 200000000000000 : ℝ) ≤ sCG cZ 142 ∧ sCG cZ 142 ≤ (70791088932029 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_sin

theorem thL_143_r_bounds : (-48255513161795045797 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 ≤ (-48255489438204954203 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_143
  have hl : (566574918841572573 / 1000000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 143 ∧ 11416334 / 100000 * Real.log 143 ≤ (56657491907857563 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_143_eq : (11416334 / 100000 * Real.log 143) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 + π / 2) + ((90 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_143_cos_r : (885812058457657 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) ≤ (221453073923473 / 250000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(482555013 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) (-(482555013 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 - (-(482555013 / 1000000000 : ℝ))| ≤ (11861795045797 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 - (-(482555013 / 1000000000 : ℝ)))]

theorem thL_143_sin_r : (-464044067984799 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) ≤ (-92808766149777 / 200000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (482555013 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1698772089842158814959074758485843691013597666203809336189261715634302129988633894237829101452801714378171015489523062847153 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(482555013 / 1000000000 : ℝ)) ∧ Real.sin (-(482555013 / 1000000000 : ℝ)) ≤ -((228680858247976829054179458121823708808227134086958488288278909295708952776647713947232725220967886771123 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361) (-(482555013 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 - (-(482555013 / 1000000000 : ℝ))| ≤ (11861795045797 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 143) 361 - (-(482555013 / 1000000000 : ℝ)))]

theorem thL_143_cos : (92808766149777 / 200000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 143) ∧ Real.cos (11416334 / 100000 * Real.log 143) ≤ (464044067984799 / 1000000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_143_sin : (885812058457657 / 1000000000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 143) ∧ Real.sin (11416334 / 100000 * Real.log 143) ≤ (221453073923473 / 250000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_143 : (92808766149777 / 200000000000000 : ℝ) ≤ cCG cZ 143 ∧ cCG cZ 143 ≤ (464044067984799 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_cos

theorem sCB_143 : (885812058457657 / 1000000000000000 : ℝ) ≤ sCG cZ 143 ∧ sCG cZ 143 ≤ (221453073923473 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_sin

theorem thL_144_r_bounds : (62602286619125091233 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 ∧ PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 ≤ (62602334180874908767 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_144
  have hl : (113474097081210661 / 200000000000000 : ℝ) ≤ 11416334 / 100000 * Real.log 144 ∧ 11416334 / 100000 * Real.log 144 ≤ (283685242821528181 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_144_eq : (11416334 / 100000 * Real.log 144) = (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 + π / 2) + ((90 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_144_cos_r : (59463152116119 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) ∧ Real.cos (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) ≤ (29731583489583 / 31250000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (9781611 / 31250000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) (9781611 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 - (9781611 / 31250000 : ℝ)| ≤ (23780874908767 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 - (9781611 / 31250000 : ℝ))]

theorem thL_144_sin_r : (307925131915643 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) ∧ Real.sin (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) ≤ (153962684862197 / 500000000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (9781611 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361) (9781611 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 - (9781611 / 31250000 : ℝ)| ≤ (23780874908767 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (11416334 / 100000 * Real.log 144) 361 - (9781611 / 31250000 : ℝ))]

theorem thL_144_cos : (-153962684862197 / 500000000000000 : ℝ) ≤ Real.cos (11416334 / 100000 * Real.log 144) ∧ Real.cos (11416334 / 100000 * Real.log 144) ≤ (-307925131915643 / 1000000000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_144_sin : (59463152116119 / 62500000000000 : ℝ) ≤ Real.sin (11416334 / 100000 * Real.log 144) ∧ Real.sin (11416334 / 100000 * Real.log 144) ≤ (29731583489583 / 31250000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_144 : (-153962684862197 / 500000000000000 : ℝ) ≤ cCG cZ 144 ∧ cCG cZ 144 ≤ (-307925131915643 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_cos

theorem sCB_144 : (59463152116119 / 62500000000000 : ℝ) ≤ sCG cZ 144 ∧ sCG cZ 144 ≤ (29731583489583 / 31250000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_sin

end PsiOmega.Locate.Z2

#print axioms PsiOmega.Locate.Z2.cCB_144
#print axioms PsiOmega.Locate.Z2.sCB_144
