import DHLocate4Trig

/-! # Generated (`gen_locate_zero.py 4`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 17670246 / 100000`, `n ∈ NS` (part 2 of 2: `106 ≤ n ≤ 209`)

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate.Z4

theorem thL_106_r_bounds : (-5015293224663520787 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 ≤ (-5015290359336479213 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_106
  have hl : (164808231982847557 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 106 ∧ 17670246 / 100000 * Real.log 106 ≤ (824041160272083387 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_106_eq : (17670246 / 100000 * Real.log 106) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 + π / 2) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_106_cos_r : (809843061350113 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) ≤ (101230427440461 / 125000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(313455737 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) (-(313455737 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 - (-(313455737 / 500000000 : ℝ))| ≤ (1432663520787 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 - (-(313455737 / 500000000 : ℝ)))]

theorem thL_106_sin_r : (-117329303420619 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) ≤ (-586646158936843 / 1000000000000000 : ℝ) := by
  have hr := thL_106_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (313455737 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((63704292499569825557460078408804511260618836751675336202297164397924081968119023307587497474078724630002823012914076191071 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(313455737 / 500000000 : ℝ)) ∧ Real.sin (-(313455737 / 500000000 : ℝ)) ≤ -((1633443397423834255552912211152674158718028968125717043133347049676147487578634628660449692009503101041 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525) (-(313455737 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 - (-(313455737 / 500000000 : ℝ))| ≤ (1432663520787 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 106) 525 - (-(313455737 / 500000000 : ℝ)))]

theorem thL_106_cos : (586646158936843 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 106) ∧ Real.cos (17670246 / 100000 * Real.log 106) ≤ (117329303420619 / 200000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_106_sin : (809843061350113 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 106) ∧ Real.sin (17670246 / 100000 * Real.log 106) ≤ (101230427440461 / 125000000000000 : ℝ) := by
  have hc := thL_106_cos_r
  have hs := thL_106_sin_r
  rw [thL_106_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_106 : (586646158936843 / 1000000000000000 : ℝ) ≤ cCG cZ 106 ∧ cCG cZ 106 ≤ (117329303420619 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_cos

theorem sCB_106 : (809843061350113 / 1000000000000000 : ℝ) ≤ sCG cZ 106 ∧ sCG cZ 106 ≤ (101230427440461 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_106_sin

theorem thL_107_r_bounds : (-53851776146123671761 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 ≤ (-53851740253876328239 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_107
  have hl : (165140070026530877 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 107 ∧ 17670246 / 100000 * Real.log 107 ≤ (412850175245653039 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_107_eq : (17670246 / 100000 * Real.log 107) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 + π) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_107_cos_r : (429234861818179 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) ≤ (429235041280037 / 500000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(269258791 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) (-(269258791 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 - (-(269258791 / 500000000 : ℝ))| ≤ (17946123671761 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 - (-(269258791 / 500000000 : ℝ)))]

theorem thL_107_sin_r : (-512864123868989 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) ≤ (-512863764946463 / 1000000000000000 : ℝ) := by
  have hr := thL_107_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (269258791 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((389845513842421190648018339253005948679458810368580748236208828515763560807062831374839142829694326543313123591744484968071 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(269258791 / 500000000 : ℝ)) ∧ Real.sin (-(269258791 / 500000000 : ℝ)) ≤ -((9996038816471335584156739967120952439051287187204233854165362736828107936027069814608352354536758092809 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526) (-(269258791 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 - (-(269258791 / 500000000 : ℝ))| ≤ (17946123671761 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 107) 526 - (-(269258791 / 500000000 : ℝ)))]

theorem thL_107_cos : (-429235041280037 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 107) ∧ Real.cos (17670246 / 100000 * Real.log 107) ≤ (-429234861818179 / 500000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_107_sin : (512863764946463 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 107) ∧ Real.sin (17670246 / 100000 * Real.log 107) ≤ (512864123868989 / 1000000000000000 : ℝ) := by
  have hc := thL_107_cos_r
  have hs := thL_107_sin_r
  rw [thL_107_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_107 : (-429235041280037 / 500000000000000 : ℝ) ≤ cCG cZ 107 ∧ cCG cZ 107 ≤ (-429234861818179 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_cos

theorem sCB_107 : (512863764946463 / 1000000000000000 : ℝ) ≤ sCG cZ 107 ∧ sCG cZ 107 ≤ (512864123868989 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_107_sin

theorem thL_108_r_bounds : (-93111684218648267369 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 ≤ (-93111612181351732631 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_108
  have hl : (827344105799817277 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 108 ∧ 17670246 / 100000 * Real.log 108 ≤ (413672053079619129 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_108_eq : (17670246 / 100000 * Real.log 108) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 + π + π / 2) + ((131 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_108_cos_r : (223392729565253 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) ≤ (27924102451491 / 31250000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(465558241 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) (-(465558241 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 - (-(465558241 / 1000000000 : ℝ))| ≤ (36018648267369 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 - (-(465558241 / 1000000000 : ℝ)))]

theorem thL_108_sin_r : (-224460939742947 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) ≤ (-224460759649701 / 500000000000000 : ℝ) := by
  have hr := thL_108_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (465558241 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2795444759689389551509572878677076435728719643205043883129140932910628839591689910833522075282767341219887982127428163463533921 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(465558241 / 1000000000 : ℝ)) ∧ Real.sin (-(465558241 / 1000000000 : ℝ)) ≤ -((17919517690316290276814147013338027656413693225769124837160039808279309440104246502591994553714953105931359 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527) (-(465558241 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 - (-(465558241 / 1000000000 : ℝ))| ≤ (36018648267369 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 108) 527 - (-(465558241 / 1000000000 : ℝ)))]

theorem thL_108_cos : (-224460939742947 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 108) ∧ Real.cos (17670246 / 100000 * Real.log 108) ≤ (-224460759649701 / 500000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_108_sin : (-27924102451491 / 31250000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 108) ∧ Real.sin (17670246 / 100000 * Real.log 108) ≤ (-223392729565253 / 250000000000000 : ℝ) := by
  have hc := thL_108_cos_r
  have hs := thL_108_sin_r
  rw [thL_108_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_108 : (-224460939742947 / 500000000000000 : ℝ) ≤ cCG cZ 108 ∧ cCG cZ 108 ≤ (-224460759649701 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_cos

theorem sCB_108 : (-27924102451491 / 31250000000000 : ℝ) ≤ sCG cZ 108 ∧ sCG cZ 108 ≤ (-223392729565253 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_108_sin

theorem thL_109_r_bounds : (-2548431988325394041 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 ≤ (-2548429736674605959 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_109
  have hl : (828972711429682011 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 109 ∧ 17670246 / 100000 * Real.log 109 ≤ (414486355894918739 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_109_eq : (17670246 / 100000 * Real.log 109) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_109_cos_r : (918015612584683 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) ≤ (459007986424427 / 500000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(203874469 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) (-(203874469 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 - (-(203874469 / 500000000 : ℝ))| ≤ (1125825394041 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 - (-(203874469 / 500000000 : ℝ)))]

theorem thL_109_sin_r : (-396544004094261 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) ≤ (-396543643830133 / 1000000000000000 : ℝ) := by
  have hr := thL_109_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (203874469 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((301426591787615105444063449334149179390157961320744227680041896433246820267255879079429741212679393578477189426858337385909 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(203874469 / 500000000 : ℝ)) ∧ Real.sin (-(203874469 / 500000000 : ℝ)) ≤ -((7728886968913180876091281144927372832545910283475345678733192725264064793285311530614094858456299435331 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528) (-(203874469 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 - (-(203874469 / 500000000 : ℝ))| ≤ (1125825394041 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 109) 528 - (-(203874469 / 500000000 : ℝ)))]

theorem thL_109_cos : (918015612584683 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 109) ∧ Real.cos (17670246 / 100000 * Real.log 109) ≤ (459007986424427 / 500000000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_109_sin : (-396544004094261 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 109) ∧ Real.sin (17670246 / 100000 * Real.log 109) ≤ (-396543643830133 / 1000000000000000 : ℝ) := by
  have hc := thL_109_cos_r
  have hs := thL_109_sin_r
  rw [thL_109_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_109 : (918015612584683 / 1000000000000000 : ℝ) ≤ cCG cZ 109 ∧ cCG cZ 109 ≤ (459007986424427 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_cos

theorem sCB_109 : (-396544004094261 / 1000000000000000 : ℝ) ≤ sCG cZ 109 ∧ sCG cZ 109 ≤ (-396543643830133 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_109_sin

theorem thL_111_r_bounds : (-3364812621445118081 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 ≤ (-3364808998554881919 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_111
  have hl : (1300289956156113 / 1562500000000 : ℝ) ≤ 17670246 / 100000 * Real.log 111 ∧ 17670246 / 100000 * Real.log 111 ≤ (20804639307535993 / 25000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_111_eq : (17670246 / 100000 * Real.log 111) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 + π) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_111_cos_r : (943922159065787 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) ≤ (14748789396169 / 15625000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(336481081 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) (-(336481081 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 - (-(336481081 / 1000000000 : ℝ))| ≤ (1811445118081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 - (-(336481081 / 1000000000 : ℝ)))]

theorem thL_111_sin_r : (-165083869039361 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) ≤ (-330167375789697 / 1000000000000000 : ℝ) := by
  have hr := thL_111_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (336481081 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2055960244514506153923973619359966394221555544540128167092425589707075595755638288375140372860244879202476791450195032941265241 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(336481081 / 1000000000 : ℝ)) ∧ Real.sin (-(336481081 / 1000000000 : ℝ)) ≤ -((13179232336631445161419896756147801265482589957473352095722772053185778683690146854739085980566580151676119 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530) (-(336481081 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 - (-(336481081 / 1000000000 : ℝ))| ≤ (1811445118081 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 111) 530 - (-(336481081 / 1000000000 : ℝ)))]

theorem thL_111_cos : (-14748789396169 / 15625000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 111) ∧ Real.cos (17670246 / 100000 * Real.log 111) ≤ (-943922159065787 / 1000000000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_111_sin : (330167375789697 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 111) ∧ Real.sin (17670246 / 100000 * Real.log 111) ≤ (165083869039361 / 500000000000000 : ℝ) := by
  have hc := thL_111_cos_r
  have hs := thL_111_sin_r
  rw [thL_111_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_111 : (-14748789396169 / 15625000000000 : ℝ) ≤ cCG cZ 111 ∧ cCG cZ 111 ≤ (-943922159065787 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_cos

theorem sCB_111 : (330167375789697 / 1000000000000000 : ℝ) ≤ sCG cZ 111 ∧ sCG cZ 111 ≤ (165083869039361 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_111_sin

theorem thL_112_r_bounds : (-64498307884806362757 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 ≤ (-64498235315193637243 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_112
  have hl : (833770357988666073 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 112 ∧ 17670246 / 100000 * Real.log 112 ≤ (833770358350834323 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_112_eq : (17670246 / 100000 * Real.log 112) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 + π + π / 2) + ((132 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_112_cos_r : (948448593665427 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) ≤ (474224478256747 / 500000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(161245679 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) (-(161245679 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 - (-(161245679 / 500000000 : ℝ))| ≤ (36284806362757 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 - (-(161245679 / 500000000 : ℝ)))]

theorem thL_112_sin_r : (-7923266215273 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) ≤ (-39616285720357 / 125000000000000 : ℝ) := by
  have hr := thL_112_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (161245679 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((34415677513366169880537025174842092345135022795849256174480433221598215808837876738676962053415991439075779286054224468377 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(161245679 / 500000000 : ℝ)) ∧ Real.sin (-(161245679 / 500000000 : ℝ)) ≤ -((882453269573491352932170299306454234877720631147057437353342460082532437441255585518456804382928378503 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531) (-(161245679 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 - (-(161245679 / 500000000 : ℝ))| ≤ (36284806362757 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 112) 531 - (-(161245679 / 500000000 : ℝ)))]

theorem thL_112_cos : (-7923266215273 / 25000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 112) ∧ Real.cos (17670246 / 100000 * Real.log 112) ≤ (-39616285720357 / 125000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_112_sin : (-474224478256747 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 112) ∧ Real.sin (17670246 / 100000 * Real.log 112) ≤ (-948448593665427 / 1000000000000000 : ℝ) := by
  have hc := thL_112_cos_r
  have hs := thL_112_sin_r
  rw [thL_112_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_112 : (-7923266215273 / 25000000000000 : ℝ) ≤ cCG cZ 112 ∧ cCG cZ 112 ≤ (-39616285720357 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_cos

theorem sCB_112 : (-474224478256747 / 500000000000000 : ℝ) ≤ sCG cZ 112 ∧ sCG cZ 112 ≤ (-948448593665427 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_112_sin

theorem thL_113_r_bounds : (-8064724796940939241 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 ≤ (-8064715703059060759 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_113
  have hl : (417670528431990759 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 113 ∧ 17670246 / 100000 * Real.log 113 ≤ (835341057226762639 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_113_eq : (17670246 / 100000 * Real.log 113) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_113_cos_r : (237104425800081 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) ≤ (948418066955603 / 1000000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(32258881 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) (-(32258881 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 - (-(32258881 / 100000000 : ℝ))| ≤ (4546940939241 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 - (-(32258881 / 100000000 : ℝ)))]

theorem thL_113_sin_r : (-317023075789483 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) ≤ (-158511356017103 / 500000000000000 : ℝ) := by
  have hr := thL_113_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (32258881 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((197410815446524943384360417151223251016776395290710786461773442301697152159484187396168207512414865518077920600641 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(32258881 / 100000000 : ℝ)) ∧ Real.sin (-(32258881 / 100000000 : ℝ)) ≤ -((126545394517003142574824807960830443087254038767286641066609499036929459441960976775871782880319 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532) (-(32258881 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 - (-(32258881 / 100000000 : ℝ))| ≤ (4546940939241 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 113) 532 - (-(32258881 / 100000000 : ℝ)))]

theorem thL_113_cos : (237104425800081 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 113) ∧ Real.cos (17670246 / 100000 * Real.log 113) ≤ (948418066955603 / 1000000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_113_sin : (-317023075789483 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 113) ∧ Real.sin (17670246 / 100000 * Real.log 113) ≤ (-158511356017103 / 500000000000000 : ℝ) := by
  have hc := thL_113_cos_r
  have hs := thL_113_sin_r
  rw [thL_113_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_113 : (237104425800081 / 250000000000000 : ℝ) ≤ cCG cZ 113 ∧ cCG cZ 113 ≤ (948418066955603 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_cos

theorem sCB_113 : (-317023075789483 / 1000000000000000 : ℝ) ≤ sCG cZ 113 ∧ sCG cZ 113 ≤ (-158511356017103 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_113_sin

theorem thL_114_r_bounds : (-67305075765972010451 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 ≤ (-67305003034027989549 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_114
  have hl : (418448958401425019 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 114 ∧ 17670246 / 100000 * Real.log 114 ≤ (418448958583108751 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_114_eq : (17670246 / 100000 * Real.log 114) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 + π / 2) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_114_cos_r : (23597689794749 / 25000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) ≤ (471953977724843 / 500000000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(336525197 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) (-(336525197 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 - (-(336525197 / 1000000000 : ℝ))| ≤ (36365972010451 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 - (-(336525197 / 1000000000 : ℝ)))]

theorem thL_114_sin_r : (-41276172565091 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) ≤ (-165104508430503 / 500000000000000 : ℝ) := by
  have hr := thL_114_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (336525197 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2056219548599361683749308318215843474558084718384696099498617230281343117605613962200244054246147565563704677825824799656337277 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(336525197 / 1000000000 : ℝ)) ∧ Real.sin (-(336525197 / 1000000000 : ℝ)) ≤ -((13180894542303595985883890181773527040744778450507951740985978111463092716226728090349591330627330315894347 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533) (-(336525197 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 - (-(336525197 / 1000000000 : ℝ))| ≤ (36365972010451 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 114) 533 - (-(336525197 / 1000000000 : ℝ)))]

theorem thL_114_cos : (165104508430503 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 114) ∧ Real.cos (17670246 / 100000 * Real.log 114) ≤ (41276172565091 / 125000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_114_sin : (23597689794749 / 25000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 114) ∧ Real.sin (17670246 / 100000 * Real.log 114) ≤ (471953977724843 / 500000000000000 : ℝ) := by
  have hc := thL_114_cos_r
  have hs := thL_114_sin_r
  rw [thL_114_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_114 : (165104508430503 / 500000000000000 : ℝ) ≤ cCG cZ 114 ∧ cCG cZ 114 ≤ (41276172565091 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_cos

theorem sCB_114 : (23597689794749 / 25000000000000 : ℝ) ≤ sCG cZ 114 ∧ sCG cZ 114 ≤ (471953977724843 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_114_sin

theorem thL_116_r_bounds : (-8099086254019134239 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 ≤ (-8099078945980865761 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_116
  have hl : (419985540261752349 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 116 ∧ 17670246 / 100000 * Real.log 116 ≤ (104996385110996331 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_116_eq : (17670246 / 100000 * Real.log 116) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 + π + π / 2) + ((133 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_116_cos_r : (919120287138387 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) ≤ (459560326270171 / 500000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(40495413 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) (-(40495413 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 - (-(40495413 / 100000000 : ℝ))| ≤ (3654019134239 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 - (-(40495413 / 100000000 : ℝ)))]

theorem thL_116_sin_r : (-15759071337211 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) ≤ (-9849410450709 / 25000000000000 : ℝ) := by
  have hr := thL_116_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (40495413 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((144226953994988834544973499631329367457150531080835149163769145041728089042167686697000320724426352472222288353 / 366080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(40495413 / 100000000 : ℝ)) ∧ Real.sin (-(40495413 / 100000000 : ℝ)) ≤ -((277359526913439176067464346716100295616915304198999635284111643372138402401015651863207654789 / 704000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535) (-(40495413 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 - (-(40495413 / 100000000 : ℝ))| ≤ (3654019134239 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 116) 535 - (-(40495413 / 100000000 : ℝ)))]

theorem thL_116_cos : (-15759071337211 / 40000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 116) ∧ Real.cos (17670246 / 100000 * Real.log 116) ≤ (-9849410450709 / 25000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_116_sin : (-459560326270171 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 116) ∧ Real.sin (17670246 / 100000 * Real.log 116) ≤ (-919120287138387 / 1000000000000000 : ℝ) := by
  have hc := thL_116_cos_r
  have hs := thL_116_sin_r
  rw [thL_116_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_116 : (-15759071337211 / 40000000000000 : ℝ) ≤ cCG cZ 116 ∧ cCG cZ 116 ≤ (-9849410450709 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_cos

theorem sCB_116 : (-459560326270171 / 500000000000000 : ℝ) ≤ sCG cZ 116 ∧ sCG cZ 116 ≤ (-919120287138387 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_116_sin

theorem thL_117_r_bounds : (-5737275157451563659 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 ≤ (-5737270592548436341 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_117
  have hl : (6731902793197441 / 8000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 117 ∧ 17670246 / 100000 * Real.log 117 ≤ (841487849514660713 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_117_eq : (17670246 / 100000 * Real.log 117) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_117_cos_r : (89650386503979 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) ≤ (28015757194757 / 31250000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(45898183 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) (-(45898183 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 - (-(45898183 / 100000000 : ℝ))| ≤ (2282451563659 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 - (-(45898183 / 100000000 : ℝ)))]

theorem thL_117_sin_r : (-13844866432313 / 31250000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) ≤ (-221517680320879 / 500000000000000 : ℝ) := by
  have hr := thL_117_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (45898183 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((275879154288164370358879848668239720755615107730067881194901549473794610091807389355740166829725369020217479626663 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(45898183 / 100000000 : ℝ)) ∧ Real.sin (-(45898183 / 100000000 : ℝ)) ≤ -((176845611723179717012266083510482491447426515628987204404454035737750893208350377793650270497833 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536) (-(45898183 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 - (-(45898183 / 100000000 : ℝ))| ≤ (2282451563659 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 117) 536 - (-(45898183 / 100000000 : ℝ)))]

theorem thL_117_cos : (89650386503979 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 117) ∧ Real.cos (17670246 / 100000 * Real.log 117) ≤ (28015757194757 / 31250000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_117_sin : (-13844866432313 / 31250000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 117) ∧ Real.sin (17670246 / 100000 * Real.log 117) ≤ (-221517680320879 / 500000000000000 : ℝ) := by
  have hc := thL_117_cos_r
  have hs := thL_117_sin_r
  rw [thL_117_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_117 : (89650386503979 / 100000000000000 : ℝ) ≤ cCG cZ 117 ∧ cCG cZ 117 ≤ (28015757194757 / 31250000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_cos

theorem sCB_117 : (-13844866432313 / 31250000000000 : ℝ) ≤ sCG cZ 117 ∧ sCG cZ 117 ≤ (-221517680320879 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_117_sin

theorem thL_118_r_bounds : (-52591853881175447349 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 ≤ (-52591817318824552651 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_118
  have hl : (105373963618774693 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 118 ∧ 17670246 / 100000 * Real.log 118 ≤ (842991709315671239 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_118_eq : (17670246 / 100000 * Real.log 118) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_118_cos_r : (432431551003691 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) ≤ (864863467631827 / 1000000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(131479589 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) (-(131479589 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 - (-(131479589 / 250000000 : ℝ))| ≤ (18281175447349 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 - (-(131479589 / 250000000 : ℝ)))]

theorem thL_118_sin_r : (-502007651451653 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) ≤ (-100401457165621 / 200000000000000 : ℝ) := by
  have hr := thL_118_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (131479589 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((46581193044423913733323114070316142027633356048178846210844557207195479309320470010661774790290059909725463336673666869 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(131479589 / 250000000 : ℝ)) ∧ Real.sin (-(131479589 / 250000000 : ℝ)) ≤ -((4777558260966195377961200815673139209576789621949616307037639213286630943394765584142285467166435011 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537) (-(131479589 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 - (-(131479589 / 250000000 : ℝ))| ≤ (18281175447349 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 118) 537 - (-(131479589 / 250000000 : ℝ)))]

theorem thL_118_cos : (100401457165621 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 118) ∧ Real.cos (17670246 / 100000 * Real.log 118) ≤ (502007651451653 / 1000000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_118_sin : (432431551003691 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 118) ∧ Real.sin (17670246 / 100000 * Real.log 118) ≤ (864863467631827 / 1000000000000000 : ℝ) := by
  have hc := thL_118_cos_r
  have hs := thL_118_sin_r
  rw [thL_118_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_118 : (100401457165621 / 200000000000000 : ℝ) ≤ cCG cZ 118 ∧ cCG cZ 118 ≤ (502007651451653 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_cos

theorem sCB_118 : (432431551003691 / 500000000000000 : ℝ) ≤ sCG cZ 118 ∧ sCG cZ 118 ≤ (864863467631827 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_118_sin

theorem thL_119_r_bounds : (-60554601621021814843 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 ≤ (-60554564978978185157 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_119
  have hl : (844482877799444163 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 119 ∧ 17670246 / 100000 * Real.log 119 ≤ (422241439082695253 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_119_eq : (17670246 / 100000 * Real.log 119) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 + π) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_119_cos_r : (822191342796613 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) ≤ (6577533673777 / 8000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(605545833 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) (-(605545833 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 - (-(605545833 / 1000000000 : ℝ))| ≤ (18321021814843 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 - (-(605545833 / 1000000000 : ℝ)))]

theorem thL_119_sin_r : (-569211123507601 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) ≤ (-569210757086927 / 1000000000000000 : ℝ) := by
  have hr := thL_119_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (605545833 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2083767410240656317468710769248968500274445121693638860771263216979585824974267462967638808272800519510194150899734908701013 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(605545833 / 1000000000 : ℝ)) ∧ Real.sin (-(605545833 / 1000000000 : ℝ)) ≤ -((280507151378433395403934501984750188434324598005118755154517544933024693630523456803154806481164605083543 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538) (-(605545833 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 - (-(605545833 / 1000000000 : ℝ))| ≤ (18321021814843 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 119) 538 - (-(605545833 / 1000000000 : ℝ)))]

theorem thL_119_cos : (-6577533673777 / 8000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 119) ∧ Real.cos (17670246 / 100000 * Real.log 119) ≤ (-822191342796613 / 1000000000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_119_sin : (569210757086927 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 119) ∧ Real.sin (17670246 / 100000 * Real.log 119) ≤ (569211123507601 / 1000000000000000 : ℝ) := by
  have hc := thL_119_cos_r
  have hs := thL_119_sin_r
  rw [thL_119_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_119 : (-6577533673777 / 8000000000000 : ℝ) ≤ cCG cZ 119 ∧ cCG cZ 119 ≤ (-822191342796613 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_cos

theorem sCB_119 : (569210757086927 / 1000000000000000 : ℝ) ≤ sCG cZ 119 ∧ sCG cZ 119 ≤ (569211123507601 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_119_sin

theorem thL_121_r_bounds : (76876683126242376497 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 ≤ (76876719873757623503 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_121
  have hl : (211856996743588151 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 121 ∧ 17670246 / 100000 * Real.log 121 ≤ (423713993670593427 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_121_eq : (17670246 / 100000 * Real.log 121) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 + π + π / 2) + ((134 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_121_cos_r : (359384132085957 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) ≤ (718768631736029 / 1000000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (153753403 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) (153753403 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 - (153753403 / 200000000 : ℝ)| ≤ (18373757623503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 - (153753403 / 200000000 : ℝ))]

theorem thL_121_sin_r : (347624676435707 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) ≤ (173812430087957 / 250000000000000 : ℝ) := by
  have hr := thL_121_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (153753403 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539) (153753403 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 - (153753403 / 200000000 : ℝ)| ≤ (18373757623503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 121) 539 - (153753403 / 200000000 : ℝ))]

theorem thL_121_cos : (347624676435707 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 121) ∧ Real.cos (17670246 / 100000 * Real.log 121) ≤ (173812430087957 / 250000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_121_sin : (-718768631736029 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 121) ∧ Real.sin (17670246 / 100000 * Real.log 121) ≤ (-359384132085957 / 500000000000000 : ℝ) := by
  have hc := thL_121_cos_r
  have hs := thL_121_sin_r
  rw [thL_121_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_121 : (347624676435707 / 500000000000000 : ℝ) ≤ cCG cZ 121 ∧ cCG cZ 121 ≤ (173812430087957 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_cos

theorem sCB_121 : (-718768631736029 / 1000000000000000 : ℝ) ≤ sCG cZ 121 ∧ sCG cZ 121 ≤ (-359384132085957 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_121_sin

theorem thL_122_r_bounds : (6523199495585896131 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 ≤ (6523203164414103869 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_122
  have hl : (212220584104700691 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 122 ∧ 17670246 / 100000 * Real.log 122 ≤ (848882336785637013 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_122_eq : (17670246 / 100000 * Real.log 122) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_122_cos_r : (99334670092313 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) ≤ (794677727633719 / 1000000000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (652320133 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) (652320133 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 - (652320133 / 1000000000 : ℝ)| ≤ (1834414103869 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 - (652320133 / 1000000000 : ℝ))]

theorem thL_122_sin_r : (607031612065031 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) ≤ (24281279157939 / 40000000000000 : ℝ) := by
  have hr := thL_122_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (652320133 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540) (652320133 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 - (652320133 / 1000000000 : ℝ)| ≤ (1834414103869 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 122) 540 - (652320133 / 1000000000 : ℝ))]

theorem thL_122_cos : (99334670092313 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 122) ∧ Real.cos (17670246 / 100000 * Real.log 122) ≤ (794677727633719 / 1000000000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_122_sin : (607031612065031 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 122) ∧ Real.sin (17670246 / 100000 * Real.log 122) ≤ (24281279157939 / 40000000000000 : ℝ) := by
  have hc := thL_122_cos_r
  have hs := thL_122_sin_r
  rw [thL_122_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_122 : (99334670092313 / 125000000000000 : ℝ) ≤ cCG cZ 122 ∧ cCG cZ 122 ≤ (794677727633719 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_cos

theorem sCB_122 : (607031612065031 / 1000000000000000 : ℝ) ≤ sCG cZ 122 ∧ sCG cZ 122 ≤ (24281279157939 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_122_sin

theorem thL_123_r_bounds : (104800138889520598773 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 ≤ (104800212310479401227 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_123
  have hl : (425162406745243337 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 123 ∧ 17670246 / 100000 * Real.log 123 ≤ (850324813857320923 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_123_eq : (17670246 / 100000 * Real.log 123) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 + π / 2) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_123_cos_r : (865824099023477 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) ≤ (432912233064583 / 500000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (262000439 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) (262000439 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 - (262000439 / 500000000 : ℝ)| ≤ (36710479401227 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 - (262000439 / 500000000 : ℝ))]

theorem thL_123_sin_r : (250174003455697 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) ≤ (20013934960649 / 40000000000000 : ℝ) := by
  have hr := thL_123_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (262000439 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541) (262000439 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 - (262000439 / 500000000 : ℝ)| ≤ (36710479401227 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 123) 541 - (262000439 / 500000000 : ℝ))]

theorem thL_123_cos : (-20013934960649 / 40000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 123) ∧ Real.cos (17670246 / 100000 * Real.log 123) ≤ (-250174003455697 / 500000000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_123_sin : (865824099023477 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 123) ∧ Real.sin (17670246 / 100000 * Real.log 123) ≤ (432912233064583 / 500000000000000 : ℝ) := by
  have hc := thL_123_cos_r
  have hs := thL_123_sin_r
  rw [thL_123_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_123 : (-20013934960649 / 40000000000000 : ℝ) ≤ cCG cZ 123 ∧ cCG cZ 123 ≤ (-250174003455697 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_cos

theorem sCB_123 : (865824099023477 / 1000000000000000 : ℝ) ≤ sCG cZ 123 ∧ sCG cZ 123 ≤ (432912233064583 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_123_sin

theorem thL_124_r_bounds : (19200066713601481133 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 ≤ (19200085086398518867 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_124
  have hl : (106469451307215961 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 124 ∧ 17670246 / 100000 * Real.log 124 ≤ (425877805412280969 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_124_eq : (17670246 / 100000 * Real.log 124) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 + π) + ((135 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_124_cos_r : (115896596990937 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) ≤ (927173143383459 / 1000000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (192000759 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) (192000759 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 - (192000759 / 500000000 : ℝ)| ≤ (9186398518867 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 - (192000759 / 500000000 : ℝ))]

theorem thL_124_sin_r : (74926674882151 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) ≤ (374633741866697 / 1000000000000000 : ℝ) := by
  have hr := thL_124_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (192000759 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542) (192000759 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 - (192000759 / 500000000 : ℝ)| ≤ (9186398518867 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 124) 542 - (192000759 / 500000000 : ℝ))]

theorem thL_124_cos : (-927173143383459 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 124) ∧ Real.cos (17670246 / 100000 * Real.log 124) ≤ (-115896596990937 / 125000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_124_sin : (-374633741866697 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 124) ∧ Real.sin (17670246 / 100000 * Real.log 124) ≤ (-74926674882151 / 200000000000000 : ℝ) := by
  have hc := thL_124_cos_r
  have hs := thL_124_sin_r
  rw [thL_124_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_124 : (-927173143383459 / 1000000000000000 : ℝ) ≤ cCG cZ 124 ∧ cCG cZ 124 ≤ (-115896596990937 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_cos

theorem sCB_124 : (-374633741866697 / 1000000000000000 : ℝ) ≤ sCG cZ 124 ∧ sCG cZ 124 ≤ (-74926674882151 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_124_sin

theorem thL_126_r_bounds : (217838615956133941 / 3125000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 ≤ (217839765293866059 / 3125000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_126
  have hl : (854582910134483549 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 126 ∧ 17670246 / 100000 * Real.log 126 ≤ (427291455250658899 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_126_eq : (17670246 / 100000 * Real.log 126) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_126_cos_r : (997571159461141 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) ≤ (15587055113269 / 15625000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (69708541 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) (69708541 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 - (69708541 / 1000000000 : ℝ)| ≤ (574668866059 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 - (69708541 / 1000000000 : ℝ))]

theorem thL_126_sin_r : (8706489407483 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) ≤ (69652283047939 / 1000000000000000 : ℝ) := by
  have hr := thL_126_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (69708541 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544) (69708541 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 - (69708541 / 1000000000 : ℝ)| ≤ (574668866059 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 126) 544 - (69708541 / 1000000000 : ℝ))]

theorem thL_126_cos : (997571159461141 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 126) ∧ Real.cos (17670246 / 100000 * Real.log 126) ≤ (15587055113269 / 15625000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_126_sin : (8706489407483 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 126) ∧ Real.sin (17670246 / 100000 * Real.log 126) ≤ (69652283047939 / 1000000000000000 : ℝ) := by
  have hc := thL_126_cos_r
  have hs := thL_126_sin_r
  rw [thL_126_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_126 : (997571159461141 / 1000000000000000 : ℝ) ≤ cCG cZ 126 ∧ cCG cZ 126 ≤ (15587055113269 / 15625000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_cos

theorem sCB_126 : (8706489407483 / 125000000000000 : ℝ) ≤ sCG cZ 126 ∧ sCG cZ 126 ≤ (69652283047939 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_126_sin

theorem thL_127_r_bounds : (-2084466074952870393 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 ≤ (-2084458725047129607 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_127
  have hl : (213994943700033013 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 127 ∧ 17670246 / 100000 * Real.log 127 ≤ (855979775166966301 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_127_eq : (17670246 / 100000 * Real.log 127) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 + π / 2) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_127_cos_r : (994573501476717 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) ≤ (198914773794401 / 200000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(1302789 / 12500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) (-(1302789 / 12500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 - (-(1302789 / 12500000 : ℝ))| ≤ (3674952870393 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 - (-(1302789 / 12500000 : ℝ)))]

theorem thL_127_sin_r : (-6502169977769 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) ≤ (-13004294018627 / 125000000000000 : ℝ) := by
  have hr := thL_127_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (1302789 / 12500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((484933007660120895794154140281890721052237355116132108564446408825070886483926194997627376362052183 / 4661269485950469970703125000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(1302789 / 12500000 : ℝ)) ∧ Real.sin (-(1302789 / 12500000 : ℝ)) ≤ -((59684062481245648713110889724441144799648921424520591720813591975234017392927393331 / 573694705963134765625000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545) (-(1302789 / 12500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 - (-(1302789 / 12500000 : ℝ))| ≤ (3674952870393 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 127) 545 - (-(1302789 / 12500000 : ℝ)))]

theorem thL_127_cos : (13004294018627 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 127) ∧ Real.cos (17670246 / 100000 * Real.log 127) ≤ (6502169977769 / 62500000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_127_sin : (994573501476717 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 127) ∧ Real.sin (17670246 / 100000 * Real.log 127) ≤ (198914773794401 / 200000000000000 : ℝ) := by
  have hc := thL_127_cos_r
  have hs := thL_127_sin_r
  rw [thL_127_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_127 : (13004294018627 / 125000000000000 : ℝ) ≤ cCG cZ 127 ∧ cCG cZ 127 ≤ (6502169977769 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_cos

theorem sCB_127 : (994573501476717 / 1000000000000000 : ℝ) ≤ sCG cZ 127 ∧ sCG cZ 127 ≤ (198914773794401 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_127_sin

theorem thL_128_r_bounds : (-14455543926628845021 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 ≤ (-14455525573371154979 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_128
  have hl : (428682841775855941 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 128 ∧ 17670246 / 100000 * Real.log 128 ≤ (857365683918546131 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_128_eq : (17670246 / 100000 * Real.log 128) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 + π) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_128_cos_r : (38339904470807 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) ≤ (958497978835331 / 1000000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(57822139 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) (-(57822139 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 - (-(57822139 / 200000000 : ℝ))| ≤ (9176628845021 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 - (-(57822139 / 200000000 : ℝ)))]

theorem thL_128_sin_r : (-285100124605461 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) ≤ (-142549878770153 / 500000000000000 : ℝ) := by
  have hr := thL_128_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (57822139 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1454344817163975299754714242058114416098075515684427904100679850608097371223215394971145793974011291963233109298463019 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(57822139 / 200000000 : ℝ)) ∧ Real.sin (-(57822139 / 200000000 : ℝ)) ≤ -((233068079673713977402174056659477651319003019420431073968337410498158429633149964057860979643074461 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546) (-(57822139 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 - (-(57822139 / 200000000 : ℝ))| ≤ (9176628845021 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 128) 546 - (-(57822139 / 200000000 : ℝ)))]

theorem thL_128_cos : (-958497978835331 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 128) ∧ Real.cos (17670246 / 100000 * Real.log 128) ≤ (-38339904470807 / 40000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_128_sin : (142549878770153 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 128) ∧ Real.sin (17670246 / 100000 * Real.log 128) ≤ (285100124605461 / 1000000000000000 : ℝ) := by
  have hc := thL_128_cos_r
  have hs := thL_128_sin_r
  rw [thL_128_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_128 : (-958497978835331 / 1000000000000000 : ℝ) ≤ cCG cZ 128 ∧ cCG cZ 128 ≤ (-38339904470807 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_cos

theorem sCB_128 : (142549878770153 / 500000000000000 : ℝ) ≤ sCG cZ 128 ∧ sCG cZ 128 ≤ (285100124605461 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_128_sin

theorem thL_129_r_bounds : (-48478384591427728119 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 ≤ (-48478347808572271881 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_129
  have hl : (429370403455944239 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 129 ∧ 17670246 / 100000 * Real.log 129 ≤ (107342600909840341 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_129_eq : (17670246 / 100000 * Real.log 129) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 + π + π / 2) + ((136 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_129_cos_r : (884775603074843 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) ≤ (707820776723 / 800000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(242391831 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) (-(242391831 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 - (-(242391831 / 500000000 : ℝ))| ≤ (18391427728119 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 - (-(242391831 / 500000000 : ℝ)))]

theorem thL_129_sin_r : (-466017143645531 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) ≤ (-233008387908481 / 500000000000000 : ℝ) := by
  have hr := thL_129_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (242391831 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((132523572923575150274497352452949313595007560889428462103524160325068635008349323894288685493586048814774931937062483367 / 284375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(242391831 / 500000000 : ℝ)) ∧ Real.sin (-(242391831 / 500000000 : ℝ)) ≤ -((10194120994120878465515190834995090716300962835773721478261433132833640021216511520148654786793280859 / 21875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547) (-(242391831 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 - (-(242391831 / 500000000 : ℝ))| ≤ (18391427728119 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 129) 547 - (-(242391831 / 500000000 : ℝ)))]

theorem thL_129_cos : (-466017143645531 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 129) ∧ Real.cos (17670246 / 100000 * Real.log 129) ≤ (-233008387908481 / 500000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_129_sin : (-707820776723 / 800000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 129) ∧ Real.sin (17670246 / 100000 * Real.log 129) ≤ (-884775603074843 / 1000000000000000 : ℝ) := by
  have hc := thL_129_cos_r
  have hs := thL_129_sin_r
  rw [thL_129_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_129 : (-466017143645531 / 1000000000000000 : ℝ) ≤ cCG cZ 129 ∧ cCG cZ 129 ≤ (-233008387908481 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_cos

theorem sCB_129 : (-707820776723 / 800000000000 : ℝ) ≤ sCG cZ 129 ∧ sCG cZ 129 ≤ (-884775603074843 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_129_sin

theorem thL_131_r_bounds : (33148641706074582961 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 ≤ (33148660093925417039 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_131
  have hl : (861459359917724839 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 131 ∧ 17670246 / 100000 * Real.log 131 ≤ (53841210017784943 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_131_eq : (17670246 / 100000 * Real.log 131) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_131_cos_r : (39408287577437 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) ≤ (788166119320811 / 1000000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (331486509 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) (331486509 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 - (331486509 / 500000000 : ℝ)| ≤ (9193925417039 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 - (331486509 / 500000000 : ℝ))]

theorem thL_131_sin_r : (615462616140693 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) ≤ (307731491949239 / 500000000000000 : ℝ) := by
  have hr := thL_131_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (331486509 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548) (331486509 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 - (331486509 / 500000000 : ℝ)| ≤ (9193925417039 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 131) 548 - (331486509 / 500000000 : ℝ))]

theorem thL_131_cos : (39408287577437 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 131) ∧ Real.cos (17670246 / 100000 * Real.log 131) ≤ (788166119320811 / 1000000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_131_sin : (615462616140693 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 131) ∧ Real.sin (17670246 / 100000 * Real.log 131) ≤ (307731491949239 / 500000000000000 : ℝ) := by
  have hc := thL_131_cos_r
  have hs := thL_131_sin_r
  rw [thL_131_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_131 : (39408287577437 / 50000000000000 : ℝ) ≤ cCG cZ 131 ∧ cCG cZ 131 ≤ (788166119320811 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_cos

theorem sCB_131 : (615462616140693 / 1000000000000000 : ℝ) ≤ sCG cZ 131 ∧ sCG cZ 131 ≤ (307731491949239 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_131_sin

theorem thL_132_r_bounds : (43592792515641595727 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 ≤ (43592829284358404273 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_132
  have hl : (862803111336407579 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 132 ∧ 17670246 / 100000 * Real.log 132 ≤ (215700777925810457 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_132_eq : (17670246 / 100000 * Real.log 132) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 + π / 2) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_132_cos_r : (226619588285727 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) ≤ (36259148833207 / 40000000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (435928109 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) (435928109 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 - (435928109 / 1000000000 : ℝ)| ≤ (18384358404273 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 - (435928109 / 1000000000 : ℝ))]

theorem thL_132_sin_r : (422251710151751 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) ≤ (422252077838923 / 1000000000000000 : ℝ) := by
  have hr := thL_132_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (435928109 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549) (435928109 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 - (435928109 / 1000000000 : ℝ)| ≤ (18384358404273 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 132) 549 - (435928109 / 1000000000 : ℝ))]

theorem thL_132_cos : (-422252077838923 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 132) ∧ Real.cos (17670246 / 100000 * Real.log 132) ≤ (-422251710151751 / 1000000000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_132_sin : (226619588285727 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 132) ∧ Real.sin (17670246 / 100000 * Real.log 132) ≤ (36259148833207 / 40000000000000 : ℝ) := by
  have hc := thL_132_cos_r
  have hs := thL_132_sin_r
  rw [thL_132_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_132 : (-422252077838923 / 1000000000000000 : ℝ) ≤ cCG cZ 132 ∧ cCG cZ 132 ≤ (-422251710151751 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_cos

theorem sCB_132 : (226619588285727 / 250000000000000 : ℝ) ≤ sCG cZ 132 ∧ sCG cZ 132 ≤ (36259148833207 / 40000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_132_sin

theorem thL_133_r_bounds : (794965604449845683 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 ≤ (794967075550154317 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_133
  have hl : (432068360569152801 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 133 ∧ 17670246 / 100000 * Real.log 133 ≤ (864136721505139851 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_133_eq : (17670246 / 100000 * Real.log 133) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 + π) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_133_cos_r : (490157813166471 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) ≤ (49015799705401 / 50000000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (39748317 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) (39748317 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 - (39748317 / 200000000 : ℝ)| ≤ (735550154317 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 - (39748317 / 200000000 : ℝ))]

theorem thL_133_sin_r : (98717829721653 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) ≤ (12339751701149 / 62500000000000 : ℝ) := by
  have hr := thL_133_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (39748317 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550) (39748317 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 - (39748317 / 200000000 : ℝ)| ≤ (735550154317 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 133) 550 - (39748317 / 200000000 : ℝ))]

theorem thL_133_cos : (-49015799705401 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 133) ∧ Real.cos (17670246 / 100000 * Real.log 133) ≤ (-490157813166471 / 500000000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_133_sin : (-12339751701149 / 62500000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 133) ∧ Real.sin (17670246 / 100000 * Real.log 133) ≤ (-98717829721653 / 500000000000000 : ℝ) := by
  have hc := thL_133_cos_r
  have hs := thL_133_sin_r
  rw [thL_133_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_133 : (-49015799705401 / 50000000000000 : ℝ) ≤ cCG cZ 133 ∧ cCG cZ 133 ≤ (-490157813166471 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_cos

theorem sCB_133 : (-12339751701149 / 62500000000000 : ℝ) ≤ sCG cZ 133 ∧ sCG cZ 133 ≤ (-98717829721653 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_133_sin

theorem thL_134_r_bounds : (-4843480474641580427 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 ≤ (-4843443725358419573 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_134
  have hl : (216365085314975051 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 134 ∧ 17670246 / 100000 * Real.log 134 ≤ (865460341626734453 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_134_eq : (17670246 / 100000 * Real.log 134) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 + π + π / 2) + ((137 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_134_cos_r : (998827089284343 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) ≤ (124853432097147 / 125000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(48434621 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) (-(48434621 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 - (-(48434621 / 1000000000 : ℝ))| ≤ (18374641580427 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 - (-(48434621 / 1000000000 : ℝ)))]

theorem thL_134_sin_r : (-24207934868491 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) ≤ (-48415502244149 / 1000000000000000 : ℝ) := by
  have hr := thL_134_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (48434621 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((43069354815645557724380324844290315553638303582272282198978989633709830697302240978383991249663385420597300447518342158217323 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(48434621 / 1000000000 : ℝ)) ∧ Real.sin (-(48434621 / 1000000000 : ℝ)) ≤ -((1932599254548198103017065806648616819671895491216489106544325939697141919922901728991515702276882695957179 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551) (-(48434621 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 - (-(48434621 / 1000000000 : ℝ))| ≤ (18374641580427 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 134) 551 - (-(48434621 / 1000000000 : ℝ)))]

theorem thL_134_cos : (-24207934868491 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 134) ∧ Real.cos (17670246 / 100000 * Real.log 134) ≤ (-48415502244149 / 1000000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_134_sin : (-124853432097147 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 134) ∧ Real.sin (17670246 / 100000 * Real.log 134) ≤ (-998827089284343 / 1000000000000000 : ℝ) := by
  have hc := thL_134_cos_r
  have hs := thL_134_sin_r
  rw [thL_134_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_134 : (-24207934868491 / 500000000000000 : ℝ) ≤ cCG cZ 134 ∧ cCG cZ 134 ≤ (-48415502244149 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_cos

theorem sCB_134 : (-124853432097147 / 125000000000000 : ℝ) ≤ sCG cZ 134 ∧ sCG cZ 134 ≤ (-998827089284343 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_134_sin

theorem thL_136_r_bounds : (-57216535450200556581 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 ≤ (-57216498749799443419 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_136
  have hl : (868078203363245587 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 136 ∧ 17670246 / 100000 * Real.log 136 ≤ (217019550932519959 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_136_eq : (17670246 / 100000 * Real.log 136) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 + π / 2) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_136_cos_r : (840730423507433 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) ≤ (168146158102803 / 200000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(572165171 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) (-(572165171 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 - (-(572165171 / 1000000000 : ℝ))| ≤ (18350200556581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 - (-(572165171 / 1000000000 : ℝ)))]

theorem thL_136_sin_r : (-54145382550031 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) ≤ (-108290691699237 / 200000000000000 : ℝ) := by
  have hr := thL_136_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (572165171 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((481663298708456014381180298345260528535551268631369843953922967686417824242553150586663796125022091640456216988513079927052773 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(572165171 / 1000000000 : ℝ)) ∧ Real.sin (-(572165171 / 1000000000 : ℝ)) ≤ -((21613096736913383121979348377638414266342189540336128171504815173639946125497484783869211422529299685248629 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553) (-(572165171 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 - (-(572165171 / 1000000000 : ℝ))| ≤ (18350200556581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 136) 553 - (-(572165171 / 1000000000 : ℝ)))]

theorem thL_136_cos : (108290691699237 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 136) ∧ Real.cos (17670246 / 100000 * Real.log 136) ≤ (54145382550031 / 100000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_136_sin : (840730423507433 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 136) ∧ Real.sin (17670246 / 100000 * Real.log 136) ≤ (168146158102803 / 200000000000000 : ℝ) := by
  have hc := thL_136_cos_r
  have hs := thL_136_sin_r
  rw [thL_136_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_136 : (108290691699237 / 200000000000000 : ℝ) ≤ cCG cZ 136 ∧ cCG cZ 136 ≤ (54145382550031 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_cos

theorem sCB_136 : (840730423507433 / 1000000000000000 : ℝ) ≤ sCG cZ 136 ∧ sCG cZ 136 ≤ (168146158102803 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_136_sin

theorem thL_137_r_bounds : (72236395117008543419 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 ≤ (72236431882991456581 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_137
  have hl : (108671591583696687 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 137 ∧ 17670246 / 100000 * Real.log 137 ≤ (173874546607281549 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_137_eq : (17670246 / 100000 * Real.log 137) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 + π / 2) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_137_cos_r : (187561142842249 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) ≤ (750244939070971 / 1000000000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (144472827 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) (144472827 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 - (144472827 / 200000000 : ℝ)| ≤ (18382991456581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 - (144472827 / 200000000 : ℝ))]

theorem thL_137_sin_r : (33058000701357 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) ≤ (20661261927791 / 31250000000000 : ℝ) := by
  have hr := thL_137_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (144472827 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553) (144472827 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 - (144472827 / 200000000 : ℝ)| ≤ (18382991456581 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 137) 553 - (144472827 / 200000000 : ℝ))]

theorem thL_137_cos : (-20661261927791 / 31250000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 137) ∧ Real.cos (17670246 / 100000 * Real.log 137) ≤ (-33058000701357 / 50000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_137_sin : (187561142842249 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 137) ∧ Real.sin (17670246 / 100000 * Real.log 137) ≤ (750244939070971 / 1000000000000000 : ℝ) := by
  have hc := thL_137_cos_r
  have hs := thL_137_sin_r
  rw [thL_137_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_137 : (-20661261927791 / 31250000000000 : ℝ) ≤ cCG cZ 137 ∧ cCG cZ 137 ≤ (-33058000701357 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_cos

theorem sCB_137 : (187561142842249 / 250000000000000 : ℝ) ≤ sCG cZ 137 ∧ sCG cZ 137 ≤ (750244939070971 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_137_sin

theorem thL_138_r_bounds : (21834104476431802671 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 ≤ (21834122823568197329 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_138
  have hl : (435328923567004921 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 138 ∧ 17670246 / 100000 * Real.log 138 ≤ (870657847500844091 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_138_eq : (17670246 / 100000 * Real.log 138) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 + π) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_138_cos_r : (453079824291031 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) ≤ (906160015524891 / 1000000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (436682273 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) (436682273 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 - (436682273 / 1000000000 : ℝ)| ≤ (9173568197329 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 - (436682273 / 1000000000 : ℝ))]

theorem thL_138_sin_r : (422935223857841 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) ≤ (211467795400287 / 500000000000000 : ℝ) := by
  have hr := thL_138_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (436682273 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554) (436682273 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 - (436682273 / 1000000000 : ℝ)| ≤ (9173568197329 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 138) 554 - (436682273 / 1000000000 : ℝ))]

theorem thL_138_cos : (-906160015524891 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 138) ∧ Real.cos (17670246 / 100000 * Real.log 138) ≤ (-453079824291031 / 500000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_138_sin : (-211467795400287 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 138) ∧ Real.sin (17670246 / 100000 * Real.log 138) ≤ (-422935223857841 / 1000000000000000 : ℝ) := by
  have hc := thL_138_cos_r
  have hs := thL_138_sin_r
  rw [thL_138_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_138 : (-906160015524891 / 1000000000000000 : ℝ) ≤ cCG cZ 138 ∧ cCG cZ 138 ≤ (-453079824291031 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_cos

theorem sCB_138 : (-211467795400287 / 500000000000000 : ℝ) ≤ sCG cZ 138 ∧ sCG cZ 138 ≤ (-422935223857841 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_138_sin

theorem thL_139_r_bounds : (5668853662695892983 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 ≤ (5668868337304107017 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_139
  have hl : (871933682712735021 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 139 ∧ 17670246 / 100000 * Real.log 139 ≤ (87193368307956927 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_139_eq : (17670246 / 100000 * Real.log 139) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 + π + π / 2) + ((138 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_139_cos_r : (989974118612627 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) ≤ (989974485477833 / 1000000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (5668861 / 40000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) (5668861 / 40000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 - (5668861 / 40000000 : ℝ)| ≤ (7337304107017 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 - (5668861 / 40000000 : ℝ))]

theorem thL_139_sin_r : (141247405184193 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) ≤ (141247772049399 / 1000000000000000 : ℝ) := by
  have hr := thL_139_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (5668861 / 40000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555) (5668861 / 40000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 - (5668861 / 40000000 : ℝ)| ≤ (7337304107017 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 139) 555 - (5668861 / 40000000 : ℝ))]

theorem thL_139_cos : (141247405184193 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 139) ∧ Real.cos (17670246 / 100000 * Real.log 139) ≤ (141247772049399 / 1000000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_139_sin : (-989974485477833 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 139) ∧ Real.sin (17670246 / 100000 * Real.log 139) ≤ (-989974118612627 / 1000000000000000 : ℝ) := by
  have hc := thL_139_cos_r
  have hs := thL_139_sin_r
  rw [thL_139_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_139 : (141247405184193 / 1000000000000000 : ℝ) ≤ cCG cZ 139 ∧ cCG cZ 139 ≤ (141247772049399 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_cos

theorem sCB_139 : (-989974485477833 / 1000000000000000 : ℝ) ≤ sCG cZ 139 ∧ sCG cZ 139 ≤ (-989974118612627 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_139_sin

theorem thL_141_r_bounds : (-47550752389578308889 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 ≤ (-47550715610421691111 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_141
  have hl : (874458046501818951 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 141 ∧ 17670246 / 100000 * Real.log 141 ≤ (2186145117171633 / 2500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_141_eq : (17670246 / 100000 * Real.log 141) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_141_cos_r : (44453019860001 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) ≤ (444530382495933 / 500000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(23775367 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) (-(23775367 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 - (-(23775367 / 50000000 : ℝ))| ≤ (18389578308889 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 - (-(23775367 / 50000000 : ℝ)))]

theorem thL_141_sin_r : (-114447436491679 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) ≤ (-457789378175139 / 1000000000000000 : ℝ) := by
  have hr := thL_141_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (23775367 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((451924133306898646678786543697977887697065008351543940278170135833279655819208046420951462010498363395379331 / 987187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(23775367 / 50000000 : ℝ)) ∧ Real.sin (-(23775367 / 50000000 : ℝ)) ≤ -((1158779828992021983528639070324710782806698096104945044327583774631796758117773305028919821 / 2531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557) (-(23775367 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 - (-(23775367 / 50000000 : ℝ))| ≤ (18389578308889 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 141) 557 - (-(23775367 / 50000000 : ℝ)))]

theorem thL_141_cos : (457789378175139 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 141) ∧ Real.cos (17670246 / 100000 * Real.log 141) ≤ (114447436491679 / 250000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_141_sin : (44453019860001 / 50000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 141) ∧ Real.sin (17670246 / 100000 * Real.log 141) ≤ (444530382495933 / 500000000000000 : ℝ) := by
  have hc := thL_141_cos_r
  have hs := thL_141_sin_r
  rw [thL_141_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_141 : (457789378175139 / 1000000000000000 : ℝ) ≤ cCG cZ 141 ∧ cCG cZ 141 ≤ (114447436491679 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_cos

theorem sCB_141 : (44453019860001 / 50000000000000 : ℝ) ≤ sCG cZ 141 ∧ sCG cZ 141 ≤ (444530382495933 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_141_sin

theorem thL_142_r_bounds : (77327831055241191111 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 ≤ (77327867744758808889 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_142
  have hl : (218926708083842689 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 142 ∧ 17670246 / 100000 * Real.log 142 ≤ (175141366540441001 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_142_eq : (17670246 / 100000 * Real.log 142) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_142_cos_r : (22363261147423 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) ≤ (143124944741629 / 200000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (386639247 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) (386639247 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 - (386639247 / 500000000 : ℝ)| ≤ (18344758808889 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 - (386639247 / 500000000 : ℝ))]

theorem thL_142_sin_r : (174621243892783 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) ≤ (139697068494397 / 200000000000000 : ℝ) := by
  have hr := thL_142_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (386639247 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557) (386639247 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 - (386639247 / 500000000 : ℝ)| ≤ (18344758808889 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 142) 557 - (386639247 / 500000000 : ℝ))]

theorem thL_142_cos : (-139697068494397 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 142) ∧ Real.cos (17670246 / 100000 * Real.log 142) ≤ (-174621243892783 / 250000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_142_sin : (22363261147423 / 31250000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 142) ∧ Real.sin (17670246 / 100000 * Real.log 142) ≤ (143124944741629 / 200000000000000 : ℝ) := by
  have hc := thL_142_cos_r
  have hs := thL_142_sin_r
  rw [thL_142_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_142 : (-139697068494397 / 200000000000000 : ℝ) ≤ cCG cZ 142 ∧ cCG cZ 142 ≤ (-174621243892783 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_cos

theorem sCB_142 : (22363261147423 / 31250000000000 : ℝ) ≤ sCG cZ 142 ∧ sCG cZ 142 ≤ (143124944741629 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_142_sin

theorem thL_143_r_bounds : (22125216766786126517 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 ≤ (22125235133213873483 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_143
  have hl : (438473427343691171 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 143 ∧ 17670246 / 100000 * Real.log 143 ≤ (876946855054216591 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_143_eq : (17670246 / 100000 * Real.log 143) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 + π) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_143_cos_r : (903681869609569 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) ≤ (451841118469121 / 500000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (442504519 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) (442504519 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 - (442504519 / 1000000000 : ℝ)| ≤ (9183213873483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 - (442504519 / 1000000000 : ℝ))]

theorem thL_143_sin_r : (10705097772177 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) ≤ (10705106955391 / 25000000000000 : ℝ) := by
  have hr := thL_143_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (442504519 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558) (442504519 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 - (442504519 / 1000000000 : ℝ)| ≤ (9183213873483 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 143) 558 - (442504519 / 1000000000 : ℝ))]

theorem thL_143_cos : (-451841118469121 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 143) ∧ Real.cos (17670246 / 100000 * Real.log 143) ≤ (-903681869609569 / 1000000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_143_sin : (-10705106955391 / 25000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 143) ∧ Real.sin (17670246 / 100000 * Real.log 143) ≤ (-10705097772177 / 25000000000000 : ℝ) := by
  have hc := thL_143_cos_r
  have hs := thL_143_sin_r
  rw [thL_143_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_143 : (-451841118469121 / 500000000000000 : ℝ) ≤ cCG cZ 143 ∧ cCG cZ 143 ≤ (-903681869609569 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_cos

theorem sCB_143 : (-10705106955391 / 25000000000000 : ℝ) ≤ sCG cZ 143 ∧ sCG cZ 143 ≤ (-10705097772177 / 25000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_143_sin

theorem thL_144_r_bounds : (20617804023068569527 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 ≤ (20617877576931430473 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_144
  have hl : (878178235698462553 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 144 ∧ 17670246 / 100000 * Real.log 144 ≤ (439089118032648401 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_144_eq : (17670246 / 100000 * Real.log 144) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 + π + π / 2) + ((139 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_144_cos_r : (198938165669007 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) ≤ (19893823922287 / 20000000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (25772301 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) (25772301 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 - (25772301 / 250000000 : ℝ)| ≤ (36776931430473 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 - (25772301 / 250000000 : ℝ))]

theorem thL_144_sin_r : (5145326117841 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) ≤ (20581378025227 / 200000000000000 : ℝ) := by
  have hr := thL_144_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (25772301 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559) (25772301 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 - (25772301 / 250000000 : ℝ)| ≤ (36776931430473 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 144) 559 - (25772301 / 250000000 : ℝ))]

theorem thL_144_cos : (5145326117841 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 144) ∧ Real.cos (17670246 / 100000 * Real.log 144) ≤ (20581378025227 / 200000000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_144_sin : (-19893823922287 / 20000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 144) ∧ Real.sin (17670246 / 100000 * Real.log 144) ≤ (-198938165669007 / 200000000000000 : ℝ) := by
  have hc := thL_144_cos_r
  have hs := thL_144_sin_r
  rw [thL_144_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_144 : (5145326117841 / 50000000000000 : ℝ) ≤ cCG cZ 144 ∧ cCG cZ 144 ≤ (20581378025227 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_cos

theorem sCB_144 : (-19893823922287 / 20000000000000 : ℝ) ≤ sCG cZ 144 ∧ sCG cZ 144 ≤ (-198938165669007 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_144_sin

theorem thL_146_r_bounds : (-60118968171598261197 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 ≤ (-60118931428401738803 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_146
  have hl : (880615549650818737 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 146 ∧ 17670246 / 100000 * Real.log 146 ≤ (440307775008826493 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_146_eq : (17670246 / 100000 * Real.log 146) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_146_cos_r : (824663206368739 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) ≤ (824663573805359 / 1000000000000000 : ℝ) := by
  have hr := thL_146_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(300594749 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) (-(300594749 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 - (-(300594749 / 500000000 : ℝ))| ≤ (18371598261197 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 - (-(300594749 / 500000000 : ℝ)))]

theorem thL_146_sin_r : (-565623992484951 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) ≤ (-56562362505277 / 100000000000000 : ℝ) := by
  have hr := thL_146_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (300594749 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4724726377623285608920294000368307598905935024378446552718217047344068371167088964525285248973583195405331942745801185239 / 8353125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(300594749 / 500000000 : ℝ)) ∧ Real.sin (-(300594749 / 500000000 : ℝ)) ≤ -((1574908792540495970390578302711495314256995625168408043137361924311323935231933561324912642822487502893 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561) (-(300594749 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 - (-(300594749 / 500000000 : ℝ))| ≤ (18371598261197 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 146) 561 - (-(300594749 / 500000000 : ℝ)))]

theorem thL_146_cos : (56562362505277 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 146) ∧ Real.cos (17670246 / 100000 * Real.log 146) ≤ (565623992484951 / 1000000000000000 : ℝ) := by
  have hc := thL_146_cos_r
  have hs := thL_146_sin_r
  rw [thL_146_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_146_sin : (824663206368739 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 146) ∧ Real.sin (17670246 / 100000 * Real.log 146) ≤ (824663573805359 / 1000000000000000 : ℝ) := by
  have hc := thL_146_cos_r
  have hs := thL_146_sin_r
  rw [thL_146_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_146 : (56562362505277 / 100000000000000 : ℝ) ≤ cCG cZ 146 ∧ cCG cZ 146 ≤ (565623992484951 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_146_cos

theorem sCB_146 : (824663206368739 / 1000000000000000 : ℝ) ≤ sCG cZ 146 ∧ sCG cZ 146 ≤ (824663573805359 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_146_sin

theorem thL_147_r_bounds : (60497513847028838803 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 ≤ (60497550552971161197 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_147
  have hl : (440910857235316233 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 147 ∧ 17670246 / 100000 * Real.log 147 ≤ (176364342967493343 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_147_eq : (17670246 / 100000 * Real.log 147) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_147_cos_r : (822515949757723 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) ≤ (164503263364433 / 200000000000000 : ℝ) := by
  have hr := thL_147_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (302487661 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) (302487661 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 - (302487661 / 500000000 : ℝ)| ≤ (18352971161197 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 - (302487661 / 500000000 : ℝ))]

theorem thL_147_sin_r : (284370797424501 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) ≤ (28437098095433 / 50000000000000 : ℝ) := by
  have hr := thL_147_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (302487661 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561) (302487661 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 - (302487661 / 500000000 : ℝ)| ≤ (18352971161197 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 147) 561 - (302487661 / 500000000 : ℝ))]

theorem thL_147_cos : (-28437098095433 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 147) ∧ Real.cos (17670246 / 100000 * Real.log 147) ≤ (-284370797424501 / 500000000000000 : ℝ) := by
  have hc := thL_147_cos_r
  have hs := thL_147_sin_r
  rw [thL_147_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_147_sin : (822515949757723 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 147) ∧ Real.sin (17670246 / 100000 * Real.log 147) ≤ (164503263364433 / 200000000000000 : ℝ) := by
  have hc := thL_147_cos_r
  have hs := thL_147_sin_r
  rw [thL_147_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_147 : (-28437098095433 / 50000000000000 : ℝ) ≤ cCG cZ 147 ∧ cCG cZ 147 ≤ (-284370797424501 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_147_cos

theorem sCB_147 : (822515949757723 / 1000000000000000 : ℝ) ≤ sCG cZ 147 ∧ sCG cZ 147 ≤ (164503263364433 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_147_sin

theorem thL_148_r_bounds : (23216618024697698993 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 ≤ (23216654775302301007 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_148
  have hl : (883019701838978877 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 148 ∧ 17670246 / 100000 * Real.log 148 ≤ (883019702205813127 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_148_eq : (17670246 / 100000 * Real.log 148) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 + π) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_148_cos_r : (973170044566823 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) ≤ (97317041207287 / 100000000000000 : ℝ) := by
  have hr := thL_148_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (58041591 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) (58041591 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 - (58041591 / 250000000 : ℝ)| ≤ (18375302301007 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 - (58041591 / 250000000 : ℝ))]

theorem thL_148_sin_r : (230086118994223 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) ≤ (23008648650027 / 100000000000000 : ℝ) := by
  have hr := thL_148_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (58041591 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562) (58041591 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 - (58041591 / 250000000 : ℝ)| ≤ (18375302301007 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 148) 562 - (58041591 / 250000000 : ℝ))]

theorem thL_148_cos : (-97317041207287 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 148) ∧ Real.cos (17670246 / 100000 * Real.log 148) ≤ (-973170044566823 / 1000000000000000 : ℝ) := by
  have hc := thL_148_cos_r
  have hs := thL_148_sin_r
  rw [thL_148_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_148_sin : (-23008648650027 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 148) ∧ Real.sin (17670246 / 100000 * Real.log 148) ≤ (-230086118994223 / 1000000000000000 : ℝ) := by
  have hc := thL_148_cos_r
  have hs := thL_148_sin_r
  rw [thL_148_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_148 : (-97317041207287 / 100000000000000 : ℝ) ≤ cCG cZ 148 ∧ cCG cZ 148 ≤ (-973170044566823 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_148_cos

theorem sCB_148 : (-23008648650027 / 100000000000000 : ℝ) ≤ sCG cZ 148 ∧ sCG cZ 148 ≤ (-230086118994223 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_148_sin

theorem thL_149_r_bounds : (-14871009444899437351 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 ≤ (-14870972755100562649 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_149
  have hl : (442104810945570771 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 149 ∧ 17670246 / 100000 * Real.log 149 ≤ (884209622257975791 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_149_eq : (17670246 / 100000 * Real.log 149) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 + π + π / 2) + ((140 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_149_cos_r : (988962860104069 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) ≤ (988963227002059 / 1000000000000000 : ℝ) := by
  have hr := thL_149_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(148709911 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) (-(148709911 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 - (-(148709911 / 1000000000 : ℝ))| ≤ (18344899437351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 - (-(148709911 / 1000000000 : ℝ)))]

theorem thL_149_sin_r : (-148162589228129 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) ≤ (-7408111116507 / 50000000000000 : ℝ) := by
  have hr := thL_149_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (148709911 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((131801483223530128217243357363961915076422960378744850733713227681423787186131072549825259748406075801452596781612363316545233 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(148709911 / 1000000000 : ℝ)) ∧ Real.sin (-(148709911 / 1000000000 : ℝ)) ≤ -((844881302714936719325374289412518678249984408576062320360703235713606690850282108842376440001042876932927 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563) (-(148709911 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 - (-(148709911 / 1000000000 : ℝ))| ≤ (18344899437351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 149) 563 - (-(148709911 / 1000000000 : ℝ)))]

theorem thL_149_cos : (-148162589228129 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 149) ∧ Real.cos (17670246 / 100000 * Real.log 149) ≤ (-7408111116507 / 50000000000000 : ℝ) := by
  have hc := thL_149_cos_r
  have hs := thL_149_sin_r
  rw [thL_149_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_149_sin : (-988963227002059 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 149) ∧ Real.sin (17670246 / 100000 * Real.log 149) ≤ (-988962860104069 / 1000000000000000 : ℝ) := by
  have hc := thL_149_cos_r
  have hs := thL_149_sin_r
  rw [thL_149_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_149 : (-148162589228129 / 1000000000000000 : ℝ) ≤ cCG cZ 149 ∧ cCG cZ 149 ≤ (-7408111116507 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_149_cos

theorem sCB_149 : (-988963227002059 / 1000000000000000 : ℝ) ≤ sCG cZ 149 ∧ sCG cZ 149 ≤ (-988962860104069 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_149_sin

theorem thL_151_r_bounds : (15914032080636606143 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 ≤ (15914041269363393857 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_151
  have hl : (44328284479813099 / 50000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 151 ∧ 17670246 / 100000 * Real.log 151 ≤ (886565689963096229 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_151_eq : (17670246 / 100000 * Real.log 151) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_151_cos_r : (25129509515561 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) ≤ (402072336028133 / 500000000000000 : ℝ) := by
  have hr := thL_151_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (636561467 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) (636561467 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 - (636561467 / 1000000000 : ℝ)| ≤ (4594363393857 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 - (636561467 / 1000000000 : ℝ))]

theorem thL_151_sin_r : (594433699820277 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) ≤ (297217033684901 / 500000000000000 : ℝ) := by
  have hr := thL_151_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (636561467 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564) (636561467 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 - (636561467 / 1000000000 : ℝ)| ≤ (4594363393857 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 151) 564 - (636561467 / 1000000000 : ℝ))]

theorem thL_151_cos : (25129509515561 / 31250000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 151) ∧ Real.cos (17670246 / 100000 * Real.log 151) ≤ (402072336028133 / 500000000000000 : ℝ) := by
  have hc := thL_151_cos_r
  have hs := thL_151_sin_r
  rw [thL_151_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_151_sin : (594433699820277 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 151) ∧ Real.sin (17670246 / 100000 * Real.log 151) ≤ (297217033684901 / 500000000000000 : ℝ) := by
  have hc := thL_151_cos_r
  have hs := thL_151_sin_r
  rw [thL_151_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_151 : (25129509515561 / 31250000000000 : ℝ) ≤ cCG cZ 151 ∧ cCG cZ 151 ≤ (402072336028133 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_151_cos

theorem sCB_151 : (594433699820277 / 1000000000000000 : ℝ) ≤ sCG cZ 151 ∧ sCG cZ 151 ≤ (297217033684901 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_151_sin

theorem thL_152_r_bounds : (9284882526720645289 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 ≤ (9284897233279354711 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_152
  have hl : (443866023351142303 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 152 ∧ 17670246 / 100000 * Real.log 152 ≤ (177546409413823771 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_152_eq : (17670246 / 100000 * Real.log 152) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 + π / 2) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_152_cos_r : (121647524282279 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) ≤ (973180561922201 / 1000000000000000 : ℝ) := by
  have hr := thL_152_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (232122247 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) (232122247 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 - (232122247 / 1000000000 : ℝ)| ≤ (7353279354711 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 - (232122247 / 1000000000 : ℝ))]

theorem thL_152_sin_r : (57510796335101 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) ≤ (230043553004373 / 1000000000000000 : ℝ) := by
  have hr := thL_152_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (232122247 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565) (232122247 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 - (232122247 / 1000000000 : ℝ)| ≤ (7353279354711 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 152) 565 - (232122247 / 1000000000 : ℝ))]

theorem thL_152_cos : (-230043553004373 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 152) ∧ Real.cos (17670246 / 100000 * Real.log 152) ≤ (-57510796335101 / 250000000000000 : ℝ) := by
  have hc := thL_152_cos_r
  have hs := thL_152_sin_r
  rw [thL_152_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_152_sin : (121647524282279 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 152) ∧ Real.sin (17670246 / 100000 * Real.log 152) ≤ (973180561922201 / 1000000000000000 : ℝ) := by
  have hc := thL_152_cos_r
  have hs := thL_152_sin_r
  rw [thL_152_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_152 : (-230043553004373 / 1000000000000000 : ℝ) ≤ cCG cZ 152 ∧ cCG cZ 152 ≤ (-57510796335101 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_152_cos

theorem sCB_152 : (121647524282279 / 125000000000000 : ℝ) ≤ sCG cZ 152 ∧ sCG cZ 152 ≤ (973180561922201 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_152_sin

theorem thL_153_r_bounds : (-17996545591522848701 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 ≤ (-17996508808477151299 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_153
  have hl : (444445377754998129 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 153 ∧ 17670246 / 100000 * Real.log 153 ≤ (888890755876830507 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_153_eq : (17670246 / 100000 * Real.log 153) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 + π) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_153_cos_r : (983849725618643 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) ≤ (983850093449101 / 1000000000000000 : ℝ) := by
  have hr := thL_153_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(22495659 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) (-(22495659 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 - (-(22495659 / 125000000 : ℝ))| ≤ (18391522848701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 - (-(22495659 / 125000000 : ℝ)))]

theorem thL_153_sin_r : (-178995590309339 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) ≤ (-178995222478881 / 1000000000000000 : ℝ) := by
  have hr := thL_153_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (22495659 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1191922608500241005237459529569672338542380780977224994838842938485262788762322611863703278898153026681431508479 / 6658956408500671386718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(22495659 / 125000000 : ℝ)) ∧ Real.sin (-(22495659 / 125000000 : ℝ)) ≤ -((10268871704002076350901424683249936040664313683434257409942539409514735738964070991456037916861 / 57369470596313476562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566) (-(22495659 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 - (-(22495659 / 125000000 : ℝ))| ≤ (18391522848701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 153) 566 - (-(22495659 / 125000000 : ℝ)))]

theorem thL_153_cos : (-983850093449101 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 153) ∧ Real.cos (17670246 / 100000 * Real.log 153) ≤ (-983849725618643 / 1000000000000000 : ℝ) := by
  have hc := thL_153_cos_r
  have hs := thL_153_sin_r
  rw [thL_153_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_153_sin : (178995222478881 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 153) ∧ Real.sin (17670246 / 100000 * Real.log 153) ≤ (178995590309339 / 1000000000000000 : ℝ) := by
  have hc := thL_153_cos_r
  have hs := thL_153_sin_r
  rw [thL_153_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_153 : (-983850093449101 / 1000000000000000 : ℝ) ≤ cCG cZ 153 ∧ cCG cZ 153 ≤ (-983849725618643 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_153_cos

theorem sCB_153 : (178995222478881 / 1000000000000000 : ℝ) ≤ sCG cZ 153 ∧ sCG cZ 153 ≤ (178995590309339 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_153_sin

theorem thL_154_r_bounds : (-59960162068436189659 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 ≤ (-59960125331563810341 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_154
  have hl : (55627619729534781 / 62500000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 154 ∧ 17670246 / 100000 * Real.log 154 ≤ (178008383207878149 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_154_eq : (17670246 / 100000 * Real.log 154) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 + π + π / 2) + ((141 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_154_cos_r : (206390102814921 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) ≤ (412780389316459 / 500000000000000 : ℝ) := by
  have hr := thL_154_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(599601437 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) (-(599601437 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 - (-(599601437 / 1000000000 : ℝ))| ≤ (18368436189659 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 - (-(599601437 / 1000000000 : ℝ)))]

theorem thL_154_sin_r : (-282156832000999 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) ≤ (-112862659326613 / 200000000000000 : ℝ) := by
  have hr := thL_154_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (599601437 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3513991779658308344129015409810842950972403306792718465644161159360742744205612034510365034582482202067490020143059950937659597 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(599601437 / 1000000000 : ℝ)) ∧ Real.sin (-(599601437 / 1000000000 : ℝ)) ≤ -((22525588331134701977487549717956732181748989892853615196811786898354356561139961766924588189116976060664987 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567) (-(599601437 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 - (-(599601437 / 1000000000 : ℝ))| ≤ (18368436189659 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 154) 567 - (-(599601437 / 1000000000 : ℝ)))]

theorem thL_154_cos : (-282156832000999 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 154) ∧ Real.cos (17670246 / 100000 * Real.log 154) ≤ (-112862659326613 / 200000000000000 : ℝ) := by
  have hc := thL_154_cos_r
  have hs := thL_154_sin_r
  rw [thL_154_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_154_sin : (-412780389316459 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 154) ∧ Real.sin (17670246 / 100000 * Real.log 154) ≤ (-206390102814921 / 250000000000000 : ℝ) := by
  have hc := thL_154_cos_r
  have hs := thL_154_sin_r
  rw [thL_154_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_154 : (-282156832000999 / 500000000000000 : ℝ) ≤ cCG cZ 154 ∧ cCG cZ 154 ≤ (-112862659326613 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_154_cos

theorem sCB_154 : (-412780389316459 / 500000000000000 : ℝ) ≤ sCG cZ 154 ∧ sCG cZ 154 ≤ (-206390102814921 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_154_sin

theorem thL_156_r_bounds : (1370817865371434033 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 ≤ (1370822459628565967 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_156
  have hl : (223080494762359329 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 156 ∧ 17670246 / 100000 * Real.log 156 ≤ (178464395883254313 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_156_eq : (17670246 / 100000 * Real.log 156) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) + ((142 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_156_cos_r : (39759702682119 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) ≤ (993992934593547 / 1000000000000000 : ℝ) := by
  have hr := thL_156_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (109665613 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) (109665613 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 - (109665613 / 1000000000 : ℝ)| ≤ (2297128565967 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 - (109665613 / 1000000000 : ℝ))]

theorem thL_156_sin_r : (13680718117243 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) ≤ (21889222495703 / 200000000000000 : ℝ) := by
  have hr := thL_156_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (109665613 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568) (109665613 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 - (109665613 / 1000000000 : ℝ)| ≤ (2297128565967 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 156) 568 - (109665613 / 1000000000 : ℝ))]

theorem thL_156_cos : (39759702682119 / 40000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 156) ∧ Real.cos (17670246 / 100000 * Real.log 156) ≤ (993992934593547 / 1000000000000000 : ℝ) := by
  have hc := thL_156_cos_r
  have hs := thL_156_sin_r
  rw [thL_156_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_156_sin : (13680718117243 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 156) ∧ Real.sin (17670246 / 100000 * Real.log 156) ≤ (21889222495703 / 200000000000000 : ℝ) := by
  have hc := thL_156_cos_r
  have hs := thL_156_sin_r
  rw [thL_156_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_156 : (39759702682119 / 40000000000000 : ℝ) ≤ cCG cZ 156 ∧ cCG cZ 156 ≤ (993992934593547 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_156_cos

theorem sCB_156 : (13680718117243 / 125000000000000 : ℝ) ≤ sCG cZ 156 ∧ sCG cZ 156 ≤ (21889222495703 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_156_sin

theorem thL_157_r_bounds : (-66407570780539868943 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 ≤ (-66407497219460131057 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_157
  have hl : (893451072092393477 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 157 ∧ 17670246 / 100000 * Real.log 157 ≤ (446725536229613863 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_157_eq : (17670246 / 100000 * Real.log 157) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 + π / 2) + ((142 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_157_cos_r : (945379903294879 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) ≤ (472690135550141 / 500000000000000 : ℝ) := by
  have hr := thL_157_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(33203767 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) (-(33203767 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 - (-(33203767 / 100000000 : ℝ))| ≤ (36780539868943 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 - (-(33203767 / 100000000 : ℝ)))]

theorem thL_157_sin_r : (-325970260336551 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) ≤ (-20373118283197 / 62500000000000 : ℝ) := by
  have hr := thL_157_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (33203767 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((202982244613118380212382799186582833161819099084006252325592788759519958093586794225217282392955237910305340729687 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(33203767 / 100000000 : ℝ)) ∧ Real.sin (-(33203767 / 100000000 : ℝ)) ≤ -((130116823469947641401529767359930368287854065308735335842574336395252259966596652716080477558617 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569) (-(33203767 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 - (-(33203767 / 100000000 : ℝ))| ≤ (36780539868943 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 157) 569 - (-(33203767 / 100000000 : ℝ)))]

theorem thL_157_cos : (20373118283197 / 62500000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 157) ∧ Real.cos (17670246 / 100000 * Real.log 157) ≤ (325970260336551 / 1000000000000000 : ℝ) := by
  have hc := thL_157_cos_r
  have hs := thL_157_sin_r
  rw [thL_157_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_157_sin : (945379903294879 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 157) ∧ Real.sin (17670246 / 100000 * Real.log 157) ≤ (472690135550141 / 500000000000000 : ℝ) := by
  have hc := thL_157_cos_r
  have hs := thL_157_sin_r
  rw [thL_157_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_157 : (20373118283197 / 62500000000000 : ℝ) ≤ cCG cZ 157 ∧ cCG cZ 157 ≤ (325970260336551 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_157_cos

theorem sCB_157 : (945379903294879 / 1000000000000000 : ℝ) ≤ sCG cZ 157 ∧ sCG cZ 157 ≤ (472690135550141 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_157_sin

theorem thL_158_r_bounds : (-15618200615570119279 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 ≤ (-15618193264429880721 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_158
  have hl : (894572996242312567 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 158 ∧ 17670246 / 100000 * Real.log 158 ≤ (13977703072017919 / 15625000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_158_eq : (17670246 / 100000 * Real.log 158) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 + π) + ((142 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_158_cos_r : (710273183290567 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) ≤ (710273550954947 / 1000000000000000 : ℝ) := by
  have hr := thL_158_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(780909847 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) (-(780909847 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 - (-(780909847 / 1000000000 : ℝ))| ≤ (3675570119279 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 - (-(780909847 / 1000000000 : ℝ)))]

theorem thL_158_sin_r : (-703926134344599 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) ≤ (-43995360423821 / 62500000000000 : ℝ) := by
  have hr := thL_158_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (780909847 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((626194505119261288558197896541095427671116377516814869961204984706022853315203579519173807623872722143434081833487908901162961 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(780909847 / 1000000000 : ℝ)) ∧ Real.sin (-(780909847 / 1000000000 : ℝ)) ≤ -((28098471383299149722863236661426663108817149358666345782563059598314530744331415445888405272601537804205497 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570) (-(780909847 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 - (-(780909847 / 1000000000 : ℝ))| ≤ (3675570119279 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 158) 570 - (-(780909847 / 1000000000 : ℝ)))]

theorem thL_158_cos : (-710273550954947 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 158) ∧ Real.cos (17670246 / 100000 * Real.log 158) ≤ (-710273183290567 / 1000000000000000 : ℝ) := by
  have hc := thL_158_cos_r
  have hs := thL_158_sin_r
  rw [thL_158_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_158_sin : (43995360423821 / 62500000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 158) ∧ Real.sin (17670246 / 100000 * Real.log 158) ≤ (703926134344599 / 1000000000000000 : ℝ) := by
  have hc := thL_158_cos_r
  have hs := thL_158_sin_r
  rw [thL_158_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_158 : (-710273550954947 / 1000000000000000 : ℝ) ≤ cCG cZ 158 ∧ cCG cZ 158 ≤ (-710273183290567 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_158_cos

theorem sCB_158 : (43995360423821 / 62500000000000 : ℝ) ≤ sCG cZ 158 ∧ sCG cZ 158 ≤ (703926134344599 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_158_sin

theorem thL_159_r_bounds : (6678713724551700721 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 ≤ (6678721075448299279 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_159
  have hl : (447843920979659329 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 159 ∧ 17670246 / 100000 * Real.log 159 ≤ (223921960581538227 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_159_eq : (17670246 / 100000 * Real.log 159) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 + π) + ((142 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_159_cos_r : (944759444218779 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) ≤ (472379905881807 / 500000000000000 : ℝ) := by
  have hr := thL_159_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (33393587 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) (33393587 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 - (33393587 / 100000000 : ℝ)| ≤ (3675448299279 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 - (33393587 / 100000000 : ℝ))]

theorem thL_159_sin_r : (163881912401887 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) ≤ (65552838469721 / 200000000000000 : ℝ) := by
  have hr := thL_159_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (33393587 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570) (33393587 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 - (33393587 / 100000000 : ℝ)| ≤ (3675448299279 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 159) 570 - (33393587 / 100000000 : ℝ))]

theorem thL_159_cos : (-472379905881807 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 159) ∧ Real.cos (17670246 / 100000 * Real.log 159) ≤ (-944759444218779 / 1000000000000000 : ℝ) := by
  have hc := thL_159_cos_r
  have hs := thL_159_sin_r
  rw [thL_159_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_159_sin : (-65552838469721 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 159) ∧ Real.sin (17670246 / 100000 * Real.log 159) ≤ (-163881912401887 / 500000000000000 : ℝ) := by
  have hc := thL_159_cos_r
  have hs := thL_159_sin_r
  rw [thL_159_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_159 : (-472379905881807 / 500000000000000 : ℝ) ≤ cCG cZ 159 ∧ cCG cZ 159 ≤ (-944759444218779 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_159_cos

theorem sCB_159 : (-65552838469721 / 200000000000000 : ℝ) ≤ sCG cZ 159 ∧ sCG cZ 159 ≤ (-163881912401887 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_159_sin

theorem thL_161_r_bounds : (-29942372826105360121 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 ≤ (-29942354473894639879 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_161
  have hl : (897896651470158759 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 161 ∧ 17670246 / 100000 * Real.log 161 ≤ (56118540739812063 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_161_eq : (17670246 / 100000 * Real.log 161) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) + ((143 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_161_cos_r : (165197152303789 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) ≤ (825986128567601 / 1000000000000000 : ℝ) := by
  have hr := thL_161_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(598847273 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) (-(598847273 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 - (-(598847273 / 1000000000 : ℝ))| ≤ (9176105360121 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 - (-(598847273 / 1000000000 : ℝ)))]

theorem thL_161_sin_r : (-70461361917229 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) ≤ (-140922632073353 / 250000000000000 : ℝ) := by
  have hr := thL_161_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (598847273 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((501444826749045923238446637526730685392015907110810020675918873364513749090688543578765557120008709529597231518500627451809519 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(598847273 / 1000000000 : ℝ)) ∧ Real.sin (-(598847273 / 1000000000 : ℝ)) ≤ -((22500729405397741281720756563459084759945147455026390225366752906767578716855800387905719108933288370130823 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572) (-(598847273 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 - (-(598847273 / 1000000000 : ℝ))| ≤ (9176105360121 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 161) 572 - (-(598847273 / 1000000000 : ℝ)))]

theorem thL_161_cos : (165197152303789 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 161) ∧ Real.cos (17670246 / 100000 * Real.log 161) ≤ (825986128567601 / 1000000000000000 : ℝ) := by
  have hc := thL_161_cos_r
  have hs := thL_161_sin_r
  rw [thL_161_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_161_sin : (-70461361917229 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 161) ∧ Real.sin (17670246 / 100000 * Real.log 161) ≤ (-140922632073353 / 250000000000000 : ℝ) := by
  have hc := thL_161_cos_r
  have hs := thL_161_sin_r
  rw [thL_161_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_161 : (165197152303789 / 200000000000000 : ℝ) ≤ cCG cZ 161 ∧ cCG cZ 161 ≤ (825986128567601 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_161_cos

theorem sCB_161 : (-70461361917229 / 125000000000000 : ℝ) ≤ sCG cZ 161 ∧ sCG cZ 161 ≤ (-140922632073353 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_161_sin

theorem thL_162_r_bounds : (24764445926617889879 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 ≤ (24764464273382110121 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_162
  have hl : (112373848480651653 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 162 ∧ 17670246 / 100000 * Real.log 162 ≤ (898990788212047473 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_162_eq : (17670246 / 100000 * Real.log 162) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) + ((143 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_162_cos_r : (879831156995697 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) ≤ (439915761965719 / 500000000000000 : ℝ) := by
  have hr := thL_162_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (247644551 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) (247644551 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 - (247644551 / 500000000 : ℝ)| ≤ (9173382110121 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 - (247644551 / 500000000 : ℝ))]

theorem thL_162_sin_r : (475285848662133 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) ≤ (118821553899359 / 250000000000000 : ℝ) := by
  have hr := thL_162_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (247644551 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572) (247644551 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 - (247644551 / 500000000 : ℝ)| ≤ (9173382110121 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 162) 572 - (247644551 / 500000000 : ℝ))]

theorem thL_162_cos : (879831156995697 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 162) ∧ Real.cos (17670246 / 100000 * Real.log 162) ≤ (439915761965719 / 500000000000000 : ℝ) := by
  have hc := thL_162_cos_r
  have hs := thL_162_sin_r
  rw [thL_162_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_162_sin : (475285848662133 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 162) ∧ Real.sin (17670246 / 100000 * Real.log 162) ≤ (118821553899359 / 250000000000000 : ℝ) := by
  have hc := thL_162_cos_r
  have hs := thL_162_sin_r
  rw [thL_162_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_162 : (879831156995697 / 1000000000000000 : ℝ) ≤ cCG cZ 162 ∧ cCG cZ 162 ≤ (439915761965719 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_162_cos

theorem sCB_162 : (475285848662133 / 1000000000000000 : ℝ) ≤ sCG cZ 162 ∧ sCG cZ 162 ≤ (118821553899359 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_162_sin

theorem thL_163_r_bounds : (2379155447882435669 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 ≤ (2379228952117564331 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_163
  have hl : (36003127641228607 / 40000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 163 ∧ 17670246 / 100000 * Real.log 163 ≤ (56254886962346839 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_163_eq : (17670246 / 100000 * Real.log 163) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 + π / 2) + ((143 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_163_cos_r : (39997162405191 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) ≤ (124991178456369 / 125000000000000 : ℝ) := by
  have hr := thL_163_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (11895961 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) (11895961 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 - (11895961 / 1000000000 : ℝ)| ≤ (36752117564331 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 - (11895961 / 1000000000 : ℝ))]

theorem thL_163_sin_r : (1486937083431 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) ≤ (95166913509 / 8000000000000 : ℝ) := by
  have hr := thL_163_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (11895961 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573) (11895961 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 - (11895961 / 1000000000 : ℝ)| ≤ (36752117564331 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 163) 573 - (11895961 / 1000000000 : ℝ))]

theorem thL_163_cos : (-95166913509 / 8000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 163) ∧ Real.cos (17670246 / 100000 * Real.log 163) ≤ (-1486937083431 / 125000000000000 : ℝ) := by
  have hc := thL_163_cos_r
  have hs := thL_163_sin_r
  rw [thL_163_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_163_sin : (39997162405191 / 40000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 163) ∧ Real.sin (17670246 / 100000 * Real.log 163) ≤ (124991178456369 / 125000000000000 : ℝ) := by
  have hc := thL_163_cos_r
  have hs := thL_163_sin_r
  rw [thL_163_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_163 : (-95166913509 / 8000000000000 : ℝ) ≤ cCG cZ 163 ∧ cCG cZ 163 ≤ (-1486937083431 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_163_cos

theorem sCB_163 : (39997162405191 / 40000000000000 : ℝ) ≤ sCG cZ 163 ∧ sCG cZ 163 ≤ (124991178456369 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_163_sin

theorem thL_164_r_bounds : (-47814818965606444089 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 ≤ (-47814782234393555911 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_164
  have hl : (180231788678122919 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 164 ∧ 17670246 / 100000 * Real.log 164 ≤ (225289735939362211 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_164_eq : (17670246 / 100000 * Real.log 164) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 + π) + ((143 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_164_cos_r : (221962107438261 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) ≤ (3468159363537 / 3906250000000 : ℝ) := by
  have hr := thL_164_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(239074003 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) (-(239074003 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 - (-(239074003 / 500000000 : ℝ))| ≤ (18365606444089 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 - (-(239074003 / 500000000 : ℝ)))]

theorem thL_164_sin_r : (-460135858937817 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) ≤ (-115033872906419 / 250000000000000 : ℝ) := by
  have hr := thL_164_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (239074003 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((49966420563642477873689197979010083132166526350333229273442220450164264415153077039471204657069011591281504214661464405189 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(239074003 / 500000000 : ℝ)) ∧ Real.sin (-(239074003 / 500000000 : ℝ)) ≤ -((1281190270862597105597607299702203994019120558262641635228240181631419393665756266076005543263738990979 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574) (-(239074003 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 - (-(239074003 / 500000000 : ℝ))| ≤ (18365606444089 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 164) 574 - (-(239074003 / 500000000 : ℝ)))]

theorem thL_164_cos : (-3468159363537 / 3906250000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 164) ∧ Real.cos (17670246 / 100000 * Real.log 164) ≤ (-221962107438261 / 250000000000000 : ℝ) := by
  have hc := thL_164_cos_r
  have hs := thL_164_sin_r
  rw [thL_164_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_164_sin : (115033872906419 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 164) ∧ Real.sin (17670246 / 100000 * Real.log 164) ≤ (460135858937817 / 1000000000000000 : ℝ) := by
  have hc := thL_164_cos_r
  have hs := thL_164_sin_r
  rw [thL_164_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_164 : (-3468159363537 / 3906250000000 : ℝ) ≤ cCG cZ 164 ∧ cCG cZ 164 ≤ (-221962107438261 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_164_cos

theorem sCB_164 : (115033872906419 / 250000000000000 : ℝ) ≤ sCG cZ 164 ∧ sCG cZ 164 ≤ (460135858937817 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_164_sin

theorem thL_166_r_bounds : (743437665290207519 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 ≤ (743440606709792481 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_166
  have hl : (56456301100951677 / 62500000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 166 ∧ 17670246 / 100000 * Real.log 166 ≤ (451650408991030541 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_166_eq : (17670246 / 100000 * Real.log 166) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 + π + π / 2) + ((143 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_166_cos_r : (995684940348661 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) ≤ (99568530802611 / 100000000000000 : ℝ) := by
  have hr := thL_166_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (23232473 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) (23232473 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 - (23232473 / 250000000 : ℝ)| ≤ (1470709792481 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 - (23232473 / 250000000 : ℝ))]

theorem thL_166_sin_r : (92796009358793 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) ≤ (46398188518121 / 500000000000000 : ℝ) := by
  have hr := thL_166_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (23232473 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575) (23232473 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 - (23232473 / 250000000 : ℝ)| ≤ (1470709792481 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 166) 575 - (23232473 / 250000000 : ℝ))]

theorem thL_166_cos : (92796009358793 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 166) ∧ Real.cos (17670246 / 100000 * Real.log 166) ≤ (46398188518121 / 500000000000000 : ℝ) := by
  have hc := thL_166_cos_r
  have hs := thL_166_sin_r
  rw [thL_166_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_166_sin : (-99568530802611 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 166) ∧ Real.sin (17670246 / 100000 * Real.log 166) ≤ (-995684940348661 / 1000000000000000 : ℝ) := by
  have hc := thL_166_cos_r
  have hs := thL_166_sin_r
  rw [thL_166_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_166 : (92796009358793 / 1000000000000000 : ℝ) ≤ cCG cZ 166 ∧ cCG cZ 166 ≤ (46398188518121 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_166_cos

theorem sCB_166 : (-99568530802611 / 100000000000000 : ℝ) ≤ sCG cZ 166 ∧ sCG cZ 166 ≤ (-995684940348661 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_166_sin

theorem thL_167_r_bounds : (-650917800717586443 / 1562500000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 ≤ (-650917227407413557 / 1562500000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_167
  have hl : (904362096841485459 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 167 ∧ 17670246 / 100000 * Real.log 167 ≤ (226090524302079927 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_167_eq : (17670246 / 100000 * Real.log 167) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) + ((144 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_167_cos_r : (914475037922693 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) ≤ (914475404841261 / 1000000000000000 : ℝ) := by
  have hr := thL_167_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(416587209 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) (-(416587209 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 - (-(416587209 / 1000000000 : ℝ))| ≤ (286655086443 / 1562500000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 - (-(416587209 / 1000000000 : ℝ)))]

theorem thL_167_sin_r : (-404642086230499 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) ≤ (-202320859655993 / 500000000000000 : ℝ) := by
  have hr := thL_167_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (416587209 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1481313077664967133600683599348249751917888836840354673297217085898440584223641506117543985794069191352764768194936349800629 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(416587209 / 1000000000 : ℝ)) ∧ Real.sin (-(416587209 / 1000000000 : ℝ)) ≤ -((199407529685667751926379462457457787473407104456459440501423976730574188192481564542706288732983163496311 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576) (-(416587209 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 - (-(416587209 / 1000000000 : ℝ))| ≤ (286655086443 / 1562500000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 167) 576 - (-(416587209 / 1000000000 : ℝ)))]

theorem thL_167_cos : (914475037922693 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 167) ∧ Real.cos (17670246 / 100000 * Real.log 167) ≤ (914475404841261 / 1000000000000000 : ℝ) := by
  have hc := thL_167_cos_r
  have hs := thL_167_sin_r
  rw [thL_167_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_167_sin : (-404642086230499 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 167) ∧ Real.sin (17670246 / 100000 * Real.log 167) ≤ (-202320859655993 / 500000000000000 : ℝ) := by
  have hc := thL_167_cos_r
  have hs := thL_167_sin_r
  rw [thL_167_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_167 : (914475037922693 / 1000000000000000 : ℝ) ≤ cCG cZ 167 ∧ cCG cZ 167 ≤ (914475404841261 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_167_cos

theorem sCB_167 : (-404642086230499 / 1000000000000000 : ℝ) ≤ sCG cZ 167 ∧ sCG cZ 167 ≤ (-202320859655993 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_167_sin

theorem thL_168_r_bounds : (1994861876296042739 / 3125000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 ≤ (1994863023703957261 / 3125000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_168
  have hl : (90541704003461147 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 168 ∧ 17670246 / 100000 * Real.log 168 ≤ (905417040401445719 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_168_eq : (17670246 / 100000 * Real.log 168) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) + ((144 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_168_cos_r : (160615257752111 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) ≤ (803076655940647 / 1000000000000000 : ℝ) := by
  have hr := thL_168_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (39897249 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) (39897249 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 - (39897249 / 62500000 : ℝ)| ≤ (573703957261 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 - (39897249 / 62500000 : ℝ))]

theorem thL_168_sin_r : (148968948266209 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) ≤ (595876160235839 / 1000000000000000 : ℝ) := by
  have hr := thL_168_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (39897249 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576) (39897249 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 - (39897249 / 62500000 : ℝ)| ≤ (573703957261 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 168) 576 - (39897249 / 62500000 : ℝ))]

theorem thL_168_cos : (160615257752111 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 168) ∧ Real.cos (17670246 / 100000 * Real.log 168) ≤ (803076655940647 / 1000000000000000 : ℝ) := by
  have hc := thL_168_cos_r
  have hs := thL_168_sin_r
  rw [thL_168_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_168_sin : (148968948266209 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 168) ∧ Real.sin (17670246 / 100000 * Real.log 168) ≤ (595876160235839 / 1000000000000000 : ℝ) := by
  have hc := thL_168_cos_r
  have hs := thL_168_sin_r
  rw [thL_168_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_168 : (160615257752111 / 200000000000000 : ℝ) ≤ cCG cZ 168 ∧ cCG cZ 168 ≤ (803076655940647 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_168_cos

theorem sCB_168 : (148968948266209 / 250000000000000 : ℝ) ≤ sCG cZ 168 ∧ sCG cZ 168 ≤ (595876160235839 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_168_sin

theorem thL_169_r_bounds : (11624183940902029571 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 ≤ (11624220659097970429 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_169
  have hl : (906465722400412079 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 169 ∧ 17670246 / 100000 * Real.log 169 ≤ (906465722767246329 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_169_eq : (17670246 / 100000 * Real.log 169) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 + π / 2) + ((144 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_169_cos_r : (248312829129481 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) ≤ (248312920924971 / 250000000000000 : ℝ) := by
  have hr := thL_169_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (116242023 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) (116242023 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 - (116242023 / 1000000000 : ℝ)| ≤ (18359097970429 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 - (116242023 / 1000000000 : ℝ))]

theorem thL_169_sin_r : (115980235150341 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) ≤ (115980602332301 / 1000000000000000 : ℝ) := by
  have hr := thL_169_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (116242023 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577) (116242023 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 - (116242023 / 1000000000 : ℝ)| ≤ (18359097970429 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 169) 577 - (116242023 / 1000000000 : ℝ))]

theorem thL_169_cos : (-115980602332301 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 169) ∧ Real.cos (17670246 / 100000 * Real.log 169) ≤ (-115980235150341 / 1000000000000000 : ℝ) := by
  have hc := thL_169_cos_r
  have hs := thL_169_sin_r
  rw [thL_169_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_169_sin : (248312829129481 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 169) ∧ Real.sin (17670246 / 100000 * Real.log 169) ≤ (248312920924971 / 250000000000000 : ℝ) := by
  have hc := thL_169_cos_r
  have hs := thL_169_sin_r
  rw [thL_169_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_169 : (-115980602332301 / 1000000000000000 : ℝ) ≤ cCG cZ 169 ∧ cCG cZ 169 ≤ (-115980235150341 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_169_cos

theorem sCB_169 : (248312829129481 / 250000000000000 : ℝ) ≤ sCG cZ 169 ∧ sCG cZ 169 ≤ (248312920924971 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_169_sin

theorem thL_171_r_bounds : (31216098079035995747 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 ≤ (31216116420964004253 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_171
  have hl : (908544598849035277 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 171 ∧ 17670246 / 100000 * Real.log 171 ≤ (454272299607934763 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_171_eq : (17670246 / 100000 * Real.log 171) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 + π) + ((144 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_171_cos_r : (811359360846547 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) ≤ (811359727692429 / 1000000000000000 : ℝ) := by
  have hr := thL_171_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (124864429 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) (124864429 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 - (124864429 / 200000000 : ℝ)| ≤ (9170964004253 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 - (124864429 / 200000000 : ℝ))]

theorem thL_171_sin_r : (584547239735149 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) ≤ (292273803287031 / 500000000000000 : ℝ) := by
  have hr := thL_171_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (124864429 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578) (124864429 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 - (124864429 / 200000000 : ℝ)| ≤ (9170964004253 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 171) 578 - (124864429 / 200000000 : ℝ))]

theorem thL_171_cos : (-811359727692429 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 171) ∧ Real.cos (17670246 / 100000 * Real.log 171) ≤ (-811359360846547 / 1000000000000000 : ℝ) := by
  have hc := thL_171_cos_r
  have hs := thL_171_sin_r
  rw [thL_171_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_171_sin : (-292273803287031 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 171) ∧ Real.sin (17670246 / 100000 * Real.log 171) ≤ (-584547239735149 / 1000000000000000 : ℝ) := by
  have hc := thL_171_cos_r
  have hs := thL_171_sin_r
  rw [thL_171_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_171 : (-811359727692429 / 1000000000000000 : ℝ) ≤ cCG cZ 171 ∧ cCG cZ 171 ≤ (-811359360846547 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_171_cos

theorem sCB_171 : (-292273803287031 / 500000000000000 : ℝ) ≤ sCG cZ 171 ∧ sCG cZ 171 ≤ (-584547239735149 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_171_sin

theorem thL_172_r_bounds : (8386359739449353417 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 ≤ (8386396460550646583 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_172
  have hl : (2273937342030041 / 2500000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 172 ∧ 17670246 / 100000 * Real.log 172 ≤ (909574937178850649 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_172_eq : (17670246 / 100000 * Real.log 172) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 + π + π / 2) + ((144 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_172_cos_r : (996485310069999 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) ≤ (996485677281013 / 1000000000000000 : ℝ) := by
  have hr := thL_172_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (83863781 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) (83863781 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 - (83863781 / 1000000000 : ℝ)| ≤ (18360550646583 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 - (83863781 / 1000000000 : ℝ))]

theorem thL_172_sin_r : (83765327759751 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) ≤ (16753138994153 / 200000000000000 : ℝ) := by
  have hr := thL_172_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (83863781 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579) (83863781 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 - (83863781 / 1000000000 : ℝ)| ≤ (18360550646583 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 172) 579 - (83863781 / 1000000000 : ℝ))]

theorem thL_172_cos : (83765327759751 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 172) ∧ Real.cos (17670246 / 100000 * Real.log 172) ≤ (16753138994153 / 200000000000000 : ℝ) := by
  have hc := thL_172_cos_r
  have hs := thL_172_sin_r
  rw [thL_172_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_172_sin : (-996485677281013 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 172) ∧ Real.sin (17670246 / 100000 * Real.log 172) ≤ (-996485310069999 / 1000000000000000 : ℝ) := by
  have hc := thL_172_cos_r
  have hs := thL_172_sin_r
  rw [thL_172_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_172 : (83765327759751 / 1000000000000000 : ℝ) ≤ cCG cZ 172 ∧ cCG cZ 172 ≤ (16753138994153 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_172_cos

theorem sCB_172 : (-996485677281013 / 1000000000000000 : ℝ) ≤ sCG cZ 172 ∧ sCG cZ 172 ≤ (-996485310069999 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_172_sin

theorem thL_173_r_bounds : (-2312838867702504233 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 ≤ (-2312837032297495767 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_173
  have hl : (910599301767746291 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 173 ∧ 17670246 / 100000 * Real.log 173 ≤ (45529965106729027 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_173_eq : (17670246 / 100000 * Real.log 173) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) + ((145 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_173_cos_r : (894909484897633 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) ≤ (223727462994709 / 250000000000000 : ℝ) := by
  have hr := thL_173_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(46256759 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) (-(46256759 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 - (-(46256759 / 100000000 : ℝ))| ≤ (917702504233 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 - (-(46256759 / 100000000 : ℝ)))]

theorem thL_173_sin_r : (-223123760021509 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) ≤ (-55780894120251 / 125000000000000 : ℝ) := by
  have hr := thL_173_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (46256759 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((277879144634576787081104058447815751352639063064413130792315950885262889943558392755337114302742587161631265661079 / 622702080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(46256759 / 100000000 : ℝ)) ∧ Real.sin (-(46256759 / 100000000 : ℝ)) ≤ -((178127656817033556511641154904656966922351928169558853885735244759985893760878400746185543103641 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580) (-(46256759 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 - (-(46256759 / 100000000 : ℝ))| ≤ (917702504233 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 173) 580 - (-(46256759 / 100000000 : ℝ)))]

theorem thL_173_cos : (894909484897633 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 173) ∧ Real.cos (17670246 / 100000 * Real.log 173) ≤ (223727462994709 / 250000000000000 : ℝ) := by
  have hc := thL_173_cos_r
  have hs := thL_173_sin_r
  rw [thL_173_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_173_sin : (-223123760021509 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 173) ∧ Real.sin (17670246 / 100000 * Real.log 173) ≤ (-55780894120251 / 125000000000000 : ℝ) := by
  have hc := thL_173_cos_r
  have hs := thL_173_sin_r
  rw [thL_173_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_173 : (894909484897633 / 1000000000000000 : ℝ) ≤ cCG cZ 173 ∧ cCG cZ 173 ≤ (223727462994709 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_173_cos

theorem sCB_173 : (-223123760021509 / 500000000000000 : ℝ) ≤ sCG cZ 173 ∧ sCG cZ 173 ≤ (-55780894120251 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_173_sin

theorem thL_174_r_bounds : (2779465141480785767 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 ≤ (2779466978519214233 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_174
  have hl : (911617762569909633 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 174 ∧ 17670246 / 100000 * Real.log 174 ≤ (455808881468371941 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_174_eq : (17670246 / 100000 * Real.log 174) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) + ((145 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_174_cos_r : (424714622755337 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) ≤ (424714806460089 / 500000000000000 : ℝ) := by
  have hr := thL_174_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (138973303 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) (138973303 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 - (138973303 / 250000000 : ℝ)| ≤ (918519214233 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 - (138973303 / 250000000 : ℝ))]

theorem thL_174_sin_r : (52770204746553 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) ≤ (105540482974659 / 200000000000000 : ℝ) := by
  have hr := thL_174_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (138973303 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580) (138973303 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 - (138973303 / 250000000 : ℝ)| ≤ (918519214233 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 174) 580 - (138973303 / 250000000 : ℝ))]

theorem thL_174_cos : (424714622755337 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 174) ∧ Real.cos (17670246 / 100000 * Real.log 174) ≤ (424714806460089 / 500000000000000 : ℝ) := by
  have hc := thL_174_cos_r
  have hs := thL_174_sin_r
  rw [thL_174_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_174_sin : (52770204746553 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 174) ∧ Real.sin (17670246 / 100000 * Real.log 174) ≤ (105540482974659 / 200000000000000 : ℝ) := by
  have hc := thL_174_cos_r
  have hs := thL_174_sin_r
  rw [thL_174_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_174 : (424714622755337 / 500000000000000 : ℝ) ≤ cCG cZ 174 ∧ cCG cZ 174 ≤ (424714806460089 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_174_cos

theorem sCB_174 : (52770204746553 / 100000000000000 : ℝ) ≤ sCG cZ 174 ∧ sCG cZ 174 ≤ (105540482974659 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_174_sin

theorem thL_176_r_bounds : (-28311047936995830407 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 ≤ (-28311029563004169593 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_176
  have hl : (1827274482473071 / 2000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 176 ∧ 17670246 / 100000 * Real.log 176 ≤ (913637241603369749 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_176_eq : (17670246 / 100000 * Real.log 176) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 + π) + ((145 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_176_cos_r : (843934165259159 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) ≤ (843934532741261 / 1000000000000000 : ℝ) := by
  have hr := thL_176_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(22648831 / 40000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) (-(22648831 / 40000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 - (-(22648831 / 40000000 : ℝ))| ≤ (9186995830407 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 - (-(22648831 / 40000000 : ℝ)))]

theorem thL_176_sin_r : (-53644665318089 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) ≤ (-536446285700957 / 1000000000000000 : ℝ) := by
  have hr := thL_176_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (22648831 / 40000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2241746988600260918311616037228114507988913185531169073171998372583781166574956313059373612397916933725140991 / 4178882919923712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(22648831 / 40000000 : ℝ)) ∧ Real.sin (-(22648831 / 40000000 : ℝ)) ≤ -((8981358127403238203305383592933570221627667404134865532916229077650911034201595842757818369 / 16742319390720000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582) (-(22648831 / 40000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 - (-(22648831 / 40000000 : ℝ))| ≤ (9186995830407 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 176) 582 - (-(22648831 / 40000000 : ℝ)))]

theorem thL_176_cos : (-843934532741261 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 176) ∧ Real.cos (17670246 / 100000 * Real.log 176) ≤ (-843934165259159 / 1000000000000000 : ℝ) := by
  have hc := thL_176_cos_r
  have hs := thL_176_sin_r
  rw [thL_176_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_176_sin : (536446285700957 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 176) ∧ Real.sin (17670246 / 100000 * Real.log 176) ≤ (53644665318089 / 100000000000000 : ℝ) := by
  have hc := thL_176_cos_r
  have hs := thL_176_sin_r
  rw [thL_176_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_176 : (-843934532741261 / 1000000000000000 : ℝ) ≤ cCG cZ 176 ∧ cCG cZ 176 ≤ (-843934165259159 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_176_cos

theorem sCB_176 : (536446285700957 / 1000000000000000 : ℝ) ≤ sCG cZ 176 ∧ sCG cZ 176 ≤ (53644665318089 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_176_sin

theorem thL_177_r_bounds : (43492880217419460523 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 ≤ (43492916982580539477 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_177
  have hl : (914638390996804027 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 177 ∧ 17670246 / 100000 * Real.log 177 ≤ (228659597840909569 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_177_eq : (17670246 / 100000 * Real.log 177) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 + π) + ((145 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_177_cos_r : (181379956444997 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) ≤ (906900149876693 / 1000000000000000 : ℝ) := by
  have hr := thL_177_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (217464493 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) (217464493 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 - (217464493 / 500000000 : ℝ)| ≤ (18382580539477 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 - (217464493 / 500000000 : ℝ))]

theorem thL_177_sin_r : (3370766528073 / 8000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) ≤ (21067309183037 / 50000000000000 : ℝ) := by
  have hr := thL_177_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (217464493 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582) (217464493 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 - (217464493 / 500000000 : ℝ)| ≤ (18382580539477 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 177) 582 - (217464493 / 500000000 : ℝ))]

theorem thL_177_cos : (-906900149876693 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 177) ∧ Real.cos (17670246 / 100000 * Real.log 177) ≤ (-181379956444997 / 200000000000000 : ℝ) := by
  have hc := thL_177_cos_r
  have hs := thL_177_sin_r
  rw [thL_177_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_177_sin : (-21067309183037 / 50000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 177) ∧ Real.sin (17670246 / 100000 * Real.log 177) ≤ (-3370766528073 / 8000000000000 : ℝ) := by
  have hc := thL_177_cos_r
  have hs := thL_177_sin_r
  rw [thL_177_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_177 : (-906900149876693 / 1000000000000000 : ℝ) ≤ cCG cZ 177 ∧ cCG cZ 177 ≤ (-181379956444997 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_177_cos

theorem sCB_177 : (-21067309183037 / 50000000000000 : ℝ) ≤ sCG cZ 177 ∧ sCG cZ 177 ≤ (-3370766528073 / 8000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_177_sin

theorem thL_178_r_bounds : (-28071614922655802801 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 ≤ (-28071541477344197199 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_178
  have hl : (18312678008936229 / 20000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 178 ∧ 17670246 / 100000 * Real.log 178 ≤ (915633900813645699 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_178_eq : (17670246 / 100000 * Real.log 178) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 + π + π / 2) + ((145 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_178_cos_r : (495082903979597 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) ≤ (990166175185753 / 1000000000000000 : ℝ) := by
  have hr := thL_178_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(140357891 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) (-(140357891 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 - (-(140357891 / 1000000000 : ℝ))| ≤ (36722655802801 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 - (-(140357891 / 1000000000 : ℝ)))]

theorem thL_178_sin_r : (-69948839353147 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) ≤ (-27979462295947 / 200000000000000 : ℝ) := by
  have hr := thL_178_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (140357891 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((871144611812097851155651373607273395901224143510513698474790160551602406408985073683596640929958006021008511967971753713500371 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(140357891 / 1000000000 : ℝ)) ∧ Real.sin (-(140357891 / 1000000000 : ℝ)) ≤ -((5584260332128832379150297235733197819994503490910022887099466689797142105265520011338245075698218564712709 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583) (-(140357891 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 - (-(140357891 / 1000000000 : ℝ))| ≤ (36722655802801 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 178) 583 - (-(140357891 / 1000000000 : ℝ)))]

theorem thL_178_cos : (-69948839353147 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 178) ∧ Real.cos (17670246 / 100000 * Real.log 178) ≤ (-27979462295947 / 200000000000000 : ℝ) := by
  have hc := thL_178_cos_r
  have hs := thL_178_sin_r
  rw [thL_178_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_178_sin : (-990166175185753 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 178) ∧ Real.sin (17670246 / 100000 * Real.log 178) ≤ (-495082903979597 / 500000000000000 : ℝ) := by
  have hc := thL_178_cos_r
  have hs := thL_178_sin_r
  rw [thL_178_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_178 : (-69948839353147 / 500000000000000 : ℝ) ≤ cCG cZ 178 ∧ cCG cZ 178 ≤ (-27979462295947 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_178_cos

theorem sCB_178 : (-990166175185753 / 1000000000000000 : ℝ) ≤ sCG cZ 178 ∧ sCG cZ 178 ≤ (-495082903979597 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_178_sin

theorem thL_179_r_bounds : (-9015275805308567121 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 ≤ (-9015271219691432879 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_179
  have hl : (458311916391905031 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 179 ∧ 17670246 / 100000 * Real.log 179 ≤ (916623833150644311 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_179_eq : (17670246 / 100000 * Real.log 179) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) + ((146 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_179_cos_r : (750999295052741 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) ≤ (93874957742933 / 125000000000000 : ℝ) := by
  have hr := thL_179_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(721221881 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) (-(721221881 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 - (-(721221881 / 1000000000 : ℝ))| ≤ (2292808567121 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 - (-(721221881 / 1000000000 : ℝ)))]

theorem thL_179_sin_r : (-165075745018841 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) ≤ (-330151306611849 / 500000000000000 : ℝ) := by
  have hr := thL_179_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (721221881 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4111719249041945048642763665981867026461108039607777775043018407849550919916537134897937707303892453612439560863563130261359641 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(721221881 / 1000000000 : ℝ)) ∧ Real.sin (-(721221881 / 1000000000 : ℝ)) ≤ -((26357174673254227838100622866597375872371706452059343564019280082873780444850166833239978811119945166887319 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584) (-(721221881 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 - (-(721221881 / 1000000000 : ℝ))| ≤ (2292808567121 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 179) 584 - (-(721221881 / 1000000000 : ℝ)))]

theorem thL_179_cos : (750999295052741 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 179) ∧ Real.cos (17670246 / 100000 * Real.log 179) ≤ (93874957742933 / 125000000000000 : ℝ) := by
  have hc := thL_179_cos_r
  have hs := thL_179_sin_r
  rw [thL_179_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_179_sin : (-165075745018841 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 179) ∧ Real.sin (17670246 / 100000 * Real.log 179) ≤ (-330151306611849 / 500000000000000 : ℝ) := by
  have hc := thL_179_cos_r
  have hs := thL_179_sin_r
  rw [thL_179_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_179 : (750999295052741 / 1000000000000000 : ℝ) ≤ cCG cZ 179 ∧ cCG cZ 179 ≤ (93874957742933 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_179_cos

theorem sCB_179 : (-165075745018841 / 250000000000000 : ℝ) ≤ sCG cZ 179 ∧ sCG cZ 179 ≤ (-330151306611849 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_179_sin

theorem thL_181_r_bounds : (-6572750517086735009 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 ≤ (-6572743162913264991 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_181
  have hl : (918587213650034609 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 181 ∧ 17670246 / 100000 * Real.log 181 ≤ (918587214016868859 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_181_eq : (17670246 / 100000 * Real.log 181) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 + π / 2) + ((146 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_181_cos_r : (946482841039387 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) ≤ (189296641749613 / 200000000000000 : ℝ) := by
  have hr := thL_181_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(164318671 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) (-(164318671 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 - (-(164318671 / 500000000 : ℝ))| ≤ (3677086735009 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 - (-(164318671 / 500000000 : ℝ)))]

theorem thL_181_sin_r : (-161376889816471 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) ≤ (-322753411924267 / 1000000000000000 : ℝ) := by
  have hr := thL_181_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (164318671 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((22303282073288379482419722452625815434316539068492149257267455370363503462565515893660955379193809756985869314124709125901 / 69103125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(164318671 / 500000000 : ℝ)) ∧ Real.sin (-(164318671 / 500000000 : ℝ)) ≤ -((571879027520214710110363160635390187377645890612062360195975063726149341148420386990983671856957782739 / 1771875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585) (-(164318671 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 - (-(164318671 / 500000000 : ℝ))| ≤ (3677086735009 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 181) 585 - (-(164318671 / 500000000 : ℝ)))]

theorem thL_181_cos : (322753411924267 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 181) ∧ Real.cos (17670246 / 100000 * Real.log 181) ≤ (161376889816471 / 500000000000000 : ℝ) := by
  have hc := thL_181_cos_r
  have hs := thL_181_sin_r
  rw [thL_181_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_181_sin : (946482841039387 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 181) ∧ Real.sin (17670246 / 100000 * Real.log 181) ≤ (189296641749613 / 200000000000000 : ℝ) := by
  have hc := thL_181_cos_r
  have hs := thL_181_sin_r
  rw [thL_181_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_181 : (322753411924267 / 1000000000000000 : ℝ) ≤ cCG cZ 181 ∧ cCG cZ 181 ≤ (161376889816471 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_181_cos

theorem sCB_181 : (946482841039387 / 1000000000000000 : ℝ) ≤ sCG cZ 181 ∧ sCG cZ 181 ≤ (189296641749613 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_181_sin

theorem thL_182_r_bounds : (25797288422868429901 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 ≤ (25797303097131570099 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_182
  have hl : (919560783385586233 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 182 ∧ 17670246 / 100000 * Real.log 182 ≤ (919560783752420483 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_182_eq : (17670246 / 100000 * Real.log 182) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 + π / 2) + ((146 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_182_cos_r : (199785056574827 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) ≤ (399570296583349 / 500000000000000 : ℝ) := by
  have hr := thL_182_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (322466197 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) (322466197 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 - (322466197 / 500000000 : ℝ)| ≤ (7337131570099 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 - (322466197 / 500000000 : ℝ))]

theorem thL_182_sin_r : (601144229772503 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) ≤ (601144596629619 / 1000000000000000 : ℝ) := by
  have hr := thL_182_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (322466197 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585) (322466197 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 - (322466197 / 500000000 : ℝ)| ≤ (7337131570099 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 182) 585 - (322466197 / 500000000 : ℝ))]

theorem thL_182_cos : (-601144596629619 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 182) ∧ Real.cos (17670246 / 100000 * Real.log 182) ≤ (-601144229772503 / 1000000000000000 : ℝ) := by
  have hc := thL_182_cos_r
  have hs := thL_182_sin_r
  rw [thL_182_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_182_sin : (199785056574827 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 182) ∧ Real.sin (17670246 / 100000 * Real.log 182) ≤ (399570296583349 / 500000000000000 : ℝ) := by
  have hc := thL_182_cos_r
  have hs := thL_182_sin_r
  rw [thL_182_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_182 : (-601144596629619 / 1000000000000000 : ℝ) ≤ cCG cZ 182 ∧ cCG cZ 182 ≤ (-601144229772503 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_182_cos

theorem sCB_182 : (199785056574827 / 250000000000000 : ℝ) ≤ sCG cZ 182 ∧ sCG cZ 182 ≤ (399570296583349 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_182_sin

theorem thL_183_r_bounds : (2118548164690693439 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 ≤ (2118566535309306561 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_183
  have hl : (230132254616420339 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 183 ∧ 17670246 / 100000 * Real.log 183 ≤ (184105803766503121 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_183_eq : (17670246 / 100000 * Real.log 183) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 + π) + ((146 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_183_cos_r : (999102293534759 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) ≤ (249775665236783 / 250000000000000 : ℝ) := by
  have hr := thL_183_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (42371147 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) (42371147 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 - (42371147 / 1000000000 : ℝ)| ≤ (9185309306561 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 - (42371147 / 1000000000 : ℝ))]

theorem thL_183_sin_r : (4235828617891 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) ≤ (42358653591283 / 1000000000000000 : ℝ) := by
  have hr := thL_183_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (42371147 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586) (42371147 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 - (42371147 / 1000000000 : ℝ)| ≤ (9185309306561 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 183) 586 - (42371147 / 1000000000 : ℝ))]

theorem thL_183_cos : (-249775665236783 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 183) ∧ Real.cos (17670246 / 100000 * Real.log 183) ≤ (-999102293534759 / 1000000000000000 : ℝ) := by
  have hc := thL_183_cos_r
  have hs := thL_183_sin_r
  rw [thL_183_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_183_sin : (-42358653591283 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 183) ∧ Real.sin (17670246 / 100000 * Real.log 183) ≤ (-4235828617891 / 100000000000000 : ℝ) := by
  have hc := thL_183_cos_r
  have hs := thL_183_sin_r
  rw [thL_183_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_183 : (-249775665236783 / 250000000000000 : ℝ) ≤ cCG cZ 183 ∧ cCG cZ 183 ≤ (-999102293534759 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_183_cos

theorem sCB_183 : (-42358653591283 / 1000000000000000 : ℝ) ≤ sCG cZ 183 ∧ sCG cZ 183 ≤ (-4235828617891 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_183_sin

theorem thL_184_r_bounds : (-113093358893310498189 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 ≤ (-113093285506689501811 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_184
  have hl : (921491977034137763 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 184 ∧ 17670246 / 100000 * Real.log 184 ≤ (230372994350243003 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_184_eq : (17670246 / 100000 * Real.log 184) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 + π + π / 2) + ((146 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_184_cos_r : (844338494109941 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) ≤ (422169430522639 / 500000000000000 : ℝ) := by
  have hr := thL_184_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(565466611 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) (-(565466611 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 - (-(565466611 / 1000000000 : ℝ))| ≤ (36693310498189 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 - (-(565466611 / 1000000000 : ℝ)))]

theorem thL_184_sin_r : (-66976254438493 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) ≤ (-535809668574741 / 1000000000000000 : ℝ) := by
  have hr := thL_184_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (565466611 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((476642727643808936009280273180689630386700992388458424564103664754286047885785358120179424995773730806420355697748755712266533 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(565466611 / 1000000000 : ℝ)) ∧ Real.sin (-(565466611 / 1000000000 : ℝ)) ≤ -((21387814701961911533539874374328916679755248189306321576236611178151813027706359585550704499137565468436789 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587) (-(565466611 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 - (-(565466611 / 1000000000 : ℝ))| ≤ (36693310498189 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 184) 587 - (-(565466611 / 1000000000 : ℝ)))]

theorem thL_184_cos : (-66976254438493 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 184) ∧ Real.cos (17670246 / 100000 * Real.log 184) ≤ (-535809668574741 / 1000000000000000 : ℝ) := by
  have hc := thL_184_cos_r
  have hs := thL_184_sin_r
  rw [thL_184_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_184_sin : (-422169430522639 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 184) ∧ Real.sin (17670246 / 100000 * Real.log 184) ≤ (-844338494109941 / 1000000000000000 : ℝ) := by
  have hc := thL_184_cos_r
  have hs := thL_184_sin_r
  rw [thL_184_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_184 : (-66976254438493 / 125000000000000 : ℝ) ≤ cCG cZ 184 ∧ cCG cZ 184 ≤ (-535809668574741 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_184_cos

theorem sCB_184 : (-422169430522639 / 500000000000000 : ℝ) ≤ sCG cZ 184 ∧ sCG cZ 184 ≤ (-844338494109941 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_184_sin

theorem thL_186_r_bounds : (-11297382539646555509 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 ≤ (-11297364160353444491 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_186
  have hl : (923402292504606281 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 186 ∧ 17670246 / 100000 * Real.log 186 ≤ (92340229287144053 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_186_eq : (17670246 / 100000 * Real.log 186) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_186_cos_r : (974582099858789 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) ≤ (243645616861163 / 250000000000000 : ℝ) := by
  have hr := thL_186_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(225947467 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) (-(225947467 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 - (-(225947467 / 1000000000 : ℝ))| ≤ (9189646555509 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 - (-(225947467 / 1000000000 : ℝ)))]

theorem thL_186_sin_r : (-112015015447077 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) ≤ (-224029663308291 / 1000000000000000 : ℝ) := by
  have hr := thL_186_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (225947467 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((199291216817162015402423400304220185908757211646002115320173226108627273711987858123194843134537303446842392752048969813730541 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(225947467 / 1000000000 : ℝ)) ∧ Real.sin (-(225947467 / 1000000000 : ℝ)) ≤ -((8942554600770090409080904314295316225598675510998287272328034908383050299413331586858418497095929737774317 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588) (-(225947467 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 - (-(225947467 / 1000000000 : ℝ))| ≤ (9189646555509 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 186) 588 - (-(225947467 / 1000000000 : ℝ)))]

theorem thL_186_cos : (974582099858789 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 186) ∧ Real.cos (17670246 / 100000 * Real.log 186) ≤ (243645616861163 / 250000000000000 : ℝ) := by
  have hc := thL_186_cos_r
  have hs := thL_186_sin_r
  rw [thL_186_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_186_sin : (-112015015447077 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 186) ∧ Real.sin (17670246 / 100000 * Real.log 186) ≤ (-224029663308291 / 1000000000000000 : ℝ) := by
  have hc := thL_186_cos_r
  have hs := thL_186_sin_r
  rw [thL_186_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_186 : (974582099858789 / 1000000000000000 : ℝ) ≤ cCG cZ 186 ∧ cCG cZ 186 ≤ (243645616861163 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_186_cos

theorem sCB_186 : (-112015015447077 / 500000000000000 : ℝ) ≤ sCG cZ 186 ∧ sCG cZ 186 ≤ (-224029663308291 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_186_sin

theorem thL_187_r_bounds : (18038022312393952681 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 ≤ (18038031487606047319 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_187
  have hl : (184869952209613841 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 187 ∧ 17670246 / 100000 * Real.log 187 ≤ (462174880707451727 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_187_eq : (17670246 / 100000 * Real.log 187) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_187_cos_r : (75080170206683 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) ≤ (93850258639609 / 125000000000000 : ℝ) := by
  have hr := thL_187_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (180380269 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) (180380269 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 - (180380269 / 250000000 : ℝ)| ≤ (4587606047319 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 - (180380269 / 250000000 : ℝ))]

theorem thL_187_sin_r : (41282954929711 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) ≤ (660527645886167 / 1000000000000000 : ℝ) := by
  have hr := thL_187_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (180380269 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588) (180380269 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 - (180380269 / 250000000 : ℝ)| ≤ (4587606047319 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 187) 588 - (180380269 / 250000000 : ℝ))]

theorem thL_187_cos : (75080170206683 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 187) ∧ Real.cos (17670246 / 100000 * Real.log 187) ≤ (93850258639609 / 125000000000000 : ℝ) := by
  have hc := thL_187_cos_r
  have hs := thL_187_sin_r
  rw [thL_187_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_187_sin : (41282954929711 / 62500000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 187) ∧ Real.sin (17670246 / 100000 * Real.log 187) ≤ (660527645886167 / 1000000000000000 : ℝ) := by
  have hc := thL_187_cos_r
  have hs := thL_187_sin_r
  rw [thL_187_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_187 : (75080170206683 / 100000000000000 : ℝ) ≤ cCG cZ 187 ∧ cCG cZ 187 ≤ (93850258639609 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_187_cos

theorem sCB_187 : (41282954929711 / 62500000000000 : ℝ) ≤ sCG cZ 187 ∧ sCG cZ 187 ≤ (660527645886167 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_187_sin

theorem thL_188_r_bounds : (9313991941298672647 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 ≤ (9314028658701327353 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_188
  have hl : (115661522050243359 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 188 ∧ 17670246 / 100000 * Real.log 188 ≤ (462646088384390561 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_188_eq : (17670246 / 100000 * Real.log 188) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 + π / 2) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_188_cos_r : (995665411820949 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) ≤ (995665778994977 / 1000000000000000 : ℝ) := by
  have hr := thL_188_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (93140103 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) (93140103 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 - (93140103 / 1000000000 : ℝ)| ≤ (18358701327353 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 - (93140103 / 1000000000 : ℝ))]

theorem thL_188_sin_r : (23251327881083 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) ≤ (2325141967459 / 25000000000000 : ℝ) := by
  have hr := thL_188_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (93140103 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589) (93140103 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 - (93140103 / 1000000000 : ℝ)| ≤ (18358701327353 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 188) 589 - (93140103 / 1000000000 : ℝ))]

theorem thL_188_cos : (-2325141967459 / 25000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 188) ∧ Real.cos (17670246 / 100000 * Real.log 188) ≤ (-23251327881083 / 250000000000000 : ℝ) := by
  have hc := thL_188_cos_r
  have hs := thL_188_sin_r
  rw [thL_188_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_188_sin : (995665411820949 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 188) ∧ Real.sin (17670246 / 100000 * Real.log 188) ≤ (995665778994977 / 1000000000000000 : ℝ) := by
  have hc := thL_188_cos_r
  have hs := thL_188_sin_r
  rw [thL_188_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_188 : (-2325141967459 / 25000000000000 : ℝ) ≤ cCG cZ 188 ∧ cCG cZ 188 ≤ (-23251327881083 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_188_cos

theorem sCB_188 : (995665411820949 / 1000000000000000 : ℝ) ≤ sCG cZ 188 ∧ sCG cZ 188 ≤ (995665778994977 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_188_sin

theorem thL_189_r_bounds : (-10804812552537286973 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 ≤ (-10804805207462713027 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_189
  have hl : (926229592181362141 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 189 ∧ 17670246 / 100000 * Real.log 189 ≤ (92622959254819639 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_189_eq : (17670246 / 100000 * Real.log 189) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 + π) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_189_cos_r : (857584852028993 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) ≤ (857585219284013 / 1000000000000000 : ℝ) := by
  have hr := thL_189_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(135060111 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) (-(135060111 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 - (-(135060111 / 250000000 : ℝ))| ≤ (3672537286973 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 - (-(135060111 / 250000000 : ℝ)))]

theorem thL_189_sin_r : (-514342391322219 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) ≤ (-128585506017109 / 250000000000000 : ℝ) := by
  have hr := thL_189_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (135060111 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((196402187310428516924279582672699060597480173145132859973981958776866851967337850826287386360481236456472920476369717 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(135060111 / 250000000 : ℝ)) ∧ Real.sin (-(135060111 / 250000000 : ℝ)) ≤ -((60431442249356320270821264925217057900540489957723742967497593654551123964868259617586563767216769 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590) (-(135060111 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 - (-(135060111 / 250000000 : ℝ))| ≤ (3672537286973 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 189) 590 - (-(135060111 / 250000000 : ℝ)))]

theorem thL_189_cos : (-857585219284013 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 189) ∧ Real.cos (17670246 / 100000 * Real.log 189) ≤ (-857584852028993 / 1000000000000000 : ℝ) := by
  have hc := thL_189_cos_r
  have hs := thL_189_sin_r
  rw [thL_189_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_189_sin : (128585506017109 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 189) ∧ Real.sin (17670246 / 100000 * Real.log 189) ≤ (514342391322219 / 1000000000000000 : ℝ) := by
  have hc := thL_189_cos_r
  have hs := thL_189_sin_r
  rw [thL_189_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_189 : (-857585219284013 / 1000000000000000 : ℝ) ≤ cCG cZ 189 ∧ cCG cZ 189 ≤ (-857584852028993 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_189_cos

theorem sCB_189 : (128585506017109 / 250000000000000 : ℝ) ≤ sCG cZ 189 ∧ sCG cZ 189 ≤ (514342391322219 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_189_sin

theorem thL_191_r_bounds : (-50198776929024593577 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 ≤ (-50198703470975406423 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_191
  have hl : (928089635251138779 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 191 ∧ 17670246 / 100000 * Real.log 191 ≤ (928089635617973029 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_191_eq : (17670246 / 100000 * Real.log 191) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 + π + π / 2) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_191_cos_r : (242166478543013 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) ≤ (968666281462299 / 1000000000000000 : ℝ) := by
  have hr := thL_191_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(250993701 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) (-(250993701 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 - (-(250993701 / 1000000000 : ℝ))| ≤ (36729024593577 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 - (-(250993701 / 1000000000 : ℝ)))]

theorem thL_191_sin_r : (-248366829835079 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) ≤ (-248366462544833 / 1000000000000000 : ℝ) := by
  have hr := thL_191_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (250993701 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((909220618372191003671831631109868637023644833378781332889799616626979613100182033927396492557861750373408911632258160856401 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(250993701 / 1000000000 : ℝ)) ∧ Real.sin (-(250993701 / 1000000000 : ℝ)) ≤ -((17485011891772903739384202279717154832170182509166164827777864239580362988864883687243331906241786262997 / 70400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591) (-(250993701 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 - (-(250993701 / 1000000000 : ℝ))| ≤ (36729024593577 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 191) 591 - (-(250993701 / 1000000000 : ℝ)))]

theorem thL_191_cos : (-248366829835079 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 191) ∧ Real.cos (17670246 / 100000 * Real.log 191) ≤ (-248366462544833 / 1000000000000000 : ℝ) := by
  have hc := thL_191_cos_r
  have hs := thL_191_sin_r
  rw [thL_191_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_191_sin : (-968666281462299 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 191) ∧ Real.sin (17670246 / 100000 * Real.log 191) ≤ (-242166478543013 / 250000000000000 : ℝ) := by
  have hc := thL_191_cos_r
  have hs := thL_191_sin_r
  rw [thL_191_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_191 : (-248366829835079 / 1000000000000000 : ℝ) ≤ cCG cZ 191 ∧ cCG cZ 191 ≤ (-248366462544833 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_191_cos

theorem sCB_191 : (-968666281462299 / 1000000000000000 : ℝ) ≤ sCG cZ 191 ∧ sCG cZ 191 ≤ (-242166478543013 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_191_sin

theorem thL_192_r_bounds : (67173646235917896493 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 ≤ (67173682964082103507 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_192
  have hl : (464506182799295237 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 192 ∧ 17670246 / 100000 * Real.log 192 ≤ (929012365965424723 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_192_eq : (17670246 / 100000 * Real.log 192) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 + π + π / 2) + ((147 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_192_cos_r : (78274186795509 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) ≤ (156548447050871 / 200000000000000 : ℝ) := by
  have hr := thL_192_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (335868323 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) (335868323 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 - (335868323 / 500000000 : ℝ)| ≤ (18364082103507 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 - (335868323 / 500000000 : ℝ))]

theorem thL_192_sin_r : (622346087043573 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) ≤ (622346454326127 / 1000000000000000 : ℝ) := by
  have hr := thL_192_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (335868323 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591) (335868323 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 - (335868323 / 500000000 : ℝ)| ≤ (18364082103507 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 192) 591 - (335868323 / 500000000 : ℝ))]

theorem thL_192_cos : (622346087043573 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 192) ∧ Real.cos (17670246 / 100000 * Real.log 192) ≤ (622346454326127 / 1000000000000000 : ℝ) := by
  have hc := thL_192_cos_r
  have hs := thL_192_sin_r
  rw [thL_192_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_192_sin : (-156548447050871 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 192) ∧ Real.sin (17670246 / 100000 * Real.log 192) ≤ (-78274186795509 / 100000000000000 : ℝ) := by
  have hc := thL_192_cos_r
  have hs := thL_192_sin_r
  rw [thL_192_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_192 : (622346087043573 / 1000000000000000 : ℝ) ≤ cCG cZ 192 ∧ cCG cZ 192 ≤ (622346454326127 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_192_cos

theorem sCB_192 : (-156548447050871 / 200000000000000 : ℝ) ≤ sCG cZ 192 ∧ sCG cZ 192 ≤ (-78274186795509 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_192_sin

theorem thL_193_r_bounds : (235963218068380161 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 ≤ (235967806931619839 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_193
  have hl : (929930302520024269 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 193 ∧ 17670246 / 100000 * Real.log 193 ≤ (464965151443429259 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_193_eq : (17670246 / 100000 * Real.log 193) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_193_cos_r : (999821646622583 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) ≤ (999822013731643 / 1000000000000000 : ℝ) := by
  have hr := thL_193_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (18877241 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) (18877241 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 - (18877241 / 1000000000 : ℝ)| ≤ (2294431619839 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 - (18877241 / 1000000000 : ℝ))]

theorem thL_193_sin_r : (4718984078481 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) ≤ (2359537927873 / 125000000000000 : ℝ) := by
  have hr := thL_193_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (18877241 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592) (18877241 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 - (18877241 / 1000000000 : ℝ)| ≤ (2294431619839 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 193) 592 - (18877241 / 1000000000 : ℝ))]

theorem thL_193_cos : (999821646622583 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 193) ∧ Real.cos (17670246 / 100000 * Real.log 193) ≤ (999822013731643 / 1000000000000000 : ℝ) := by
  have hc := thL_193_cos_r
  have hs := thL_193_sin_r
  rw [thL_193_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_193_sin : (4718984078481 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 193) ∧ Real.sin (17670246 / 100000 * Real.log 193) ≤ (2359537927873 / 125000000000000 : ℝ) := by
  have hc := thL_193_cos_r
  have hs := thL_193_sin_r
  rw [thL_193_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_193 : (999821646622583 / 1000000000000000 : ℝ) ≤ cCG cZ 193 ∧ cCG cZ 193 ≤ (999822013731643 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_193_cos

theorem sCB_193 : (4718984078481 / 250000000000000 : ℝ) ≤ sCG cZ 193 ∧ sCG cZ 193 ≤ (2359537927873 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_193_sin

theorem thL_194_r_bounds : (-63872622968821679661 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 ≤ (-63872586231178320339 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_194
  have hl : (930843495560227663 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 194 ∧ 17670246 / 100000 * Real.log 194 ≤ (116355436990882739 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_194_eq : (17670246 / 100000 * Real.log 194) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 + π / 2) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_194_cos_r : (802855722617891 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) ≤ (50178505625247 / 62500000000000 : ℝ) := by
  have hr := thL_194_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(319363023 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) (-(319363023 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 - (-(319363023 / 500000000 : ℝ))| ≤ (18368821679661 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 - (-(319363023 / 500000000 : ℝ)))]

theorem thL_194_sin_r : (-298086653808069 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) ≤ (-596172940239231 / 1000000000000000 : ℝ) := by
  have hr := thL_194_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (319363023 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((266414864755289659350380504777515802915724792354332147431438806921666851797422483297063378292937944430056785903947285283 / 446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(319363023 / 500000000 : ℝ)) ∧ Real.sin (-(319363023 / 500000000 : ℝ)) ≤ -((20493451135006024034596263975040280723551026683340334663343755173339346449923465105846170863954524919 / 34375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593) (-(319363023 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 - (-(319363023 / 500000000 : ℝ))| ≤ (18368821679661 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 194) 593 - (-(319363023 / 500000000 : ℝ)))]

theorem thL_194_cos : (596172940239231 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 194) ∧ Real.cos (17670246 / 100000 * Real.log 194) ≤ (298086653808069 / 500000000000000 : ℝ) := by
  have hc := thL_194_cos_r
  have hs := thL_194_sin_r
  rw [thL_194_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_194_sin : (802855722617891 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 194) ∧ Real.sin (17670246 / 100000 * Real.log 194) ≤ (50178505625247 / 62500000000000 : ℝ) := by
  have hc := thL_194_cos_r
  have hs := thL_194_sin_r
  rw [thL_194_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_194 : (596172940239231 / 1000000000000000 : ℝ) ≤ cCG cZ 194 ∧ cCG cZ 194 ≤ (298086653808069 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_194_cos

theorem sCB_194 : (802855722617891 / 1000000000000000 : ℝ) ≤ sCG cZ 194 ∧ sCG cZ 194 ≤ (50178505625247 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_194_sin

theorem thL_196_r_bounds : (-19858687271302258869 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 ≤ (-19858668928697741131 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_196
  have hl : (233163961092690097 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 196 ∧ 17670246 / 100000 * Real.log 196 ≤ (932655844737594637 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_196_eq : (17670246 / 100000 * Real.log 196) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 + π) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_196_cos_r : (922157796850541 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) ≤ (115269770462833 / 125000000000000 : ℝ) := by
  have hr := thL_196_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(198586781 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) (-(198586781 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 - (-(198586781 / 500000000 : ℝ))| ≤ (9171302258869 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 - (-(198586781 / 500000000 : ℝ)))]

theorem thL_196_sin_r : (-386813651924943 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) ≤ (-7736265701457 / 20000000000000 : ℝ) := by
  have hr := thL_196_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (198586781 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((294030214118991336073308975257643769665200533310257985099042875418446594071613529137945621172403104053678713416496358635341 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(198586781 / 500000000 : ℝ)) ∧ Real.sin (-(198586781 / 500000000 : ℝ)) ≤ -((7539236259461297154236522635396912270647773425581362336708361403655897364486226595448076653741259803419 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594) (-(198586781 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 - (-(198586781 / 500000000 : ℝ))| ≤ (9171302258869 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 196) 594 - (-(198586781 / 500000000 : ℝ)))]

theorem thL_196_cos : (-115269770462833 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 196) ∧ Real.cos (17670246 / 100000 * Real.log 196) ≤ (-922157796850541 / 1000000000000000 : ℝ) := by
  have hc := thL_196_cos_r
  have hs := thL_196_sin_r
  rw [thL_196_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_196_sin : (7736265701457 / 20000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 196) ∧ Real.sin (17670246 / 100000 * Real.log 196) ≤ (386813651924943 / 1000000000000000 : ℝ) := by
  have hc := thL_196_cos_r
  have hs := thL_196_sin_r
  rw [thL_196_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_196 : (-115269770462833 / 125000000000000 : ℝ) ≤ cCG cZ 196 ∧ cCG cZ 196 ≤ (-922157796850541 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_196_cos

theorem sCB_196 : (7736265701457 / 20000000000000 : ℝ) ≤ sCG cZ 196 ∧ sCG cZ 196 ≤ (386813651924943 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_196_sin

theorem thL_197_r_bounds : (25103867774639591131 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 ≤ (25103886125360408869 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_197
  have hl : (933555095471841551 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 197 ∧ 17670246 / 100000 * Real.log 197 ≤ (4667775479193379 / 5000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_197_eq : (17670246 / 100000 * Real.log 197) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 + π) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_197_cos_r : (701267567959 / 800000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) ≤ (876584826963703 / 1000000000000000 : ℝ) := by
  have hr := thL_197_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (502077539 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) (502077539 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 - (502077539 / 1000000000 : ℝ)| ≤ (9175360408869 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 - (502077539 / 1000000000 : ℝ))]

theorem thL_197_sin_r : (48124753114319 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) ≤ (120311974539407 / 250000000000000 : ℝ) := by
  have hr := thL_197_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (502077539 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594) (502077539 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 - (502077539 / 1000000000 : ℝ)| ≤ (9175360408869 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 197) 594 - (502077539 / 1000000000 : ℝ))]

theorem thL_197_cos : (-876584826963703 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 197) ∧ Real.cos (17670246 / 100000 * Real.log 197) ≤ (-701267567959 / 800000000000 : ℝ) := by
  have hc := thL_197_cos_r
  have hs := thL_197_sin_r
  rw [thL_197_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_197_sin : (-120311974539407 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 197) ∧ Real.sin (17670246 / 100000 * Real.log 197) ≤ (-48124753114319 / 100000000000000 : ℝ) := by
  have hc := thL_197_cos_r
  have hs := thL_197_sin_r
  rw [thL_197_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_197 : (-876584826963703 / 1000000000000000 : ℝ) ≤ cCG cZ 197 ∧ cCG cZ 197 ≤ (-701267567959 / 800000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_197_cos

theorem sCB_197 : (-120311974539407 / 250000000000000 : ℝ) ≤ sCG cZ 197 ∧ sCG cZ 197 ≤ (-48124753114319 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_197_sin

theorem thL_198_r_bounds : (-6960842387092697793 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 ≤ (-6960827692907302207 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_198
  have hl : (934449793383286171 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 198 ∧ 17670246 / 100000 * Real.log 198 ≤ (46722489687506021 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_198_eq : (17670246 / 100000 * Real.log 198) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 + π + π / 2) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_198_cos_r : (492448178317917 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) ≤ (98489672399047 / 100000000000000 : ℝ) := by
  have hr := thL_198_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(43505219 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) (-(43505219 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 - (-(43505219 / 250000000 : ℝ))| ≤ (7347092697793 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 - (-(43505219 / 250000000 : ℝ)))]

theorem thL_198_sin_r : (-173144068579971 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) ≤ (-34628740245067 / 200000000000000 : ℝ) := by
  have hr := thL_198_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (43505219 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((16065993497991983269048125894746917467906891042835726346997230271577392974640065555913389429864982738168500511125520659 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(43505219 / 250000000 : ℝ)) ∧ Real.sin (-(43505219 / 250000000 : ℝ)) ≤ -((1647794204922254694056214415964962581524494726236560270426935230014541193861359694300451091967584581 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595) (-(43505219 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 - (-(43505219 / 250000000 : ℝ))| ≤ (7347092697793 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 198) 595 - (-(43505219 / 250000000 : ℝ)))]

theorem thL_198_cos : (-173144068579971 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 198) ∧ Real.cos (17670246 / 100000 * Real.log 198) ≤ (-34628740245067 / 200000000000000 : ℝ) := by
  have hc := thL_198_cos_r
  have hs := thL_198_sin_r
  rw [thL_198_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_198_sin : (-98489672399047 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 198) ∧ Real.sin (17670246 / 100000 * Real.log 198) ≤ (-492448178317917 / 500000000000000 : ℝ) := by
  have hc := thL_198_cos_r
  have hs := thL_198_sin_r
  rw [thL_198_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_198 : (-173144068579971 / 1000000000000000 : ℝ) ≤ cCG cZ 198 ∧ cCG cZ 198 ≤ (-34628740245067 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_198_cos

theorem sCB_198 : (-98489672399047 / 100000000000000 : ℝ) ≤ sCG cZ 198 ∧ sCG cZ 198 ≤ (-492448178317917 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_198_sin

theorem thL_199_r_bounds : (28646781535577062207 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 ≤ (28646796224422937793 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_199
  have hl : (187067996796270583 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 199 ∧ 17670246 / 100000 * Real.log 199 ≤ (233834996087046791 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_199_eq : (17670246 / 100000 * Real.log 199) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 + π + π / 2) + ((148 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_199_cos_r : (754325651044131 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) ≤ (150865203660657 / 200000000000000 : ℝ) := by
  have hr := thL_199_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (358084861 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) (358084861 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 - (358084861 / 500000000 : ℝ)| ≤ (7344422937793 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 - (358084861 / 500000000 : ℝ))]

theorem thL_199_sin_r : (82062504191911 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) ≤ (656500400758529 / 1000000000000000 : ℝ) := by
  have hr := thL_199_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (358084861 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595) (358084861 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 - (358084861 / 500000000 : ℝ)| ≤ (7344422937793 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 199) 595 - (358084861 / 500000000 : ℝ))]

theorem thL_199_cos : (82062504191911 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 199) ∧ Real.cos (17670246 / 100000 * Real.log 199) ≤ (656500400758529 / 1000000000000000 : ℝ) := by
  have hc := thL_199_cos_r
  have hs := thL_199_sin_r
  rw [thL_199_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_199_sin : (-150865203660657 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 199) ∧ Real.sin (17670246 / 100000 * Real.log 199) ≤ (-754325651044131 / 1000000000000000 : ℝ) := by
  have hc := thL_199_cos_r
  have hs := thL_199_sin_r
  rw [thL_199_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_199 : (82062504191911 / 125000000000000 : ℝ) ≤ cCG cZ 199 ∧ cCG cZ 199 ≤ (656500400758529 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_199_cos

theorem sCB_199 : (-150865203660657 / 200000000000000 : ℝ) ≤ sCG cZ 199 ∧ sCG cZ 199 ≤ (-754325651044131 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_199_sin

theorem thL_201_r_bounds : (-131676757954896936659 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 ≤ (-131676684445103063341 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_201
  have hl : (937107023306778797 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 201 ∧ 17670246 / 100000 * Real.log 201 ≤ (468553511836806523 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_201_eq : (17670246 / 100000 * Real.log 201) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 + π / 2) + ((149 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_201_cos_r : (98872756707567 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) ≤ (158196484244671 / 200000000000000 : ℝ) := by
  have hr := thL_201_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(329191803 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) (-(329191803 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 - (-(329191803 / 500000000 : ℝ))| ≤ (36754896936659 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 - (-(329191803 / 500000000 : ℝ)))]

theorem thL_201_sin_r : (-611839296646843 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) ≤ (-611838929097171 / 1000000000000000 : ℝ) := by
  have hr := thL_201_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (329191803 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1913909224953843037403846272095155281426836812200363993638913709976355802512989430019662492128625148781597143950828952361 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(329191803 / 500000000 : ℝ)) ∧ Real.sin (-(329191803 / 500000000 : ℝ)) ≤ -((147223786534742235874433221662156142597973488719649714440279030218972534179107528246608037910068353613 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597) (-(329191803 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 - (-(329191803 / 500000000 : ℝ))| ≤ (36754896936659 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 201) 597 - (-(329191803 / 500000000 : ℝ)))]

theorem thL_201_cos : (611838929097171 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 201) ∧ Real.cos (17670246 / 100000 * Real.log 201) ≤ (611839296646843 / 1000000000000000 : ℝ) := by
  have hc := thL_201_cos_r
  have hs := thL_201_sin_r
  rw [thL_201_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_201_sin : (98872756707567 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 201) ∧ Real.sin (17670246 / 100000 * Real.log 201) ≤ (158196484244671 / 200000000000000 : ℝ) := by
  have hc := thL_201_cos_r
  have hs := thL_201_sin_r
  rw [thL_201_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_201 : (611838929097171 / 1000000000000000 : ℝ) ≤ cCG cZ 201 ∧ cCG cZ 201 ≤ (611839296646843 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_201_cos

theorem sCB_201 : (98872756707567 / 125000000000000 : ℝ) ≤ sCG cZ 201 ∧ sCG cZ 201 ≤ (158196484244671 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_201_sin

theorem thL_202_r_bounds : (43710659088298463341 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 ≤ (43710732511701536659 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_202
  have hl : (468991980195997387 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 202 ∧ 17670246 / 100000 * Real.log 202 ≤ (937983960758829023 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_202_eq : (17670246 / 100000 * Real.log 202) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 + π / 2) + ((149 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_202_cos_r : (976211918399661 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) ≤ (976212285516677 / 1000000000000000 : ℝ) := by
  have hr := thL_202_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (218553479 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) (218553479 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 - (218553479 / 1000000000 : ℝ)| ≤ (36711701536659 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 - (218553479 / 1000000000 : ℝ))]

theorem thL_202_sin_r : (216817555546053 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) ≤ (216817922663069 / 1000000000000000 : ℝ) := by
  have hr := thL_202_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (218553479 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597) (218553479 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 - (218553479 / 1000000000 : ℝ)| ≤ (36711701536659 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 202) 597 - (218553479 / 1000000000 : ℝ))]

theorem thL_202_cos : (-216817922663069 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 202) ∧ Real.cos (17670246 / 100000 * Real.log 202) ≤ (-216817555546053 / 1000000000000000 : ℝ) := by
  have hc := thL_202_cos_r
  have hs := thL_202_sin_r
  rw [thL_202_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_202_sin : (976211918399661 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 202) ∧ Real.sin (17670246 / 100000 * Real.log 202) ≤ (976212285516677 / 1000000000000000 : ℝ) := by
  have hc := thL_202_cos_r
  have hs := thL_202_sin_r
  rw [thL_202_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_202 : (-216817922663069 / 1000000000000000 : ℝ) ≤ cCG cZ 202 ∧ cCG cZ 202 ≤ (-216817555546053 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_202_cos

theorem sCB_202 : (976211918399661 / 1000000000000000 : ℝ) ≤ sCG cZ 202 ∧ sCG cZ 202 ≤ (976212285516677 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_202_sin

theorem thL_203_r_bounds : (-23981825877231085023 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 ≤ (-23981807522768914977 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_203
  have hl : (18777131338121171 / 20000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 203 ∧ 17670246 / 100000 * Real.log 203 ≤ (293392677272779 / 312500000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_203_eq : (17670246 / 100000 * Real.log 203) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 + π) + ((149 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_203_cos_r : (887162613962453 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) ≤ (443581490526003 / 500000000000000 : ℝ) := by
  have hr := thL_203_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(239818167 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) (-(239818167 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 - (-(239818167 / 500000000 : ℝ))| ≤ (9177231085023 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 - (-(239818167 / 500000000 : ℝ)))]

theorem thL_203_sin_r : (-461456758661797 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) ≤ (-461456391572541 / 1000000000000000 : ℝ) := by
  have hr := thL_203_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (239818167 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1443493849038411829531807252810485961417442160538350732891545157016804418056315003537826406070548359050190068239248256909 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(239818167 / 500000000 : ℝ)) ∧ Real.sin (-(239818167 / 500000000 : ℝ)) ≤ -((111037988387567393361620023560292675690770524858572189233870566225545755668812452192253339620511400457 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598) (-(239818167 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 - (-(239818167 / 500000000 : ℝ))| ≤ (9177231085023 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 203) 598 - (-(239818167 / 500000000 : ℝ)))]

theorem thL_203_cos : (-443581490526003 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 203) ∧ Real.cos (17670246 / 100000 * Real.log 203) ≤ (-887162613962453 / 1000000000000000 : ℝ) := by
  have hc := thL_203_cos_r
  have hs := thL_203_sin_r
  rw [thL_203_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_203_sin : (461456391572541 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 203) ∧ Real.sin (17670246 / 100000 * Real.log 203) ≤ (461456758661797 / 1000000000000000 : ℝ) := by
  have hc := thL_203_cos_r
  have hs := thL_203_sin_r
  rw [thL_203_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_203 : (-443581490526003 / 500000000000000 : ℝ) ≤ cCG cZ 203 ∧ cCG cZ 203 ≤ (-887162613962453 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_203_cos

theorem sCB_203 : (461456391572541 / 1000000000000000 : ℝ) ≤ sCG cZ 203 ∧ sCG cZ 203 ≤ (461456758661797 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_203_sin

theorem thL_204_r_bounds : (19434099319487514977 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 ≤ (19434117680512485023 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_204
  have hl : (939724885410124179 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 204 ∧ 17670246 / 100000 * Real.log 204 ≤ (234931221444239607 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_204_eq : (17670246 / 100000 * Real.log 204) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 + π) + ((149 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_204_cos_r : (231352274166899 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) ≤ (925409463888121 / 1000000000000000 : ℝ) := by
  have hr := thL_204_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (38868217 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) (38868217 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 - (38868217 / 100000000 : ℝ)| ≤ (9180512485023 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 - (38868217 / 100000000 : ℝ))]

theorem thL_204_sin_r : (189484514413687 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) ≤ (3031755168383 / 8000000000000 : ℝ) := by
  have hr := thL_204_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (38868217 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598) (38868217 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 - (38868217 / 100000000 : ℝ)| ≤ (9180512485023 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 204) 598 - (38868217 / 100000000 : ℝ))]

theorem thL_204_cos : (-925409463888121 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 204) ∧ Real.cos (17670246 / 100000 * Real.log 204) ≤ (-231352274166899 / 250000000000000 : ℝ) := by
  have hc := thL_204_cos_r
  have hs := thL_204_sin_r
  rw [thL_204_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_204_sin : (-3031755168383 / 8000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 204) ∧ Real.sin (17670246 / 100000 * Real.log 204) ≤ (-189484514413687 / 500000000000000 : ℝ) := by
  have hc := thL_204_cos_r
  have hs := thL_204_sin_r
  rw [thL_204_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_204 : (-925409463888121 / 1000000000000000 : ℝ) ≤ cCG cZ 204 ∧ cCG cZ 204 ≤ (-231352274166899 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_204_cos

theorem sCB_204 : (-3031755168383 / 8000000000000 : ℝ) ≤ sCG cZ 204 ∧ sCG cZ 204 ≤ (-189484514413687 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_204_sin

theorem thL_206_r_bounds : (54182577214833991877 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 ≤ (54182613985166008123 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_206
  have hl : (188289765104632097 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 206 ∧ 17670246 / 100000 * Real.log 206 ≤ (188289765177998947 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_206_eq : (17670246 / 100000 * Real.log 206) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 + π + π / 2) + ((149 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_206_cos_r : (856768278484299 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) ≤ (856768646188957 / 1000000000000000 : ℝ) := by
  have hr := thL_206_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (135456489 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) (135456489 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 - (135456489 / 250000000 : ℝ)| ≤ (18385166008123 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 - (135456489 / 250000000 : ℝ))]

theorem thL_206_sin_r : (515701088150001 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) ≤ (257850727926689 / 500000000000000 : ℝ) := by
  have hr := thL_206_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (135456489 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599) (135456489 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 - (135456489 / 250000000 : ℝ)| ≤ (18385166008123 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 206) 599 - (135456489 / 250000000 : ℝ))]

theorem thL_206_cos : (515701088150001 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 206) ∧ Real.cos (17670246 / 100000 * Real.log 206) ≤ (257850727926689 / 500000000000000 : ℝ) := by
  have hc := thL_206_cos_r
  have hs := thL_206_sin_r
  rw [thL_206_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_206_sin : (-856768646188957 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 206) ∧ Real.sin (17670246 / 100000 * Real.log 206) ≤ (-856768278484299 / 1000000000000000 : ℝ) := by
  have hc := thL_206_cos_r
  have hs := thL_206_sin_r
  rw [thL_206_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_206 : (515701088150001 / 1000000000000000 : ℝ) ≤ cCG cZ 206 ∧ cCG cZ 206 ≤ (257850727926689 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_206_cos

theorem sCB_206 : (-856768646188957 / 1000000000000000 : ℝ) ≤ sCG cZ 206 ∧ sCG cZ 206 ≤ (-856768278484299 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_206_sin

theorem thL_207_r_bounds : (-86633448392355731 / 500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 ≤ (-86633264607644269 / 500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_207
  have hl : (471152264590444217 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 207 ∧ 17670246 / 100000 * Real.log 207 ≤ (942304529547722683 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_207_eq : (17670246 / 100000 * Real.log 207) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) + ((150 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_207_cos_r : (492513327570983 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) ≤ (98502702271139 / 100000000000000 : ℝ) := by
  have hr := thL_207_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(173266713 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) (-(173266713 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 - (-(173266713 / 1000000000 : ℝ))| ≤ (91892355731 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 - (-(173266713 / 1000000000 : ℝ)))]

theorem thL_207_sin_r : (-172401246989429 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) ≤ (-34480175884001 / 200000000000000 : ℝ) := by
  have hr := thL_207_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (173266713 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((631125812179828442962545153242717989162489966586909631241938224878062932890918643557402820265663867300897807042598716677253 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(173266713 / 1000000000 : ℝ)) ∧ Real.sin (-(173266713 / 1000000000 : ℝ)) ≤ -((84959243947284598081072923739004068311461897288234679565126476700512879935683683353707941813370112738823 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600) (-(173266713 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 - (-(173266713 / 1000000000 : ℝ))| ≤ (91892355731 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 207) 600 - (-(173266713 / 1000000000 : ℝ)))]

theorem thL_207_cos : (492513327570983 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 207) ∧ Real.cos (17670246 / 100000 * Real.log 207) ≤ (98502702271139 / 100000000000000 : ℝ) := by
  have hc := thL_207_cos_r
  have hs := thL_207_sin_r
  rw [thL_207_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_207_sin : (-172401246989429 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 207) ∧ Real.sin (17670246 / 100000 * Real.log 207) ≤ (-34480175884001 / 200000000000000 : ℝ) := by
  have hc := thL_207_cos_r
  have hs := thL_207_sin_r
  rw [thL_207_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_207 : (492513327570983 / 500000000000000 : ℝ) ≤ cCG cZ 207 ∧ cCG cZ 207 ≤ (98502702271139 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_207_cos

theorem sCB_207 : (-172401246989429 / 1000000000000000 : ℝ) ≤ sCG cZ 207 ∧ sCG cZ 207 ≤ (-34480175884001 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_207_sin

theorem thL_208_r_bounds : (339156436269242769 / 500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 ≤ (339156619730757231 / 500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_208
  have hl : (943156108949565237 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 208 ∧ 17670246 / 100000 * Real.log 208 ≤ (471578054658199743 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_208_eq : (17670246 / 100000 * Real.log 208) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) + ((150 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_208_cos_r : (389316083492727 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) ≤ (194658133482073 / 250000000000000 : ℝ) := by
  have hr := thL_208_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (21197283 / 31250000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) (21197283 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 - (21197283 / 31250000 : ℝ)| ≤ (91730757231 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 - (21197283 / 31250000 : ℝ))]

theorem thL_208_sin_r : (125496044968499 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) ≤ (313740295883279 / 500000000000000 : ℝ) := by
  have hr := thL_208_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (21197283 / 31250000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600) (21197283 / 31250000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 - (21197283 / 31250000 : ℝ)| ≤ (91730757231 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 208) 600 - (21197283 / 31250000 : ℝ))]

theorem thL_208_cos : (389316083492727 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 208) ∧ Real.cos (17670246 / 100000 * Real.log 208) ≤ (194658133482073 / 250000000000000 : ℝ) := by
  have hc := thL_208_cos_r
  have hs := thL_208_sin_r
  rw [thL_208_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_208_sin : (125496044968499 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 208) ∧ Real.sin (17670246 / 100000 * Real.log 208) ≤ (313740295883279 / 500000000000000 : ℝ) := by
  have hc := thL_208_cos_r
  have hs := thL_208_sin_r
  rw [thL_208_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_208 : (389316083492727 / 500000000000000 : ℝ) ≤ cCG cZ 208 ∧ cCG cZ 208 ≤ (194658133482073 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_208_cos

theorem sCB_208 : (125496044968499 / 200000000000000 : ℝ) ≤ sCG cZ 208 ∧ sCG cZ 208 ≤ (313740295883279 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_208_sin

theorem thL_209_r_bounds : (-8997603324928832047 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 ≤ (-8997529875071167953 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_209
  have hl : (7375028159274283 / 7812500000000 : ℝ) ≤ 17670246 / 100000 * Real.log 209 ∧ 17670246 / 100000 * Real.log 209 ≤ (944003604753942473 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_209_eq : (17670246 / 100000 * Real.log 209) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 + π / 2) + ((150 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_209_cos_r : (998988034479487 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) ≤ (124873550216097 / 125000000000000 : ℝ) := by
  have hr := thL_209_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(44987833 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) (-(44987833 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 - (-(44987833 / 1000000000 : ℝ))| ≤ (36724928832047 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 - (-(44987833 / 1000000000 : ℝ)))]

theorem thL_209_sin_r : (-2810802685999 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) ≤ (-8994495145339 / 200000000000000 : ℝ) := by
  have hr := thL_209_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (44987833 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((25458698655646044544759611277182575229145554049714146816842921945411430404454002453859742670084887130493001073944257785866283 / 566092800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(44987833 / 1000000000 : ℝ)) ∧ Real.sin (-(44987833 / 1000000000 : ℝ)) ≤ -((163196786254141311184356480744191947418672710617400534807311994661126046912885976464830824463094162884453 / 3628800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601) (-(44987833 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 - (-(44987833 / 1000000000 : ℝ))| ≤ (36724928832047 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 209) 601 - (-(44987833 / 1000000000 : ℝ)))]

theorem thL_209_cos : (8994495145339 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 209) ∧ Real.cos (17670246 / 100000 * Real.log 209) ≤ (2810802685999 / 62500000000000 : ℝ) := by
  have hc := thL_209_cos_r
  have hs := thL_209_sin_r
  rw [thL_209_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_209_sin : (998988034479487 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 209) ∧ Real.sin (17670246 / 100000 * Real.log 209) ≤ (124873550216097 / 125000000000000 : ℝ) := by
  have hc := thL_209_cos_r
  have hs := thL_209_sin_r
  rw [thL_209_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_209 : (8994495145339 / 200000000000000 : ℝ) ≤ cCG cZ 209 ∧ cCG cZ 209 ≤ (2810802685999 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_209_cos

theorem sCB_209 : (998988034479487 / 1000000000000000 : ℝ) ≤ sCG cZ 209 ∧ sCG cZ 209 ≤ (124873550216097 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_209_sin

end PsiOmega.Locate.Z4

#print axioms PsiOmega.Locate.Z4.cCB_209
#print axioms PsiOmega.Locate.Z4.sCB_209
