import DHLocateExp

/-! # Generated (gen_locate.py): bounds for `cC n = cos(t log n)`, `sC n = sin(t log n)`, `t = 856993/10000`, `n ∈ NS`

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate

theorem thL_2_r_bounds : (-28803225600456253093 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 ≤ (-28803223799543746907 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_2
  have hl : (59402228162201509 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 2 ∧ 856993 / 10000 * Real.log 2 ≤ (5940222817934137 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_2_eq : (856993 / 10000 * Real.log 2) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 + π) + ((9 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_2_cos_r : (958804694309421 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) ≤ (239701178079637 / 250000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(288032247 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) (-(288032247 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 - (-(288032247 / 1000000000 : ℝ))| ≤ (900456253093 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 - (-(288032247 / 1000000000 : ℝ)))]

theorem thL_2_sin_r : (-28406609445473 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) ≤ (-71016519111401 / 250000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (288032247 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7279363879311798847895143861577110717783568484587866256844537466309070034198213239431619293018870720934704646867128761018189 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(288032247 / 1000000000 : ℝ)) ∧ Real.sin (-(288032247 / 1000000000 : ℝ)) ≤ -((139987766909842278104117466263450332240205675539282787488853561603381781793642342089805140750205939076937 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38) (-(288032247 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 - (-(288032247 / 1000000000 : ℝ))| ≤ (900456253093 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 2) 38 - (-(288032247 / 1000000000 : ℝ)))]

theorem thL_2_cos : (-239701178079637 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 2) ∧ Real.cos (856993 / 10000 * Real.log 2) ≤ (-958804694309421 / 1000000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_2_sin : (71016519111401 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 2) ∧ Real.sin (856993 / 10000 * Real.log 2) ≤ (28406609445473 / 100000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_2 : (-239701178079637 / 250000000000000 : ℝ) ≤ cC 2 ∧ cC 2 ≤ (-958804694309421 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_2_cos

theorem sCB_2 : (71016519111401 / 250000000000000 : ℝ) ≤ sC 2 ∧ sC 2 ≤ (28406609445473 / 100000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_2_sin

theorem thL_3_r_bounds : (-974755065864071541 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 ≤ (-974754834135928459 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_3
  have hl : (9415030410110739 / 100000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 3 ∧ 856993 / 10000 * Real.log 3 ≤ (11768788015512207 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_3_eq : (856993 / 10000 * Real.log 3) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) + ((15 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_3_cos_r : (248813253185471 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) ≤ (9952530359147 / 10000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(19495099 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) (-(19495099 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 - (-(19495099 / 200000000 : ℝ))| ≤ (115864071541 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 - (-(19495099 / 200000000 : ℝ)))]

theorem thL_3_sin_r : (-48660609892897 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) ≤ (-48660598306489 / 500000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (19495099 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((38188658230426899594573435756763355854983747706747634289035230007015549525538611256155475824033748787616089620512023 / 392398110720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(19495099 / 200000000 : ℝ)) ∧ Real.sin (-(19495099 / 200000000 : ℝ)) ≤ -((79559704646722707488685242265731410160799046644924455595265764446568117624273483990531940691103901 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60) (-(19495099 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 - (-(19495099 / 200000000 : ℝ))| ≤ (115864071541 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 3) 60 - (-(19495099 / 200000000 : ℝ)))]

theorem thL_3_cos : (248813253185471 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 3) ∧ Real.cos (856993 / 10000 * Real.log 3) ≤ (9952530359147 / 10000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_3_sin : (-48660609892897 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 3) ∧ Real.sin (856993 / 10000 * Real.log 3) ≤ (-48660598306489 / 500000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_3 : (248813253185471 / 250000000000000 : ℝ) ≤ cC 3 ∧ cC 3 ≤ (9952530359147 / 10000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_3_cos

theorem sCB_3 : (-48660609892897 / 500000000000000 : ℝ) ≤ sC 3 ∧ sC 3 ≤ (-48660598306489 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_3_sin

theorem thL_4_r_bounds : (-28803225188818703093 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 ≤ (-28803223911181296907 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_4
  have hl : (118804456332635769 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 4 ∧ 856993 / 10000 * Real.log 4 ≤ (118804456357431911 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_4_eq : (856993 / 10000 * Real.log 4) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) + ((19 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_4_cos_r : (838612907049063 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) ≤ (4193064663023 / 5000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(576064491 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) (-(576064491 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 - (-(576064491 / 1000000000 : ℝ))| ≤ (638818703093 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 - (-(576064491 / 1000000000 : ℝ)))]

theorem thL_4_sin_r : (-544727807823761 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) ≤ (-68090972783861 / 125000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (576064491 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((13958976584766300991438394156229198121497283559341968844062305192757386743076623861132755206871906740674507339022716007226297 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(576064491 / 1000000000 : ℝ)) ∧ Real.sin (-(576064491 / 1000000000 : ℝ)) ≤ -((268441857399291056519403327449531759299571223447264727636373982328372205103705691776012606674301881620989 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76) (-(576064491 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 - (-(576064491 / 1000000000 : ℝ))| ≤ (638818703093 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 4) 76 - (-(576064491 / 1000000000 : ℝ)))]

theorem thL_4_cos : (838612907049063 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 4) ∧ Real.cos (856993 / 10000 * Real.log 4) ≤ (4193064663023 / 5000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_4_sin : (-544727807823761 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 4) ∧ Real.sin (856993 / 10000 * Real.log 4) ≤ (-68090972783861 / 125000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_4 : (838612907049063 / 1000000000000000 : ℝ) ≤ cC 4 ∧ cC 4 ≤ (4193064663023 / 5000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_4_cos

theorem sCB_4 : (-544727807823761 / 1000000000000000 : ℝ) ≤ sC 4 ∧ sC 4 ≤ (-68090972783861 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_4_sin

theorem thL_6_r_bounds : (-38550775452685968503 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 ≤ (-38550772347314031497 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_6
  have hl : (153552532271373009 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 6 ∧ 856993 / 10000 * Real.log 6 ≤ (7677626615115251 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_6_eq : (856993 / 10000 * Real.log 6) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 + π) + ((24 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_6_cos_r : (11582595145877 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) ≤ (926607642723903 / 1000000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(385507739 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) (-(385507739 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 - (-(385507739 / 1000000000 : ℝ))| ≤ (1552685968503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 - (-(385507739 / 1000000000 : ℝ)))]

theorem thL_6_sin_r : (-188014837777093 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) ≤ (-75205928900093 / 200000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (385507739 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2341544514407086364506601974377429874409004058710139997315903352844842663919018113869600414585112042524732520213913631512871819 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(385507739 / 1000000000 : ℝ)) ∧ Real.sin (-(385507739 / 1000000000 : ℝ)) ≤ -((15009900733378732120850364168457982717335410347852529236159421869860519506286988929967991774186422702372861 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98) (-(385507739 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 - (-(385507739 / 1000000000 : ℝ))| ≤ (1552685968503 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 6) 98 - (-(385507739 / 1000000000 : ℝ)))]

theorem thL_6_cos : (-926607642723903 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 6) ∧ Real.cos (856993 / 10000 * Real.log 6) ≤ (-11582595145877 / 12500000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_6_sin : (75205928900093 / 200000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 6) ∧ Real.sin (856993 / 10000 * Real.log 6) ≤ (188014837777093 / 500000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_6 : (-926607642723903 / 1000000000000000 : ℝ) ≤ cC 6 ∧ cC 6 ≤ (-11582595145877 / 12500000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_6_cos

theorem sCB_6 : (75205928900093 / 200000000000000 : ℝ) ≤ sC 6 ∧ sC 6 ≤ (188014837777093 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_6_sin

theorem thL_7_r_bounds : (12936349307319781919 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 ≤ (12936350892680218081 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_7
  have hl : (41690784406771107 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 7 ∧ 856993 / 10000 * Real.log 7 ≤ (83381568829056323 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_7_eq : (856993 / 10000 * Real.log 7) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 + π) + ((26 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_7_cos_r : (96671644219199 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) ≤ (604197796187 / 625000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (129363501 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) (129363501 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 - (129363501 / 500000000 : ℝ)| ≤ (792680218081 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 - (129363501 / 500000000 : ℝ))]

theorem thL_7_sin_r : (63962528889717 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) ≤ (255850147266077 / 1000000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (129363501 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106) (129363501 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 - (129363501 / 500000000 : ℝ)| ≤ (792680218081 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 7) 106 - (129363501 / 500000000 : ℝ))]

theorem thL_7_cos : (-604197796187 / 625000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 7) ∧ Real.cos (856993 / 10000 * Real.log 7) ≤ (-96671644219199 / 100000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_7_sin : (-255850147266077 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 7) ∧ Real.sin (856993 / 10000 * Real.log 7) ≤ (-63962528889717 / 250000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_7 : (-604197796187 / 625000000000 : ℝ) ≤ cC 7 ∧ cC 7 ≤ (-96671644219199 / 100000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_7_cos

theorem sCB_7 : (-255850147266077 / 1000000000000000 : ℝ) ≤ sC 7 ∧ sC 7 ≤ (-63962528889717 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_7_sin

theorem thL_8_r_bounds : (70669957378273897299 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 ≤ (70669961021726102701 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_8
  have hl : (89103342251266993 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 8 ∧ 856993 / 10000 * Real.log 8 ≤ (178206684538040579 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_8_eq : (856993 / 10000 * Real.log 8) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 + π / 2) + ((28 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_8_cos_r : (380254520465049 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) ≤ (95063634674627 / 125000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (88337449 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) (88337449 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 - (88337449 / 125000000 : ℝ)| ≤ (1821726102701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 - (88337449 / 125000000 : ℝ))]

theorem thL_8_sin_r : (649327303634651 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) ≤ (129865468014187 / 200000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (88337449 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113) (88337449 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 - (88337449 / 125000000 : ℝ)| ≤ (1821726102701 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 8) 113 - (88337449 / 125000000 : ℝ))]

theorem thL_8_cos : (-129865468014187 / 200000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 8) ∧ Real.cos (856993 / 10000 * Real.log 8) ≤ (-649327303634651 / 1000000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_8_sin : (380254520465049 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 8) ∧ Real.sin (856993 / 10000 * Real.log 8) ≤ (95063634674627 / 125000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_8 : (-129865468014187 / 200000000000000 : ℝ) ≤ cC 8 ∧ cC 8 ≤ (-649327303634651 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_8_cos

theorem sCB_8 : (380254520465049 / 500000000000000 : ℝ) ≤ sC 8 ∧ sC 8 ≤ (95063634674627 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_8_sin

theorem thL_9_r_bounds : (-487377513923469231 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 ≤ (-487377421076530769 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_9
  have hl : (188300608210000041 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 9 ∧ 856993 / 10000 * Real.log 9 ≤ (94150304123478491 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_9_eq : (856993 / 10000 * Real.log 9) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) + ((30 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_9_cos_r : (981057146880991 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) ≤ (981057184019767 / 1000000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(194950987 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) (-(194950987 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 - (-(194950987 / 1000000000 : ℝ))| ≤ (46423469231 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 - (-(194950987 / 1000000000 : ℝ)))]

theorem thL_9_sin_r : (-96859234604831 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) ≤ (-38743686414177 / 200000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (194950987 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((15666088590659163969053762206349547459209587868084340310275246047169029318002275082481101705117345316006270138805793557428711 / 80870400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(194950987 / 1000000000 : ℝ)) ∧ Real.sin (-(194950987 / 1000000000 : ℝ)) ≤ -((100423644811917717701432634850847265798235731615520262446603621668827657727610383707147399105699216584481 / 518400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120) (-(194950987 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 - (-(194950987 / 1000000000 : ℝ))| ≤ (46423469231 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 9) 120 - (-(194950987 / 1000000000 : ℝ)))]

theorem thL_9_cos : (981057146880991 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 9) ∧ Real.cos (856993 / 10000 * Real.log 9) ≤ (981057184019767 / 1000000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_9_sin : (-96859234604831 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 9) ∧ Real.sin (856993 / 10000 * Real.log 9) ≤ (-38743686414177 / 200000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_9 : (981057146880991 / 1000000000000000 : ℝ) ≤ cC 9 ∧ cC 9 ≤ (981057184019767 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_9_cos

theorem sCB_9 : (-96859234604831 / 500000000000000 : ℝ) ≤ sC 9 ∧ sC 9 ≤ (-38743686414177 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_9_sin

theorem thL_11_r_bounds : (-27637246911079888087 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 ≤ (-27637243088920111913 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_11
  have hl : (102748973170768199 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 11 ∧ 856993 / 10000 * Real.log 11 ≤ (12843621648702641 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_11_eq : (856993 / 10000 * Real.log 11) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 + π + π / 2) + ((32 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_11_cos_r : (962051587619759 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) ≤ (481025812920679 / 500000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(5527449 / 20000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) (-(5527449 / 20000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 - (-(5527449 / 20000000 : ℝ))| ≤ (1911079888087 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 - (-(5527449 / 20000000 : ℝ)))]

theorem thL_11_sin_r : (-272867580369279 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) ≤ (-272867542147681 / 1000000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (5527449 / 20000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((81830999511453188754152900103581231148521556422639535583472472009003414576667134639647233144175628549 / 299892736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(5527449 / 20000000 : ℝ)) ∧ Real.sin (-(5527449 / 20000000 : ℝ)) ≤ -((27539278681739053018135089629969391321267203589671816108272997956403885348094445940871 / 100925440000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131) (-(5527449 / 20000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 - (-(5527449 / 20000000 : ℝ))| ≤ (1911079888087 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 11) 131 - (-(5527449 / 20000000 : ℝ)))]

theorem thL_11_cos : (-272867580369279 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 11) ∧ Real.cos (856993 / 10000 * Real.log 11) ≤ (-272867542147681 / 1000000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_11_sin : (-481025812920679 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 11) ∧ Real.sin (856993 / 10000 * Real.log 11) ≤ (-962051587619759 / 1000000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_11 : (-272867580369279 / 1000000000000000 : ℝ) ≤ cC 11 ∧ cC 11 ≤ (-272867542147681 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_11_cos

theorem sCB_11 : (-481025812920679 / 500000000000000 : ℝ) ≤ sC 11 ∧ sC 11 ≤ (-962051587619759 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_11_sin

theorem thL_12_r_bounds : (-8419250040855559809 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 ≤ (-8419249559144440191 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_12
  have hl : (212954760441573187 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 12 ∧ 856993 / 10000 * Real.log 12 ≤ (42590952095874877 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_12_eq : (856993 / 10000 * Real.log 12) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) + ((34 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_12_cos_r : (195404614876733 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) ≤ (781618498062021 / 1000000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(42096249 / 62500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) (-(42096249 / 62500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 - (-(42096249 / 62500000 : ℝ))| ≤ (240855559809 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 - (-(42096249 / 62500000 : ℝ)))]

theorem thL_12_sin_r : (-623756825731101 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) ≤ (-623756787193267 / 1000000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (42096249 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((273014814511182433094651801881558074095070984631749150754608101954238183998053265836627683274202864726618511 / 437694325228221714496612548828125000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(42096249 / 62500000 : ℝ)) ∧ Real.sin (-(42096249 / 62500000 : ℝ)) ≤ -((17472948128689264128295083096322293947065942758039343505164335104779347123580411692931108071 / 28012436814606189727783203125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136) (-(42096249 / 62500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 - (-(42096249 / 62500000 : ℝ))| ≤ (240855559809 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 12) 136 - (-(42096249 / 62500000 : ℝ)))]

theorem thL_12_cos : (195404614876733 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 12) ∧ Real.cos (856993 / 10000 * Real.log 12) ≤ (781618498062021 / 1000000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_12_sin : (-623756825731101 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 12) ∧ Real.sin (856993 / 10000 * Real.log 12) ≤ (-623756787193267 / 1000000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_12 : (195404614876733 / 250000000000000 : ℝ) ≤ cC 12 ∧ cC 12 ≤ (781618498062021 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_12_cos

theorem sCB_12 : (-623756825731101 / 1000000000000000 : ℝ) ≤ sC 12 ∧ sC 12 ≤ (-623756787193267 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_12_sin

theorem thL_13_r_bounds : (-971212919906386929 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 ≤ (-971212540093613071 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_13
  have hl : (27476795557411861 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 13 ∧ 856993 / 10000 * Real.log 13 ≤ (21981436449714109 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_13_eq : (856993 / 10000 * Real.log 13) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) + ((35 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_13_cos_r : (49764370810557 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) ≤ (497643727096209 / 500000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(97121273 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) (-(97121273 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 - (-(97121273 / 1000000000 : ℝ))| ≤ (189906386929 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 - (-(97121273 / 1000000000 : ℝ)))]

theorem thL_13_sin_r : (-96968680575011 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) ≤ (-96968642593733 / 1000000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (97121273 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((86260838947720824133883596074702432204445390463448437438449670146411298982988688402229381838898251339011528807939039766295519 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(97121273 / 1000000000 : ℝ)) ∧ Real.sin (-(97121273 / 1000000000 : ℝ)) ≤ -((3870678670731062621391774151884975220344120135013455497344609904884402134072370385842149774213641750044823 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140) (-(97121273 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 - (-(97121273 / 1000000000 : ℝ))| ≤ (189906386929 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 13) 140 - (-(97121273 / 1000000000 : ℝ)))]

theorem thL_13_cos : (49764370810557 / 50000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 13) ∧ Real.cos (856993 / 10000 * Real.log 13) ≤ (497643727096209 / 500000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_13_sin : (-96968680575011 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 13) ∧ Real.sin (856993 / 10000 * Real.log 13) ≤ (-96968642593733 / 1000000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_13 : (49764370810557 / 50000000000000 : ℝ) ≤ cC 13 ∧ cC 13 ≤ (497643727096209 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_13_cos

theorem sCB_13 : (-96968680575011 / 1000000000000000 : ℝ) ≤ sC 13 ∧ sC 13 ≤ (-96968642593733 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_13_sin

theorem thL_14_r_bounds : (-366315764740852123 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 ≤ (-366315285259147877 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_14
  have hl : (45233073159457169 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 14 ∧ 856993 / 10000 * Real.log 14 ≤ (113082682917577277 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_14_eq : (856993 / 10000 * Real.log 14) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) + ((36 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_14_cos_r : (999570612946039 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) ≤ (999570651304577 / 1000000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(14652621 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) (-(14652621 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 - (-(14652621 / 500000000 : ℝ))| ≤ (239740852123 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 - (-(14652621 / 500000000 : ℝ)))]

theorem thL_14_sin_r : (-732526670401 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) ≤ (-29301028457503 / 1000000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (14652621 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((91657339638774955030673501304756535864654708809396865540281839862840359417488175848420654267807496827579948686643830927 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(14652621 / 500000000 : ℝ)) ∧ Real.sin (-(14652621 / 500000000 : ℝ)) ≤ -((7050564587598073463897961638373118773809344212409431675468655601995709893120771224992839074058962459 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144) (-(14652621 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 - (-(14652621 / 500000000 : ℝ))| ≤ (239740852123 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 14) 144 - (-(14652621 / 500000000 : ℝ)))]

theorem thL_14_cos : (999570612946039 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 14) ∧ Real.cos (856993 / 10000 * Real.log 14) ≤ (999570651304577 / 1000000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_14_sin : (-732526670401 / 25000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 14) ∧ Real.sin (856993 / 10000 * Real.log 14) ≤ (-29301028457503 / 1000000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_14 : (999570612946039 / 1000000000000000 : ℝ) ≤ cC 14 ∧ cC 14 ≤ (999570651304577 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_14_cos

theorem sCB_14 : (-732526670401 / 25000000000000 : ℝ) ≤ sC 14 ∧ sC 14 ≤ (-29301028457503 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_14_sin

theorem thL_16_r_bounds : (41866732557195550373 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 ≤ (41866737042804449627 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_16
  have hl : (59402228168085147 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 16 ∧ 856993 / 10000 * Real.log 16 ≤ (118804456358228717 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_16_eq : (856993 / 10000 * Real.log 16) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 + π + π / 2) + ((37 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_16_cos_r : (182726301940287 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) ≤ (182726310911517 / 200000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (104666837 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) (104666837 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 - (104666837 / 250000000 : ℝ)| ≤ (2242804449627 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 - (104666837 / 250000000 : ℝ))]

theorem thL_16_sin_r : (406543239105863 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) ≤ (203271641980977 / 500000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (104666837 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151) (104666837 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 - (104666837 / 250000000 : ℝ)| ≤ (2242804449627 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 16) 151 - (104666837 / 250000000 : ℝ))]

theorem thL_16_cos : (406543239105863 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 16) ∧ Real.cos (856993 / 10000 * Real.log 16) ≤ (203271641980977 / 500000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_16_sin : (-182726310911517 / 200000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 16) ∧ Real.sin (856993 / 10000 * Real.log 16) ≤ (-182726301940287 / 200000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_16 : (406543239105863 / 1000000000000000 : ℝ) ≤ cC 16 ∧ cC 16 ≤ (203271641980977 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_16_cos

theorem sCB_16 : (-182726310911517 / 200000000000000 : ℝ) ≤ sC 16 ∧ sC 16 ≤ (-182726301940287 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_16_sin

theorem thL_17_r_bounds : (-13380606582642200387 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 ≤ (-13380605617357799613 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_17
  have hl : (242804400324198843 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 17 ∧ 856993 / 10000 * Real.log 17 ≤ (121402200186170543 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_17_eq : (856993 / 10000 * Real.log 17) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 + π + π / 2) + ((38 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_17_cos_r : (98052930015913 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) ≤ (784423488408313 / 1000000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(133806061 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) (-(133806061 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 - (-(133806061 / 200000000 : ℝ))| ≤ (482642200387 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 - (-(133806061 / 200000000 : ℝ)))]

theorem thL_17_sin_r : (-620225651378347 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) ≤ (-310112801556631 / 500000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (133806061 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3163879736570152875435575881934713889420907373023778298181948182135265984846900292322569200278993103236397837540095581 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(133806061 / 200000000 : ℝ)) ∧ Real.sin (-(133806061 / 200000000 : ℝ)) ≤ -((507032009065023308895999073340204586065058211429096973023801603917934676351912152283153958980695339 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155) (-(133806061 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 - (-(133806061 / 200000000 : ℝ))| ≤ (482642200387 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 17) 155 - (-(133806061 / 200000000 : ℝ)))]

theorem thL_17_cos : (-620225651378347 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 17) ∧ Real.cos (856993 / 10000 * Real.log 17) ≤ (-310112801556631 / 500000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_17_sin : (-784423488408313 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 17) ∧ Real.sin (856993 / 10000 * Real.log 17) ≤ (-98052930015913 / 125000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_17 : (-620225651378347 / 1000000000000000 : ℝ) ≤ cC 17 ∧ cC 17 ≤ (-310112801556631 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_17_cos

theorem sCB_17 : (-784423488408313 / 1000000000000000 : ℝ) ≤ sC 17 ∧ sC 17 ≤ (-98052930015913 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_17_sin

theorem thL_18_r_bounds : (-48298325458172483913 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 ≤ (-48298320341827516087 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_18
  have hl : (247702836379011941 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 18 ∧ 856993 / 10000 * Real.log 18 ≤ (12385141821491017 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_18_eq : (856993 / 10000 * Real.log 18) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 + π) + ((39 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_18_cos_r : (88561335924091 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) ≤ (885613410404697 / 1000000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(482983229 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) (-(482983229 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 - (-(482983229 / 1000000000 : ℝ))| ≤ (2558172483913 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 - (-(482983229 / 1000000000 : ℝ)))]

theorem thL_18_sin_r : (-29026453208661 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) ≤ (-464423200175113 / 1000000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (482983229 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2891973086791007734845285115011822411542359388199266291074870598011826032690398396730130202869273142194639297632272548009927789 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(482983229 / 1000000000 : ℝ)) ∧ Real.sin (-(482983229 / 1000000000 : ℝ)) ≤ -((18538289017890576348000123977411661739716620123472514147349210621571078517492363653697558221008648617638971 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158) (-(482983229 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 - (-(482983229 / 1000000000 : ℝ))| ≤ (2558172483913 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 18) 158 - (-(482983229 / 1000000000 : ℝ)))]

theorem thL_18_cos : (-885613410404697 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 18) ∧ Real.cos (856993 / 10000 * Real.log 18) ≤ (-88561335924091 / 100000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_18_sin : (464423200175113 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 18) ∧ Real.sin (856993 / 10000 * Real.log 18) ≤ (29026453208661 / 62500000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_18 : (-885613410404697 / 1000000000000000 : ℝ) ≤ cC 18 ∧ cC 18 ≤ (-88561335924091 / 100000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_18_cos

theorem sCB_18 : (464423200175113 / 1000000000000000 : ℝ) ≤ sC 18 ∧ sC 18 ≤ (29026453208661 / 62500000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_18_sin

theorem thL_19_r_bounds : (-112369843883348939367 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 ≤ (-112369833316651060633 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_19
  have hl : (252336359394561611 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 19 ∧ 856993 / 10000 * Real.log 19 ≤ (252336359447176821 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_19_eq : (856993 / 10000 * Real.log 19) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 + π / 2) + ((40 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_19_cos_r : (423135685377633 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) ≤ (846271423590823 / 1000000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(561849193 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) (-(561849193 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 - (-(561849193 / 1000000000 : ℝ))| ≤ (5283348939367 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 - (-(561849193 / 1000000000 : ℝ)))]

theorem thL_19_sin_r : (-266376026732977 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) ≤ (-266376000316187 / 500000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (561849193 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((473922564811083796789444120428815370428081885661640829201753124012308893697580081799969594040374747004577979437578840635655599 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(561849193 / 1000000000 : ℝ)) ∧ Real.sin (-(561849193 / 1000000000 : ℝ)) ≤ -((21265756113314298720725844736857377130570928008549084614848051450123196522197906955889159763661884948767943 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161) (-(561849193 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 - (-(561849193 / 1000000000 : ℝ))| ≤ (5283348939367 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 19) 161 - (-(561849193 / 1000000000 : ℝ)))]

theorem thL_19_cos : (266376000316187 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 19) ∧ Real.cos (856993 / 10000 * Real.log 19) ≤ (266376026732977 / 500000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_19_sin : (423135685377633 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 19) ∧ Real.sin (856993 / 10000 * Real.log 19) ≤ (846271423590823 / 1000000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_19 : (266376000316187 / 500000000000000 : ℝ) ≤ cC 19 ∧ cC 19 ≤ (266376026732977 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_19_cos

theorem sCB_19 : (423135685377633 / 500000000000000 : ℝ) ≤ sC 19 ∧ sC 19 ≤ (846271423590823 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_19_sin

theorem thL_21_r_bounds : (16125148621688520699 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 ≤ (16125154178311479301 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_21
  have hl : (65228360433542431 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 21 ∧ 856993 / 10000 * Real.log 21 ≤ (130456720894457667 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_21_eq : (856993 / 10000 * Real.log 21) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 + π) + ((41 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_21_cos_r : (15422298336529 / 15625000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) ≤ (493513574552043 / 500000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (80625757 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) (80625757 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 - (80625757 / 500000000 : ℝ)| ≤ (2778311479301 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 - (80625757 / 500000000 : ℝ))]

theorem thL_21_sin_r : (1605535825059 / 10000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) ≤ (160553638072131 / 1000000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (80625757 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166) (80625757 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 - (80625757 / 500000000 : ℝ)| ≤ (2778311479301 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 21) 166 - (80625757 / 500000000 : ℝ))]

theorem thL_21_cos : (-493513574552043 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 21) ∧ Real.cos (856993 / 10000 * Real.log 21) ≤ (-15422298336529 / 15625000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_21_sin : (-160553638072131 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 21) ∧ Real.sin (856993 / 10000 * Real.log 21) ≤ (-1605535825059 / 10000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_21 : (-493513574552043 / 500000000000000 : ℝ) ≤ cC 21 ∧ cC 21 ≤ (-15422298336529 / 15625000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_21_cos

theorem sCB_21 : (-160553638072131 / 1000000000000000 : ℝ) ≤ sC 21 ∧ sC 21 ≤ (-1605535825059 / 10000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_21_sin

theorem thL_22_r_bounds : (-56440471901796435013 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 ≤ (-56440466298203564987 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_22
  have hl : (13245008725498949 / 50000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 22 ∧ 856993 / 10000 * Real.log 22 ≤ (264900174565355493 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_22_eq : (856993 / 10000 * Real.log 22) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 + π / 2) + ((42 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_22_cos_r : (844907160580341 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) ≤ (211226804154613 / 250000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(564404691 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) (-(564404691 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 - (-(564404691 / 1000000000 : ℝ))| ≤ (2801796435013 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 - (-(564404691 / 1000000000 : ℝ)))]

theorem thL_22_sin_r : (-534912957989963 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) ≤ (-267456450976969 / 500000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (564404691 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1958209254041489919517074672672288621515425222288172373871300399236862993743464254630889653638712559828251746006536863060071 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(564404691 / 1000000000 : ℝ)) ∧ Real.sin (-(564404691 / 1000000000 : ℝ)) ≤ -((263605091890153892803301539863009250792997868475339112271470090299453076686351581636234936082333007094789 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169) (-(564404691 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 - (-(564404691 / 1000000000 : ℝ))| ≤ (2801796435013 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 22) 169 - (-(564404691 / 1000000000 : ℝ)))]

theorem thL_22_cos : (267456450976969 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 22) ∧ Real.cos (856993 / 10000 * Real.log 22) ≤ (534912957989963 / 1000000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_22_sin : (844907160580341 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 22) ∧ Real.sin (856993 / 10000 * Real.log 22) ≤ (211226804154613 / 250000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_22 : (267456450976969 / 500000000000000 : ℝ) ≤ cC 22 ∧ cC 22 ≤ (534912957989963 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_22_cos

theorem sCB_22 : (844907160580341 / 1000000000000000 : ℝ) ≤ sC 22 ∧ sC 22 ≤ (211226804154613 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_22_sin

theorem thL_23_r_bounds : (20697512814553222163 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 ≤ (20697523985446777837 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_23
  have hl : (33588707430750011 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 23 ∧ 856993 / 10000 * Real.log 23 ≤ (134354829750917759 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_23_eq : (856993 / 10000 * Real.log 23) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 + π + π / 2) + ((42 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_23_cos_r : (994649908571461 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) ≤ (99464996442593 / 100000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (12935949 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) (12935949 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 - (12935949 / 125000000 : ℝ)| ≤ (5585446777837 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 - (12935949 / 125000000 : ℝ))]

theorem thL_23_sin_r : (4132117724017 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) ≤ (51651499477447 / 500000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (12935949 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171) (12935949 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 - (12935949 / 125000000 : ℝ)| ≤ (5585446777837 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 23) 171 - (12935949 / 125000000 : ℝ))]

theorem thL_23_cos : (4132117724017 / 40000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 23) ∧ Real.cos (856993 / 10000 * Real.log 23) ≤ (51651499477447 / 500000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_23_sin : (-99464996442593 / 100000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 23) ∧ Real.sin (856993 / 10000 * Real.log 23) ≤ (-994649908571461 / 1000000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_23 : (4132117724017 / 40000000000000 : ℝ) ≤ cC 23 ∧ cC 23 ≤ (51651499477447 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_23_cos

theorem sCB_23 : (-99464996442593 / 100000000000000 : ℝ) ≤ sC 23 ∧ sC 23 ≤ (-994649908571461 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_23_sin

theorem thL_24_r_bounds : (60922407343075812679 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 ≤ (60922413056924187321 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_24
  have hl : (136178494304956229 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 24 ∧ 856993 / 10000 * Real.log 24 ≤ (272356988666086357 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_24_eq : (856993 / 10000 * Real.log 24) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 + π / 2) + ((43 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_24_cos_r : (205023057305363 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) ≤ (410046143182697 / 500000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (304612051 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) (304612051 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 - (304612051 / 500000000 : ℝ)| ≤ (2856924187321 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 - (304612051 / 500000000 : ℝ))]

theorem thL_24_sin_r : (4577850367191 / 8000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) ≤ (114446270607523 / 200000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (304612051 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173) (304612051 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 - (304612051 / 500000000 : ℝ)| ≤ (2856924187321 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 24) 173 - (304612051 / 500000000 : ℝ))]

theorem thL_24_cos : (-114446270607523 / 200000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 24) ∧ Real.cos (856993 / 10000 * Real.log 24) ≤ (-4577850367191 / 8000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_24_sin : (205023057305363 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 24) ∧ Real.sin (856993 / 10000 * Real.log 24) ≤ (410046143182697 / 500000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_24 : (-114446270607523 / 200000000000000 : ℝ) ≤ cC 24 ∧ cC 24 ≤ (-4577850367191 / 8000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_24_cos

theorem sCB_24 : (205023057305363 / 250000000000000 : ℝ) ≤ sC 24 ∧ sC 24 ≤ (410046143182697 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_24_sin

theorem thL_26_r_bounds : (-19257677135097038853 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 ≤ (-19257674264902961147 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_26
  have hl : (279216592627575751 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 26 ∧ 856993 / 10000 * Real.log 26 ≤ (279216592684193539 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_26_eq : (856993 / 10000 * Real.log 26) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 + π) + ((44 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_26_cos_r : (926740739465409 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) ≤ (463370398434657 / 500000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(192576757 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) (-(192576757 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 - (-(192576757 / 500000000 : ℝ))| ≤ (1435097038853 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 - (-(192576757 / 500000000 : ℝ)))]

theorem thL_26_sin_r : (-375701437558161 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) ≤ (-187850690077139 / 500000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (192576757 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40797650801077415032368026927180692200028013293170719386507720298163920673286575213824772261815686688870791676603336490451 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(192576757 / 500000000 : ℝ)) ∧ Real.sin (-(192576757 / 500000000 : ℝ)) ≤ -((7322655271988241133642962752671934236940215090502271015393448038431622517300732235230230670707497767507 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178) (-(192576757 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 - (-(192576757 / 500000000 : ℝ))| ≤ (1435097038853 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 26) 178 - (-(192576757 / 500000000 : ℝ)))]

theorem thL_26_cos : (-463370398434657 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 26) ∧ Real.cos (856993 / 10000 * Real.log 26) ≤ (-926740739465409 / 1000000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_26_sin : (187850690077139 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 26) ∧ Real.sin (856993 / 10000 * Real.log 26) ≤ (375701437558161 / 1000000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_26 : (-463370398434657 / 500000000000000 : ℝ) ≤ cC 26 ∧ cC 26 ≤ (-926740739465409 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_26_cos

theorem sCB_26 : (187850690077139 / 500000000000000 : ℝ) ≤ sC 26 ∧ sC 26 ≤ (375701437558161 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_26_sin

theorem thL_27_r_bounds : (-2924265056260874623 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 ≤ (-2924264483739125377 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_27
  have hl : (35306364039681913 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 27 ∧ 856993 / 10000 * Real.log 27 ≤ (5649018247484381 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_27_eq : (856993 / 10000 * Real.log 27) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) + ((45 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_27_cos_r : (9575471701019 / 10000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) ≤ (957547227354077 / 1000000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(292426477 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) (-(292426477 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 - (-(292426477 / 1000000000 : ℝ))| ≤ (286260874623 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 - (-(292426477 / 1000000000 : ℝ)))]

theorem thL_27_sin_r : (-288276566360571 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) ≤ (-57655301821679 / 200000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (292426477 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((256443428089230056849422375136617199184292044276832264156397695921274628468769051462014182756774069794147300206560189130116731 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(292426477 / 1000000000 : ℝ)) ∧ Real.sin (-(292426477 / 1000000000 : ℝ)) ≤ -((1643868128777115644323264001058651269251151976839932020046935752590395767596364576132100479676282393840061 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180) (-(292426477 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 - (-(292426477 / 1000000000 : ℝ))| ≤ (286260874623 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 27) 180 - (-(292426477 / 1000000000 : ℝ)))]

theorem thL_27_cos : (9575471701019 / 10000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 27) ∧ Real.cos (856993 / 10000 * Real.log 27) ≤ (957547227354077 / 1000000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_27_sin : (-288276566360571 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 27) ∧ Real.sin (856993 / 10000 * Real.log 27) ≤ (-57655301821679 / 200000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_27 : (9575471701019 / 10000000000000 : ℝ) ≤ cC 27 ∧ cC 27 ≤ (957547227354077 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_27_cos

theorem sCB_27 : (-288276566360571 / 1000000000000000 : ℝ) ≤ sC 27 ∧ sC 27 ≤ (-57655301821679 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_27_sin

theorem thL_28_r_bounds : (-15866875586872615007 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 ≤ (-15866872713127384993 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_28
  have hl : (285567593965532271 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 28 ∧ 856993 / 10000 * Real.log 28 ≤ (285567594022408637 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_28_eq : (856993 / 10000 * Real.log 28) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 + π) + ((45 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_28_cos_r : (190013912521857 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) ≤ (950069620084193 / 1000000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(317337483 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) (-(317337483 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 - (-(317337483 / 1000000000 : ℝ))| ≤ (1436872615007 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 - (-(317337483 / 1000000000 : ℝ)))]

theorem thL_28_sin_r : (-4875595655031 / 15625000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) ≤ (-156019032223539 / 500000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (317337483 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7996163360709516491195756548894418128225837948008904478662297607640711264762305100488010514573611624360589219188741714761241 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(317337483 / 1000000000 : ℝ)) ∧ Real.sin (-(317337483 / 1000000000 : ℝ)) ≤ -((153772372321336829407944536094427935276545941589578329264161743529579596688846920441517761816058719569693 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182) (-(317337483 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 - (-(317337483 / 1000000000 : ℝ))| ≤ (1436872615007 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 28) 182 - (-(317337483 / 1000000000 : ℝ)))]

theorem thL_28_cos : (-950069620084193 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 28) ∧ Real.cos (856993 / 10000 * Real.log 28) ≤ (-190013912521857 / 200000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_28_sin : (156019032223539 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 28) ∧ Real.sin (856993 / 10000 * Real.log 28) ≤ (4875595655031 / 15625000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_28 : (-950069620084193 / 1000000000000000 : ℝ) ≤ cC 28 ∧ cC 28 ≤ (-190013912521857 / 200000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_28_cos

theorem sCB_28 : (156019032223539 / 500000000000000 : ℝ) ≤ sC 28 ∧ sC 28 ≤ (4875595655031 / 15625000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_28_sin

theorem thL_29_r_bounds : (-11290715520981373481 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 ≤ (-11290714079018626519 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_29
  have hl : (288574895509421723 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 29 ∧ 856993 / 10000 * Real.log 29 ≤ (288574895566385793 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_29_eq : (856993 / 10000 * Real.log 29) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) + ((46 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_29_cos_r : (112467187288033 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) ≤ (35989502239317 / 40000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(28226787 / 62500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) (-(28226787 / 62500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 - (-(28226787 / 62500000 : ℝ))| ≤ (720981373481 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 - (-(28226787 / 62500000 : ℝ)))]

theorem thL_29_sin_r : (-54553930802193 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) ≤ (-109107847184757 / 250000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (28226787 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2483306212729230667438857393012505861645319266306276372514920214704871853539062222521312150832997707988097729 / 5690026227966882288455963134765625000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(28226787 / 62500000 : ℝ)) ∧ Real.sin (-(28226787 / 62500000 : ℝ)) ≤ -((12225507508820681606350739055221560011217006265023425215791139796764245980953688147390334677 / 28012436814606189727783203125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184) (-(28226787 / 62500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 - (-(28226787 / 62500000 : ℝ))| ≤ (720981373481 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 29) 184 - (-(28226787 / 62500000 : ℝ)))]

theorem thL_29_cos : (112467187288033 / 125000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 29) ∧ Real.cos (856993 / 10000 * Real.log 29) ≤ (35989502239317 / 40000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_29_sin : (-54553930802193 / 125000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 29) ∧ Real.sin (856993 / 10000 * Real.log 29) ≤ (-109107847184757 / 250000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_29 : (112467187288033 / 125000000000000 : ℝ) ≤ cC 29 ∧ cC 29 ≤ (35989502239317 / 40000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_29_cos

theorem sCB_29 : (-54553930802193 / 125000000000000 : ℝ) ≤ sC 29 ∧ sC 29 ≤ (-109107847184757 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_29_sin

theorem thL_31_r_bounds : (110277301866496240611 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 ≤ (110277313333503759389 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_31
  have hl : (294290299619978149 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 31 ∧ 856993 / 10000 * Real.log 31 ≤ (294290299677065663 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_31_eq : (856993 / 10000 * Real.log 31) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 + π + π / 2) + ((46 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_31_cos_r : (170359789686747 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) ≤ (851799005770423 / 1000000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (275693269 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) (275693269 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 - (275693269 / 500000000 : ℝ)| ≤ (5733503759389 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 - (275693269 / 500000000 : ℝ))]

theorem thL_31_sin_r : (104773751020061 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) ≤ (523868812435413 / 1000000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (275693269 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187) (275693269 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 - (275693269 / 500000000 : ℝ)| ≤ (5733503759389 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 31) 187 - (275693269 / 500000000 : ℝ))]

theorem thL_31_cos : (104773751020061 / 200000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 31) ∧ Real.cos (856993 / 10000 * Real.log 31) ≤ (523868812435413 / 1000000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_31_sin : (-851799005770423 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 31) ∧ Real.sin (856993 / 10000 * Real.log 31) ≤ (-170359789686747 / 200000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_31 : (104773751020061 / 200000000000000 : ℝ) ≤ cC 31 ∧ cC 31 ≤ (523868812435413 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_31_cos

theorem sCB_31 : (-851799005770423 / 1000000000000000 : ℝ) ≤ sC 31 ∧ sC 31 ≤ (-170359789686747 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_31_sin

theorem thL_32_r_bounds : (26127015441436592917 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 ≤ (26127026958563407083 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_32
  have hl : (74252785210360661 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 32 ∧ 856993 / 10000 * Real.log 32 ≤ (148505570449286841 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_32_eq : (856993 / 10000 * Real.log 32) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 + π / 2) + ((47 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_32_cos_r : (99147933352771 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) ≤ (198295878222669 / 200000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (65317553 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) (65317553 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 - (65317553 / 500000000 : ℝ)| ≤ (5758563407083 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 - (65317553 / 500000000 : ℝ))]

theorem thL_32_sin_r : (65131917274011 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) ≤ (130263892133657 / 1000000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (65317553 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189) (65317553 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 - (65317553 / 500000000 : ℝ)| ≤ (5758563407083 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 32) 189 - (65317553 / 500000000 : ℝ))]

theorem thL_32_cos : (-130263892133657 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 32) ∧ Real.cos (856993 / 10000 * Real.log 32) ≤ (-65131917274011 / 500000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_32_sin : (99147933352771 / 100000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 32) ∧ Real.sin (856993 / 10000 * Real.log 32) ≤ (198295878222669 / 200000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_32 : (-130263892133657 / 1000000000000000 : ℝ) ≤ cC 32 ∧ cC 32 ≤ (-65131917274011 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_32_cos

theorem sCB_32 : (99147933352771 / 100000000000000 : ℝ) ≤ sC 32 ∧ sC 32 ≤ (198295878222669 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_32_sin

theorem thL_33_r_bounds : (-74769593761576454777 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 ≤ (-74769582238423545223 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_33
  have hl : (74912062612254343 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 33 ∧ 856993 / 10000 * Real.log 33 ≤ (149824125253091691 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_33_eq : (856993 / 10000 * Real.log 33) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 + π + π / 2) + ((47 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_33_cos_r : (930928943436489 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) ≤ (93092900105227 / 100000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(18692397 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) (-(18692397 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 - (-(18692397 / 50000000 : ℝ))| ≤ (5761576454777 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 - (-(18692397 / 50000000 : ℝ)))]

theorem thL_33_sin_r : (-91300078613501 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) ≤ (-182600128419119 / 500000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (18692397 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((16319887764811057889914763952126941727802644139228887100388339146400827395690850113353832435316250275213977 / 44687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(18692397 / 50000000 : ℝ)) ∧ Real.sin (-(18692397 / 50000000 : ℝ)) ≤ -((878763187335978963524661637048881120601354355154114333134380255074193952740365774708046587 / 2406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191) (-(18692397 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 - (-(18692397 / 50000000 : ℝ))| ≤ (5761576454777 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 33) 191 - (-(18692397 / 50000000 : ℝ)))]

theorem thL_33_cos : (-91300078613501 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 33) ∧ Real.cos (856993 / 10000 * Real.log 33) ≤ (-182600128419119 / 500000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_33_sin : (-93092900105227 / 100000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 33) ∧ Real.sin (856993 / 10000 * Real.log 33) ≤ (-930928943436489 / 1000000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_33 : (-91300078613501 / 250000000000000 : ℝ) ≤ cC 33 ∧ cC 33 ≤ (-182600128419119 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_33_cos

theorem sCB_33 : (-93092900105227 / 100000000000000 : ℝ) ≤ sC 33 ∧ sC 33 ≤ (-930928943436489 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_33_sin

theorem thL_34_r_bounds : (1917917966395784709 / 3125000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 ≤ (1917918146104215291 / 3125000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_34
  have hl : (151103314246933401 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 34 ∧ 856993 / 10000 * Real.log 34 ≤ (151103314275530549 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_34_eq : (856993 / 10000 * Real.log 34) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) + ((48 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_34_cos_r : (817503320746549 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) ≤ (817503378259211 / 1000000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (306866889 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) (306866889 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 - (306866889 / 500000000 : ℝ)| ≤ (89854215291 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 - (306866889 / 500000000 : ℝ))]

theorem thL_34_sin_r : (575923814776673 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) ≤ (287961936141827 / 500000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (306866889 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192) (306866889 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 - (306866889 / 500000000 : ℝ)| ≤ (89854215291 / 3125000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 34) 192 - (306866889 / 500000000 : ℝ))]

theorem thL_34_cos : (817503320746549 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 34) ∧ Real.cos (856993 / 10000 * Real.log 34) ≤ (817503378259211 / 1000000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_34_sin : (575923814776673 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 34) ∧ Real.sin (856993 / 10000 * Real.log 34) ≤ (287961936141827 / 500000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_34 : (817503320746549 / 1000000000000000 : ℝ) ≤ cC 34 ∧ cC 34 ≤ (817503378259211 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_34_cos

theorem sCB_34 : (575923814776673 / 1000000000000000 : ℝ) ≤ sC 34 ∧ sC 34 ≤ (287961936141827 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_34_sin

theorem thL_36_r_bounds : (-38550775137250468503 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 ≤ (-38550772262749531497 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_36
  have hl : (38388133068631841 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 36 ∧ 856993 / 10000 * Real.log 36 ≤ (19194066537893181 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_36_eq : (856993 / 10000 * Real.log 36) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) + ((49 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_36_cos_r : (717203363510079 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) ≤ (717203421092233 / 1000000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(385507737 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) (-(385507737 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 - (-(385507737 / 500000000 : ℝ))| ≤ (1437250468503 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 - (-(385507737 / 500000000 : ℝ)))]

theorem thL_36_sin_r : (-348431963971737 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) ≤ (-69686387044799 / 100000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (385507737 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2179877384680195054319898688580636897103101886469174969318798259976233316445396350960592358034012687932169069518266150179 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(385507737 / 500000000 : ℝ)) ∧ Real.sin (-(385507737 / 500000000 : ℝ)) ≤ -((167682875743315525335456894377331383321993117583320134846244199433866274405630172458855061568624149127 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196) (-(385507737 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 - (-(385507737 / 500000000 : ℝ))| ≤ (1437250468503 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 36) 196 - (-(385507737 / 500000000 : ℝ)))]

theorem thL_36_cos : (717203363510079 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 36) ∧ Real.cos (856993 / 10000 * Real.log 36) ≤ (717203421092233 / 1000000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_36_sin : (-348431963971737 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 36) ∧ Real.sin (856993 / 10000 * Real.log 36) ≤ (-69686387044799 / 100000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_36 : (717203363510079 / 1000000000000000 : ℝ) ≤ cC 36 ∧ cC 36 ≤ (717203421092233 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_36_cos

theorem sCB_36 : (-348431963971737 / 500000000000000 : ℝ) ≤ sC 36 ∧ sC 36 ≤ (-69686387044799 / 100000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_36_sin

theorem thL_37_r_bounds : (1252215819470802141 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 ≤ (1252227380529197859 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_37
  have hl : (77363284364422997 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 37 ∧ 856993 / 10000 * Real.log 37 ≤ (309453137514943673 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_37_eq : (856993 / 10000 * Real.log 37) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 + π / 2) + ((49 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_37_cos_r : (999980370424691 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) ≤ (31249388382187 / 31250000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1565277 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) (1565277 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 - (1565277 / 250000000 : ℝ)| ≤ (5780529197859 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 - (1565277 / 250000000 : ℝ))]

theorem thL_37_sin_r : (6261038189991 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) ≤ (1565273998821 / 250000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1565277 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197) (1565277 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 - (1565277 / 250000000 : ℝ)| ≤ (5780529197859 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 37) 197 - (1565277 / 250000000 : ℝ))]

theorem thL_37_cos : (-1565273998821 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 37) ∧ Real.cos (856993 / 10000 * Real.log 37) ≤ (-6261038189991 / 1000000000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_37_sin : (999980370424691 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 37) ∧ Real.sin (856993 / 10000 * Real.log 37) ≤ (31249388382187 / 31250000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_37 : (-1565273998821 / 250000000000000 : ℝ) ≤ cC 37 ∧ cC 37 ≤ (-6261038189991 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_37_cos

theorem sCB_37 : (999980370424691 / 1000000000000000 : ℝ) ≤ sC 37 ∧ sC 37 ≤ (31249388382187 / 31250000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_37_sin

theorem thL_38_r_bounds : (36045742963329030377 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 ≤ (36045745836670969623 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_38
  have hl : (311738587564858421 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 38 ∧ 856993 / 10000 * Real.log 38 ≤ (6234771752442459 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_38_eq : (856993 / 10000 * Real.log 38) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 + π) + ((49 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_38_cos_r : (6009616981509 / 8000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) ≤ (150240436039321 / 200000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (90114361 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) (90114361 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 - (90114361 / 125000000 : ℝ)| ≤ (1436670969623 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 - (90114361 / 125000000 : ℝ))]

theorem thL_38_sin_r : (66007218522067 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) ≤ (660072242689791 / 1000000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (90114361 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198) (90114361 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 - (90114361 / 125000000 : ℝ)| ≤ (1436670969623 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 38) 198 - (90114361 / 125000000 : ℝ))]

theorem thL_38_cos : (-150240436039321 / 200000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 38) ∧ Real.cos (856993 / 10000 * Real.log 38) ≤ (-6009616981509 / 8000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_38_sin : (-660072242689791 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 38) ∧ Real.sin (856993 / 10000 * Real.log 38) ≤ (-66007218522067 / 100000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_38 : (-150240436039321 / 200000000000000 : ℝ) ≤ cC 38 ∧ cC 38 ≤ (-6009616981509 / 8000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_38_cos

theorem sCB_38 : (-660072242689791 / 1000000000000000 : ℝ) ≤ sC 38 ∧ sC 38 ≤ (-66007218522067 / 100000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_38_sin

theorem thL_39_r_bounds : (-97298396535869077 / 500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 ≤ (-97298367464130923 / 500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_39
  have hl : (313964668566775851 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 39 ∧ 856993 / 10000 * Real.log 39 ≤ (156982334312025531 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_39_eq : (856993 / 10000 * Real.log 39) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) + ((50 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_39_cos_r : (245281423589849 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) ≤ (981125752502873 / 1000000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(48649191 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) (-(48649191 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 - (-(48649191 / 250000000 : ℝ))| ≤ (14535869077 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 - (-(48649191 / 250000000 : ℝ)))]

theorem thL_39_sin_r : (-96685477276827 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) ≤ (-193370896410177 / 1000000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (48649191 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((73838919222792577168791220763220161929578961891674686177429369265751083688641685728097539977037380087672956823579997 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(48649191 / 250000000 : ℝ)) ∧ Real.sin (-(48649191 / 250000000 : ℝ)) ≤ -((22719667453166946810339895349853868666817338387806885796356098969065800768905873888524549344215289 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200) (-(48649191 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 - (-(48649191 / 250000000 : ℝ))| ≤ (14535869077 / 500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 39) 200 - (-(48649191 / 250000000 : ℝ)))]

theorem thL_39_cos : (245281423589849 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 39) ∧ Real.cos (856993 / 10000 * Real.log 39) ≤ (981125752502873 / 1000000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_39_sin : (-96685477276827 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 39) ∧ Real.sin (856993 / 10000 * Real.log 39) ≤ (-193370896410177 / 1000000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_39 : (245281423589849 / 250000000000000 : ℝ) ≤ cC 39 ∧ cC 39 ≤ (981125752502873 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_39_cos

theorem sCB_39 : (-96685477276827 / 500000000000000 : ℝ) ≤ sC 39 ∧ sC 39 ≤ (-193370896410177 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_39_sin

theorem thL_41_r_bounds : (-62112773665520029631 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 ≤ (-62112767934479970369 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_41
  have hl : (318250526602727583 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 41 ∧ 856993 / 10000 * Real.log 41 ≤ (159125263330009607 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_41_eq : (856993 / 10000 * Real.log 41) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 + π + π / 2) + ((50 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_41_cos_r : (406611336312827 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) ≤ (40661136497147 / 50000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(155281927 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) (-(155281927 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 - (-(155281927 / 250000000 : ℝ))| ≤ (2865520029631 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 - (-(155281927 / 250000000 : ℝ)))]

theorem thL_41_sin_r : (-11639052735721 / 20000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) ≤ (-581952579475319 / 1000000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (155281927 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((53999289802388040984779700979947243496943307138254378763615204142838948025582750444711331961422776404790033535621044967 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(155281927 / 250000000 : ℝ)) ∧ Real.sin (-(155281927 / 250000000 : ℝ)) ≤ -((5538388697677694551333052896469956886818916830951042088211319206029435685700181559755403558647510377 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203) (-(155281927 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 - (-(155281927 / 250000000 : ℝ))| ≤ (2865520029631 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 41) 203 - (-(155281927 / 250000000 : ℝ)))]

theorem thL_41_cos : (-11639052735721 / 20000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 41) ∧ Real.cos (856993 / 10000 * Real.log 41) ≤ (-581952579475319 / 1000000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_41_sin : (-40661136497147 / 50000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 41) ∧ Real.sin (856993 / 10000 * Real.log 41) ≤ (-406611336312827 / 500000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_41 : (-11639052735721 / 20000000000000 : ℝ) ≤ cC 41 ∧ cC 41 ≤ (-581952579475319 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_41_cos

theorem sCB_41 : (-40661136497147 / 50000000000000 : ℝ) ≤ sC 41 ∧ sC 41 ≤ (-406611336312827 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_41_sin

theorem thL_42_r_bounds : (-3169519047627441927 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 ≤ (-3169517602372558073 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_42
  have hl : (320315669904766061 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 42 ∧ 856993 / 10000 * Real.log 42 ≤ (40039458745258001 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_42_eq : (856993 / 10000 * Real.log 42) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) + ((51 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_42_cos_r : (247993513223901 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) ≤ (991974110705801 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(126780733 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) (-(126780733 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 - (-(126780733 / 1000000000 : ℝ))| ≤ (722627441927 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 - (-(126780733 / 1000000000 : ℝ)))]

theorem thL_42_sin_r : (-25288280562549 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) ≤ (-126441345002549 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (126780733 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((787353065303493248528698981496941099860170370517412289479430240916088459269163850409870915729203206687457389443435007673928813 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(126780733 / 1000000000 : ℝ)) ∧ Real.sin (-(126780733 / 1000000000 : ℝ)) ≤ -((5047135033996751593118671596593562794345414871430000463532011467639894537062439817266801868980490455245883 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204) (-(126780733 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 - (-(126780733 / 1000000000 : ℝ))| ≤ (722627441927 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 42) 204 - (-(126780733 / 1000000000 : ℝ)))]

theorem thL_42_cos : (247993513223901 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 42) ∧ Real.cos (856993 / 10000 * Real.log 42) ≤ (991974110705801 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_42_sin : (-25288280562549 / 200000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 42) ∧ Real.sin (856993 / 10000 * Real.log 42) ≤ (-126441345002549 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_42 : (247993513223901 / 250000000000000 : ℝ) ≤ cC 42 ∧ cC 42 ≤ (991974110705801 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_42_cos

theorem sCB_42 : (-25288280562549 / 200000000000000 : ℝ) ≤ sC 42 ∧ sC 42 ≤ (-126441345002549 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_42_sin

theorem thL_43_r_bounds : (6379401363595338843 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 ≤ (6379402516404661157 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_43
  have hl : (161166108530735373 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 43 ∧ 856993 / 10000 * Real.log 43 ≤ (8058305427969351 / 25000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_43_eq : (856993 / 10000 * Real.log 43) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 + π / 2) + ((51 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_43_cos_r : (949558858822361 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) ≤ (94955891646283 / 100000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (318970097 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) (318970097 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 - (318970097 / 1000000000 : ℝ)| ≤ (576404661157 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 - (318970097 / 1000000000 : ℝ))]

theorem thL_43_sin_r : (313588744733531 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) ≤ (313588802373999 / 1000000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (318970097 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205) (318970097 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 - (318970097 / 1000000000 : ℝ)| ≤ (576404661157 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 43) 205 - (318970097 / 1000000000 : ℝ))]

theorem thL_43_cos : (-313588802373999 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 43) ∧ Real.cos (856993 / 10000 * Real.log 43) ≤ (-313588744733531 / 1000000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_43_sin : (949558858822361 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 43) ∧ Real.sin (856993 / 10000 * Real.log 43) ≤ (94955891646283 / 100000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_43 : (-313588802373999 / 1000000000000000 : ℝ) ≤ cC 43 ∧ cC 43 ≤ (-313588744733531 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_43_cos

theorem sCB_43 : (949558858822361 / 1000000000000000 : ℝ) ≤ sC 43 ∧ sC 43 ≤ (94955891646283 / 100000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_43_sin

theorem thL_44_r_bounds : (71835936091531743759 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 ≤ (71835941908468256241 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_44
  have hl : (324302402680664021 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 44 ∧ 856993 / 10000 * Real.log 44 ≤ (16215120136898593 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_44_eq : (856993 / 10000 * Real.log 44) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 + π) + ((51 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_44_cos_r : (376443240418963 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) ≤ (188221634761679 / 250000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (71835939 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) (71835939 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 - (71835939 / 100000000 : ℝ)| ≤ (2908468256241 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 - (71835939 / 100000000 : ℝ))]

theorem thL_44_sin_r : (131630067208113 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) ≤ (658150394212109 / 1000000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (71835939 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206) (71835939 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 - (71835939 / 100000000 : ℝ)| ≤ (2908468256241 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 44) 206 - (71835939 / 100000000 : ℝ))]

theorem thL_44_cos : (-188221634761679 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 44) ∧ Real.cos (856993 / 10000 * Real.log 44) ≤ (-376443240418963 / 500000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_44_sin : (-658150394212109 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 44) ∧ Real.sin (856993 / 10000 * Real.log 44) ≤ (-131630067208113 / 200000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_44 : (-188221634761679 / 250000000000000 : ℝ) ≤ cC 44 ∧ cC 44 ≤ (-376443240418963 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_44_cos

theorem sCB_44 : (-658150394212109 / 1000000000000000 : ℝ) ≤ sC 44 ∧ sC 44 ≤ (-131630067208113 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_44_sin

theorem thL_46_r_bounds : (-18454468393129158093 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 ≤ (-18454462606870841907 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_46
  have hl : (164055943808374827 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 46 ∧ 856993 / 10000 * Real.log 46 ≤ (65622377534812937 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_46_eq : (856993 / 10000 * Real.log 46) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 + π / 2) + ((52 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_46_cos_r : (245754969732453 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) ≤ (983019936792397 / 1000000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(36908931 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) (-(36908931 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 - (-(36908931 / 200000000 : ℝ))| ≤ (2893129158093 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 - (-(36908931 / 200000000 : ℝ)))]

theorem thL_46_sin_r : (-91749484149053 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) ≤ (-183498910435521 / 1000000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (36908931 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3852099928586825376668746724530559669751089790829065795280809907812353457357020036313015342584858138902787112559137 / 20992491520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(36908931 / 200000000 : ℝ)) ∧ Real.sin (-(36908931 / 200000000 : ℝ)) ≤ -((1851971119512896815239426449803981157421868298389628492684875096256531387313487091833602776879349 / 10092544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209) (-(36908931 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 - (-(36908931 / 200000000 : ℝ))| ≤ (2893129158093 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 46) 209 - (-(36908931 / 200000000 : ℝ)))]

theorem thL_46_cos : (183498910435521 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 46) ∧ Real.cos (856993 / 10000 * Real.log 46) ≤ (91749484149053 / 500000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_46_sin : (245754969732453 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 46) ∧ Real.sin (856993 / 10000 * Real.log 46) ≤ (983019936792397 / 1000000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_46 : (183498910435521 / 1000000000000000 : ℝ) ≤ cC 46 ∧ cC 46 ≤ (91749484149053 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_46_cos

theorem sCB_46 : (245754969732453 / 250000000000000 : ℝ) ≤ sC 46 ∧ sC 46 ≤ (983019936792397 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_46_sin

theorem thL_47_r_bounds : (1754514458277639213 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 ≤ (1754515621722360787 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_47
  have hl : (82488738587460543 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 47 ∧ 856993 / 10000 * Real.log 47 ≤ (82488738601790013 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_47_eq : (856993 / 10000 * Real.log 47) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 + π) + ((52 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_47_cos_r : (4980772671131 / 5000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) ≤ (996154592398437 / 1000000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (10965719 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) (10965719 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 - (10965719 / 125000000 : ℝ)| ≤ (581722360787 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 - (10965719 / 125000000 : ℝ))]

theorem thL_47_sin_r : (17522649223659 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) ≤ (21903326072633 / 250000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (10965719 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210) (10965719 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 - (10965719 / 125000000 : ℝ)| ≤ (581722360787 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 47) 210 - (10965719 / 125000000 : ℝ))]

theorem thL_47_cos : (-996154592398437 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 47) ∧ Real.cos (856993 / 10000 * Real.log 47) ≤ (-4980772671131 / 5000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_47_sin : (-21903326072633 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 47) ∧ Real.sin (856993 / 10000 * Real.log 47) ≤ (-17522649223659 / 200000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_47 : (-996154592398437 / 1000000000000000 : ℝ) ≤ cC 47 ∧ cC 47 ≤ (-4980772671131 / 5000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_47_cos

theorem sCB_47 : (-21903326072633 / 250000000000000 : ℝ) ≤ sC 47 ∧ sC 47 ≤ (-17522649223659 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_47_sin

theorem thL_48_r_bounds : (64238365397285468283 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 ≤ (64238377002714531717 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_48
  have hl : (165879608390354807 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 48 ∧ 856993 / 10000 * Real.log 48 ≤ (331759216838029949 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_48_eq : (856993 / 10000 * Real.log 48) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 + π + π / 2) + ((52 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_48_cos_r : (474429898455373 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) ≤ (189771970987579 / 200000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (20074491 / 62500000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) (20074491 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 - (20074491 / 62500000 : ℝ)| ≤ (5802714531717 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 - (20074491 / 62500000 : ℝ))]

theorem thL_48_sin_r : (157848829919507 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) ≤ (315697717866161 / 1000000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (20074491 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211) (20074491 / 62500000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 - (20074491 / 62500000 : ℝ)| ≤ (5802714531717 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 48) 211 - (20074491 / 62500000 : ℝ))]

theorem thL_48_cos : (157848829919507 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 48) ∧ Real.cos (856993 / 10000 * Real.log 48) ≤ (315697717866161 / 1000000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_48_sin : (-189771970987579 / 200000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 48) ∧ Real.sin (856993 / 10000 * Real.log 48) ≤ (-474429898455373 / 500000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_48 : (157848829919507 / 500000000000000 : ℝ) ≤ cC 48 ∧ cC 48 ≤ (315697717866161 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_48_cos

theorem sCB_48 : (-189771970987579 / 200000000000000 : ℝ) ≤ sC 48 ∧ sC 48 ≤ (-474429898455373 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_48_sin

theorem thL_49_r_bounds : (25872698998231686109 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 ≤ (25872701901768313891 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_49
  have hl : (333526275260482717 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 49 ∧ 856993 / 10000 * Real.log 49 ≤ (166763137658902587 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_49_eq : (856993 / 10000 * Real.log 49) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) + ((53 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_49_cos_r : (869081389002961 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) ≤ (27158795221077 / 31250000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (517454009 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) (517454009 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 - (517454009 / 1000000000 : ℝ)| ≤ (1451768313891 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 - (517454009 / 1000000000 : ℝ))]

theorem thL_49_sin_r : (24733452048457 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) ≤ (98933819807981 / 200000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (517454009 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212) (517454009 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 - (517454009 / 1000000000 : ℝ)| ≤ (1451768313891 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 49) 212 - (517454009 / 1000000000 : ℝ))]

theorem thL_49_cos : (869081389002961 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 49) ∧ Real.cos (856993 / 10000 * Real.log 49) ≤ (27158795221077 / 31250000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_49_sin : (24733452048457 / 50000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 49) ∧ Real.sin (856993 / 10000 * Real.log 49) ≤ (98933819807981 / 200000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_49 : (869081389002961 / 1000000000000000 : ℝ) ≤ cC 49 ∧ cC 49 ≤ (27158795221077 / 31250000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_49_cos

theorem sCB_49 : (24733452048457 / 50000000000000 : ℝ) ≤ sC 49 ∧ sC 49 ≤ (98933819807981 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_49_sin

theorem thL_51_r_bounds : (-30660233110430365421 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 ≤ (-30660230809569634579 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_51
  have hl : (168477352216571007 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 51 ∧ 856993 / 10000 * Real.log 51 ≤ (336954704490467909 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_51_eq : (856993 / 10000 * Real.log 51) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 + π + π / 2) + ((53 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_51_cos_r : (22510584050699 / 31250000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) ≤ (720338747229759 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(766505799 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) (-(766505799 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 - (-(766505799 / 1000000000 : ℝ))| ≤ (1150430365421 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 - (-(766505799 / 1000000000 : ℝ)))]

theorem thL_51_sin_r : (-346811249303233 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) ≤ (-173405610269971 / 250000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (766505799 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2539213137611162644575490471423817832591929685118571235588846423590704241803581731472980833162321587703310277766019374587099 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(766505799 / 1000000000 : ℝ)) ∧ Real.sin (-(766505799 / 1000000000 : ℝ)) ≤ -((341817153137469083713922365560304870715252536262894837153173504683810998121615022979863742539383764674521 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215) (-(766505799 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 - (-(766505799 / 1000000000 : ℝ))| ≤ (1150430365421 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 51) 215 - (-(766505799 / 1000000000 : ℝ)))]

theorem thL_51_cos : (-346811249303233 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 51) ∧ Real.cos (856993 / 10000 * Real.log 51) ≤ (-173405610269971 / 250000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_51_sin : (-720338747229759 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 51) ∧ Real.sin (856993 / 10000 * Real.log 51) ≤ (-22510584050699 / 31250000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_51 : (-346811249303233 / 500000000000000 : ℝ) ≤ cC 51 ∧ cC 51 ≤ (-173405610269971 / 250000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_51_cos

theorem sCB_51 : (-720338747229759 / 1000000000000000 : ℝ) ≤ sC 51 ∧ sC 51 ≤ (-22510584050699 / 31250000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_51_sin

theorem thL_52_r_bounds : (-8414822375811740579 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 ≤ (-8414821649188259421 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_52
  have hl : (338618820798435321 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 52 ∧ 856993 / 10000 * Real.log 52 ≤ (338618820855762609 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_52_eq : (856993 / 10000 * Real.log 52) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) + ((54 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_52_cos_r : (156367869935363 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) ≤ (390919703912389 / 500000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(673185761 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) (-(673185761 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 - (-(673185761 / 1000000000 : ℝ))| ≤ (363311740579 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 - (-(673185761 / 1000000000 : ℝ)))]

theorem thL_52_sin_r : (-311739964579181 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) ≤ (-311739935513773 / 500000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (673185761 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((554631758037665760335894856384805662613513988778733352262992545271928005706607934278014944353343064245209826563431376911543383 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(673185761 / 1000000000 : ℝ)) ∧ Real.sin (-(673185761 / 1000000000 : ℝ)) ≤ -((24887322476011725484083173248171022320744262618665992680620529462991951245183182633189552569924728107148639 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216) (-(673185761 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 - (-(673185761 / 1000000000 : ℝ))| ≤ (363311740579 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 52) 216 - (-(673185761 / 1000000000 : ℝ)))]

theorem thL_52_cos : (156367869935363 / 200000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 52) ∧ Real.cos (856993 / 10000 * Real.log 52) ≤ (390919703912389 / 500000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_52_sin : (-311739964579181 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 52) ∧ Real.sin (856993 / 10000 * Real.log 52) ≤ (-311739935513773 / 500000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_52 : (156367869935363 / 200000000000000 : ℝ) ≤ cC 52 ∧ cC 52 ≤ (390919703912389 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_52_cos

theorem sCB_52 : (-311739964579181 / 500000000000000 : ℝ) ≤ sC 52 ∧ sC 52 ≤ (-311739935513773 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_52_sin

theorem thL_53_r_bounds : (-122313028161076474799 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 ≤ (-122313016638923525201 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_53
  have hl : (21265702360855449 / 62500000000000 : ℝ) ≤ 856993 / 10000 * Real.log 53 ∧ 856993 / 10000 * Real.log 53 ≤ (340251237831015691 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_53_eq : (856993 / 10000 * Real.log 53) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 + π / 2) + ((54 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_53_cos_r : (409375191884777 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) ≤ (409375220693017 / 500000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(76445639 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) (-(76445639 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 - (-(76445639 / 125000000 : ℝ))| ≤ (5761076474799 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 - (-(76445639 / 125000000 : ℝ)))]

theorem thL_53_sin_r : (-57414962768971 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) ≤ (-22965982803147 / 40000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (76445639 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((929046627675717558385220262187874320151840452465849440325743271069618148306072640410673757217626862506804458661217 / 1618126407265663146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(76445639 / 125000000 : ℝ)) ∧ Real.sin (-(76445639 / 125000000 : ℝ)) ≤ -((2668031341016196070856404841661385778436340626976908825836485029660946273425002789893362366865961 / 4646927118301391601562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217) (-(76445639 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 - (-(76445639 / 125000000 : ℝ))| ≤ (5761076474799 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 53) 217 - (-(76445639 / 125000000 : ℝ)))]

theorem thL_53_cos : (22965982803147 / 40000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 53) ∧ Real.cos (856993 / 10000 * Real.log 53) ≤ (57414962768971 / 100000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_53_sin : (409375191884777 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 53) ∧ Real.sin (856993 / 10000 * Real.log 53) ≤ (409375220693017 / 500000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_53 : (22965982803147 / 40000000000000 : ℝ) ≤ cC 53 ∧ cC 53 ≤ (57414962768971 / 100000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_53_cos

theorem sCB_53 : (409375191884777 / 500000000000000 : ℝ) ≤ sC 53 ∧ sC 53 ≤ (409375220693017 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_53_sin

theorem thL_54_r_bounds : (-58045875295206599323 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 ≤ (-58045869504793400677 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_54
  have hl : (341853140488335397 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 54 ∧ 856993 / 10000 * Real.log 54 ≤ (341853140545664971 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_54_eq : (856993 / 10000 * Real.log 54) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 + π) + ((54 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_54_cos_r : (16724222824581 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) ≤ (836211199136237 / 1000000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(145114681 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) (-(145114681 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 - (-(145114681 / 250000000 : ℝ))| ≤ (2895206599323 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 - (-(145114681 / 250000000 : ℝ)))]

theorem thL_54_sin_r : (-548407613563393 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) ≤ (-137101888914781 / 250000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (145114681 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((50886652413792797989142649665194753367899518944055507122408369428897938802679002625569925957393600096300627250764030041 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(145114681 / 250000000 : ℝ)) ∧ Real.sin (-(145114681 / 250000000 : ℝ)) ≤ -((5219143837310783939896757409775863993587402163873001817988080474336510051036040704836801006927426519 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218) (-(145114681 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 - (-(145114681 / 250000000 : ℝ))| ≤ (2895206599323 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 54) 218 - (-(145114681 / 250000000 : ℝ)))]

theorem thL_54_cos : (-836211199136237 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 54) ∧ Real.cos (856993 / 10000 * Real.log 54) ≤ (-16724222824581 / 20000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_54_sin : (137101888914781 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 54) ∧ Real.sin (856993 / 10000 * Real.log 54) ≤ (548407613563393 / 1000000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_54 : (-836211199136237 / 1000000000000000 : ℝ) ≤ cC 54 ∧ cC 54 ≤ (-16724222824581 / 20000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_54_cos

theorem sCB_54 : (137101888914781 / 250000000000000 : ℝ) ≤ sC 54 ∧ sC 54 ≤ (548407613563393 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_54_sin

theorem thL_56_r_bounds : (-3026848794411403847 / 5000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 ≤ (-3026848505588596153 / 5000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_56
  have hl : (1724849110682141 / 5000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 56 ∧ 856993 / 10000 * Real.log 56 ≤ (344969822193759537 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_56_eq : (856993 / 10000 * Real.log 56) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_56_cos_r : (411145862064629 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) ≤ (822291781898877 / 1000000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(60536973 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) (-(60536973 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 - (-(60536973 / 100000000 : ℝ))| ≤ (144411403847 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 - (-(60536973 / 100000000 : ℝ)))]

theorem thL_56_sin_r : (-284533084979923 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) ≤ (-71133264024381 / 125000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (60536973 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((208323732925674808086281225116726430944557462180429754273874102809018984537301314383650133691951081633956048633 / 366080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(60536973 / 100000000 : ℝ)) ∧ Real.sin (-(60536973 / 100000000 : ℝ)) ≤ -((400622563318439608971514843944395116385533045224963967312808357437670641557956383516323280269 / 704000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220) (-(60536973 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 - (-(60536973 / 100000000 : ℝ))| ≤ (144411403847 / 5000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 56) 220 - (-(60536973 / 100000000 : ℝ)))]

theorem thL_56_cos : (411145862064629 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 56) ∧ Real.cos (856993 / 10000 * Real.log 56) ≤ (822291781898877 / 1000000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_56_sin : (-284533084979923 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 56) ∧ Real.sin (856993 / 10000 * Real.log 56) ≤ (-71133264024381 / 125000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_56 : (411145862064629 / 500000000000000 : ℝ) ≤ cC 56 ∧ cC 56 ≤ (822291781898877 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_56_cos

theorem sCB_56 : (-284533084979923 / 500000000000000 : ℝ) ≤ sC 56 ∧ sC 56 ≤ (-71133264024381 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_56_sin

theorem thL_57_r_bounds : (-65932471780269815017 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 ≤ (-65932466019730184983 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_57
  have hl : (69297332700828557 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 57 ∧ 856993 / 10000 * Real.log 57 ≤ (346486663561474851 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_57_eq : (856993 / 10000 * Real.log 57) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 + π / 2) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_57_cos_r : (790406067067589 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) ≤ (395203062343537 / 500000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(659324689 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) (-(659324689 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 - (-(659324689 / 1000000000 : ℝ))| ≤ (2880269815017 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 - (-(659324689 / 1000000000 : ℝ)))]

theorem thL_57_sin_r : (-612583250568423 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) ≤ (-612583192962311 / 1000000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (659324689 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3814568463666176601655245030140486587105889055316584174668752062437192868622985647942933002974360995235699413200265175720649169 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(659324689 / 1000000000 : ℝ)) ∧ Real.sin (-(659324689 / 1000000000 : ℝ)) ≤ -((24452361946549534003878478388688530009881708451251394794883734598458851621586128487130705164675601040728911 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221) (-(659324689 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 - (-(659324689 / 1000000000 : ℝ))| ≤ (2880269815017 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 57) 221 - (-(659324689 / 1000000000 : ℝ)))]

theorem thL_57_cos : (612583192962311 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 57) ∧ Real.cos (856993 / 10000 * Real.log 57) ≤ (612583250568423 / 1000000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_57_sin : (790406067067589 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 57) ∧ Real.sin (856993 / 10000 * Real.log 57) ≤ (395203062343537 / 500000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_57 : (612583192962311 / 1000000000000000 : ℝ) ≤ cC 57 ∧ cC 57 ≤ (612583250568423 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_57_cos

theorem sCB_57 : (790406067067589 / 1000000000000000 : ℝ) ≤ sC 57 ∧ sC 57 ≤ (395203062343537 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_57_sin

theorem thL_58_r_bounds : (-36983043500643826547 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 ≤ (-36983040199356173453 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_58
  have hl : (86994280919656419 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 58 ∧ 856993 / 10000 * Real.log 58 ≤ (173988561872239963 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_58_eq : (856993 / 10000 * Real.log 58) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 + π) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_58_cos_r : (147739435338779 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) ≤ (46168577673477 / 62500000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(739660837 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) (-(739660837 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 - (-(739660837 / 1000000000 : ℝ))| ≤ (1650643826547 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 - (-(739660837 / 1000000000 : ℝ)))]

theorem thL_58_sin_r : (-33701872232593 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) ≤ (-16850934465573 / 25000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (739660837 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4197244982254106180596957193718902898581035544521918136876273324189841984348588623711261620025518067644563178713181867095167797 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(739660837 / 1000000000 : ℝ)) ∧ Real.sin (-(739660837 / 1000000000 : ℝ)) ≤ -((26905416552783791986157415073586882874313832409043887348448372739769696839309270682212689875925485888328387 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222) (-(739660837 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 - (-(739660837 / 1000000000 : ℝ))| ≤ (1650643826547 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 58) 222 - (-(739660837 / 1000000000 : ℝ)))]

theorem thL_58_cos : (-46168577673477 / 62500000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 58) ∧ Real.cos (856993 / 10000 * Real.log 58) ≤ (-147739435338779 / 200000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_58_sin : (16850934465573 / 25000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 58) ∧ Real.sin (856993 / 10000 * Real.log 58) ≤ (33701872232593 / 50000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_58 : (-46168577673477 / 62500000000000 : ℝ) ≤ cC 58 ∧ cC 58 ≤ (-147739435338779 / 200000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_58_cos

theorem sCB_58 : (16850934465573 / 25000000000000 : ℝ) ≤ sC 58 ∧ sC 58 ≤ (33701872232593 / 50000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_58_sin

theorem thL_59_r_bounds : (36266005047191023453 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 ≤ (36266008752808976547 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_59
  have hl : (174721052324925363 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 59 ∧ 856993 / 10000 * Real.log 59 ≤ (349442104723523229 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_59_eq : (856993 / 10000 * Real.log 59) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 + π) + ((55 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_59_cos_r : (93535881457363 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) ≤ (29931485032621 / 40000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (362660069 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) (362660069 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 - (362660069 / 500000000 : ℝ)| ≤ (1852808976547 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 - (362660069 / 500000000 : ℝ))]

theorem thL_59_sin_r : (331687497363369 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) ≤ (663375068841567 / 1000000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (362660069 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222) (362660069 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 - (362660069 / 500000000 : ℝ)| ≤ (1852808976547 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 59) 222 - (362660069 / 500000000 : ℝ))]

theorem thL_59_cos : (-29931485032621 / 40000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 59) ∧ Real.cos (856993 / 10000 * Real.log 59) ≤ (-93535881457363 / 125000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_59_sin : (-663375068841567 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 59) ∧ Real.sin (856993 / 10000 * Real.log 59) ≤ (-331687497363369 / 500000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_59 : (-29931485032621 / 40000000000000 : ℝ) ≤ cC 59 ∧ cC 59 ≤ (-93535881457363 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_59_cos

theorem sCB_59 : (-663375068841567 / 1000000000000000 : ℝ) ≤ sC 59 ∧ sC 59 ≤ (-331687497363369 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_59_sin

theorem thL_61_r_bounds : (344246348485841959 / 781250000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 ≤ (344246417139158041 / 781250000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_61
  have hl : (176149506264265449 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 61 ∧ 856993 / 10000 * Real.log 61 ≤ (70459802523198993 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_61_eq : (856993 / 10000 * Real.log 61) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) + ((56 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_61_cos_r : (904480807520147 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) ≤ (113060111924563 / 125000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (44063537 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) (44063537 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 - (44063537 / 100000000 : ℝ)| ≤ (34326658041 / 781250000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 - (44063537 / 100000000 : ℝ))]

theorem thL_61_sin_r : (213257093589317 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) ≤ (106628568763721 / 250000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (44063537 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224) (44063537 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 - (44063537 / 100000000 : ℝ)| ≤ (34326658041 / 781250000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 61) 224 - (44063537 / 100000000 : ℝ))]

theorem thL_61_cos : (904480807520147 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 61) ∧ Real.cos (856993 / 10000 * Real.log 61) ≤ (113060111924563 / 125000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_61_sin : (213257093589317 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 61) ∧ Real.sin (856993 / 10000 * Real.log 61) ≤ (106628568763721 / 250000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_61 : (904480807520147 / 1000000000000000 : ℝ) ≤ cC 61 ∧ cC 61 ≤ (113060111924563 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_61_cos

theorem sCB_61 : (213257093589317 / 500000000000000 : ℝ) ≤ sC 61 ∧ sC 61 ≤ (106628568763721 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_61_sin

theorem thL_62_r_bounds : (2106834038467549377 / 8000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 ≤ (2106834793532450623 / 8000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_62
  have hl : (353692527783660183 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 62 ∧ 856993 / 10000 * Real.log 62 ≤ (353692527877212751 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_62_eq : (856993 / 10000 * Real.log 62) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 + π / 2) + ((56 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_62_cos_r : (120690271270463 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) ≤ (482761132273409 / 500000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (131677151 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) (131677151 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 - (131677151 / 500000000 : ℝ)| ≤ (377532450623 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 - (131677151 / 500000000 : ℝ))]

theorem thL_62_sin_r : (32540077026143 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) ≤ (260320710592257 / 1000000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (131677151 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225) (131677151 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 - (131677151 / 500000000 : ℝ)| ≤ (377532450623 / 8000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 62) 225 - (131677151 / 500000000 : ℝ))]

theorem thL_62_cos : (-260320710592257 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 62) ∧ Real.cos (856993 / 10000 * Real.log 62) ≤ (-32540077026143 / 125000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_62_sin : (120690271270463 / 125000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 62) ∧ Real.sin (856993 / 10000 * Real.log 62) ≤ (482761132273409 / 500000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_62 : (-260320710592257 / 1000000000000000 : ℝ) ≤ cC 62 ∧ cC 62 ≤ (-32540077026143 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_62_cos

theorem sCB_62 : (120690271270463 / 125000000000000 : ℝ) ≤ sC 62 ∧ sC 62 ≤ (482761132273409 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_62_sin

theorem thL_63_r_bounds : (6377598004128005289 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 ≤ (6377607995871994711 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_63
  have hl : (88765936458921979 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 63 ∧ 856993 / 10000 * Real.log 63 ≤ (355063745934857233 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_63_eq : (856993 / 10000 * Real.log 63) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 + π) + ((56 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_63_cos_r : (124745868532883 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) ≤ (124745881022563 / 125000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (6377603 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) (6377603 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 - (6377603 / 100000000 : ℝ)| ≤ (4995871994711 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 - (6377603 / 100000000 : ℝ))]

theorem thL_63_sin_r : (31866377626683 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) ≤ (63732855170807 / 1000000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (6377603 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226) (6377603 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 - (6377603 / 100000000 : ℝ)| ≤ (4995871994711 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 63) 226 - (6377603 / 100000000 : ℝ))]

theorem thL_63_cos : (-124745881022563 / 125000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 63) ∧ Real.cos (856993 / 10000 * Real.log 63) ≤ (-124745868532883 / 125000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_63_sin : (-63732855170807 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 63) ∧ Real.sin (856993 / 10000 * Real.log 63) ≤ (-31866377626683 / 500000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_63 : (-124745881022563 / 125000000000000 : ℝ) ≤ cC 63 ∧ cC 63 ≤ (-124745868532883 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_63_cos

theorem sCB_63 : (-63732855170807 / 1000000000000000 : ℝ) ≤ sC 63 ∧ sC 63 ≤ (-31866377626683 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_63_sin

theorem thL_64_r_bounds : (-31479435894317313269 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 ≤ (-31479414905682686731 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_64
  have hl : (178206684501484973 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 64 ∧ 856993 / 10000 * Real.log 64 ≤ (7128267382146549 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_64_eq : (856993 / 10000 * Real.log 64) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 + π + π / 2) + ((56 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_64_cos_r : (197527714257881 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) ≤ (987638676232579 / 1000000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(157397127 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) (-(157397127 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 - (-(157397127 / 1000000000 : ℝ))| ≤ (10494317313269 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 - (-(157397127 / 1000000000 : ℝ)))]

theorem thL_64_sin_r : (-156748095060619 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) ≤ (-31349598023489 / 200000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (157397127 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4016762640169498128749350263060308719584468275478115289142374187286470168392533795391377823501514569408608796666128081044669 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(157397127 / 1000000000 : ℝ)) ∧ Real.sin (-(157397127 / 1000000000 : ℝ)) ≤ -((77245435387874964011530871722644478610484110319328070097808781186308680525987702864642803888849671880217 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227) (-(157397127 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 - (-(157397127 / 1000000000 : ℝ))| ≤ (10494317313269 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 64) 227 - (-(157397127 / 1000000000 : ℝ)))]

theorem thL_64_cos : (-156748095060619 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 64) ∧ Real.cos (856993 / 10000 * Real.log 64) ≤ (-31349598023489 / 200000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_64_sin : (-987638676232579 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 64) ∧ Real.sin (856993 / 10000 * Real.log 64) ≤ (-197527714257881 / 200000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_64 : (-156748095060619 / 1000000000000000 : ℝ) ≤ cC 64 ∧ cC 64 ≤ (-31349598023489 / 200000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_64_cos

theorem sCB_64 : (-987638676232579 / 1000000000000000 : ℝ) ≤ sC 64 ∧ sC 64 ≤ (-197527714257881 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_64_sin

theorem thL_66_r_bounds : (-66188022826889519633 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 ≤ (-66188011373110480367 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_66
  have hl : (44881309826087681 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 66 ∧ 856993 / 10000 * Real.log 66 ≤ (359050478722300221 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_66_eq : (856993 / 10000 * Real.log 66) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 + π / 2) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_66_cos_r : (197209503510099 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) ≤ (157767625718589 / 200000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(661880171 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) (-(661880171 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 - (-(661880171 / 1000000000 : ℝ))| ≤ (5726889519633 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 - (-(661880171 / 1000000000 : ℝ)))]

theorem thL_66_sin_r : (-614601145154211 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) ≤ (-153650257653917 / 250000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (661880171 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((3827133757964483560354257138463573987272040844672093597702474516628391382663260738994238970401337934627743653000764653080464411 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(661880171 / 1000000000 : ℝ)) ∧ Real.sin (-(661880171 / 1000000000 : ℝ)) ≤ -((24532908704870543519692181379277903594784759969978799042551756617022770233250967284328175434466845320383629 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229) (-(661880171 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 - (-(661880171 / 1000000000 : ℝ))| ≤ (5726889519633 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 66) 229 - (-(661880171 / 1000000000 : ℝ)))]

theorem thL_66_cos : (153650257653917 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 66) ∧ Real.cos (856993 / 10000 * Real.log 66) ≤ (614601145154211 / 1000000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_66_sin : (197209503510099 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 66) ∧ Real.sin (856993 / 10000 * Real.log 66) ≤ (157767625718589 / 200000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_66 : (153650257653917 / 250000000000000 : ℝ) ≤ cC 66 ∧ cC 66 ≤ (614601145154211 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_66_cos

theorem sCB_66 : (197209503510099 / 250000000000000 : ℝ) ≤ sC 66 ∧ sC 66 ≤ (157767625718589 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_66_sin

theorem thL_67_r_bounds : (62685533480906280367 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 ≤ (62685545319093719633 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_67
  have hl : (360339214171504663 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 67 ∧ 856993 / 10000 * Real.log 67 ≤ (360339214289222263 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_67_eq : (856993 / 10000 * Real.log 67) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 + π / 2) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_67_cos_r : (404938039547639 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) ≤ (809876197484839 / 1000000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (313427697 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) (313427697 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 - (313427697 / 500000000 : ℝ)| ≤ (5919093719633 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 - (313427697 / 500000000 : ℝ))]

theorem thL_67_sin_r : (293300430948727 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) ≤ (5866009802797 / 10000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (313427697 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229) (313427697 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 - (313427697 / 500000000 : ℝ)| ≤ (5919093719633 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 67) 229 - (313427697 / 500000000 : ℝ))]

theorem thL_67_cos : (-5866009802797 / 10000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 67) ∧ Real.cos (856993 / 10000 * Real.log 67) ≤ (-293300430948727 / 500000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_67_sin : (404938039547639 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 67) ∧ Real.sin (856993 / 10000 * Real.log 67) ≤ (809876197484839 / 1000000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_67 : (-5866009802797 / 10000000000000 : ℝ) ≤ cC 67 ∧ cC 67 ≤ (-293300430948727 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_67_cos

theorem sCB_67 : (404938039547639 / 500000000000000 : ℝ) ≤ sC 67 ∧ sC 67 ≤ (809876197484839 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_67_sin

theorem thL_68_r_bounds : (6514029782808591519 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 ≤ (6514032217191408481 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_68
  have hl : (90402214162991663 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 68 ∧ 856993 / 10000 * Real.log 68 ≤ (180804428386753441 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_68_eq : (856993 / 10000 * Real.log 68) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 + π) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_68_cos_r : (947426421291141 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) ≤ (473713271505143 / 500000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (6514031 / 20000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) (6514031 / 20000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 - (6514031 / 20000000 : ℝ)| ≤ (1217191408481 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 - (6514031 / 20000000 : ℝ))]

theorem thL_68_sin_r : (319973470732529 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) ≤ (319973592451671 / 1000000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (6514031 / 20000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230) (6514031 / 20000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 - (6514031 / 20000000 : ℝ)| ≤ (1217191408481 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 68) 230 - (6514031 / 20000000 : ℝ))]

theorem thL_68_cos : (-473713271505143 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 68) ∧ Real.cos (856993 / 10000 * Real.log 68) ≤ (-947426421291141 / 1000000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_68_sin : (-319973592451671 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 68) ∧ Real.sin (856993 / 10000 * Real.log 68) ≤ (-319973470732529 / 1000000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_68 : (-473713271505143 / 500000000000000 : ℝ) ≤ cC 68 ∧ cC 68 ≤ (-947426421291141 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_68_cos

theorem sCB_68 : (-319973592451671 / 1000000000000000 : ℝ) ≤ sC 68 ∧ sC 68 ≤ (-319973470732529 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_68_sin

theorem thL_69_r_bounds : (601205203973304213 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 ≤ (601217796026695787 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_69
  have hl : (362859963542489527 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 69 ∧ 856993 / 10000 * Real.log 69 ≤ (181429981833790693 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_69_eq : (856993 / 10000 * Real.log 69) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 + π + π / 2) + ((57 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_69_cos_r : (999981864330783 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) ≤ (499990995125659 / 500000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1202423 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) (1202423 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 - (1202423 / 200000000 : ℝ)| ≤ (6296026695787 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 - (1202423 / 200000000 : ℝ))]

theorem thL_69_sin_r : (6012015821287 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) ≤ (3006070870911 / 500000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1202423 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231) (1202423 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 - (1202423 / 200000000 : ℝ)| ≤ (6296026695787 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 69) 231 - (1202423 / 200000000 : ℝ))]

theorem thL_69_cos : (6012015821287 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 69) ∧ Real.cos (856993 / 10000 * Real.log 69) ≤ (3006070870911 / 500000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_69_sin : (-499990995125659 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 69) ∧ Real.sin (856993 / 10000 * Real.log 69) ≤ (-999981864330783 / 1000000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_69 : (6012015821287 / 1000000000000000 : ℝ) ≤ cC 69 ∧ cC 69 ≤ (3006070870911 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_69_cos

theorem sCB_69 : (-499990995125659 / 500000000000000 : ℝ) ≤ sC 69 ∧ sC 69 ≤ (-999981864330783 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_69_sin

theorem thL_71_r_bounds : (-137372516980454456351 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 ≤ (-137372490619545543649 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_71
  have hl : (2283179259739429 / 6250000000000 : ℝ) ≤ 856993 / 10000 * Real.log 71 ∧ 856993 / 10000 * Real.log 71 ≤ (73061736337955897 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_71_eq : (856993 / 10000 * Real.log 71) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 + π / 2) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_71_cos_r : (773239273122703 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) ≤ (773239404950269 / 1000000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(686862519 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) (-(686862519 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 - (-(686862519 / 1000000000 : ℝ))| ≤ (13180454456351 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 - (-(686862519 / 1000000000 : ℝ)))]

theorem thL_71_sin_r : (-317057174705077 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) ≤ (-79264277200549 / 125000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (686862519 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2321365569065652473995023337325911736541003012348552873877406173897895891361855158801580083446587903571787476644546913229259 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(686862519 / 1000000000 : ℝ)) ∧ Real.sin (-(686862519 / 1000000000 : ℝ)) ≤ -((44641645558869230388289273343445577549892866351981234559274958443081566344638005003065294077103505029743 / 70400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233) (-(686862519 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 - (-(686862519 / 1000000000 : ℝ))| ≤ (13180454456351 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 71) 233 - (-(686862519 / 1000000000 : ℝ)))]

theorem thL_71_cos : (79264277200549 / 125000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 71) ∧ Real.cos (856993 / 10000 * Real.log 71) ≤ (317057174705077 / 500000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_71_sin : (773239273122703 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 71) ∧ Real.sin (856993 / 10000 * Real.log 71) ≤ (773239404950269 / 1000000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_71 : (79264277200549 / 125000000000000 : ℝ) ≤ cC 71 ∧ cC 71 ≤ (317057174705077 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_71_cos

theorem sCB_71 : (773239273122703 / 1000000000000000 : ℝ) ≤ sC 71 ∧ sC 71 ≤ (773239404950269 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_71_sin

theorem thL_72_r_bounds : (102349712278053343649 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 ≤ (102349739321946656351 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_72
  have hl : (366507292704601179 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 72 ∧ 856993 / 10000 * Real.log 72 ≤ (733014585677877 / 2000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_72_eq : (856993 / 10000 * Real.log 72) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 + π / 2) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_72_cos_r : (21797236632069 / 25000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) ≤ (871889600502901 / 1000000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (511748629 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) (511748629 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 - (511748629 / 1000000000 : ℝ)| ≤ (13521946656351 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 - (511748629 / 1000000000 : ℝ))]

theorem thL_72_sin_r : (489702538500659 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) ≤ (489702673720153 / 1000000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (511748629 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233) (511748629 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 - (511748629 / 1000000000 : ℝ)| ≤ (13521946656351 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 72) 233 - (511748629 / 1000000000 : ℝ))]

theorem thL_72_cos : (-489702673720153 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 72) ∧ Real.cos (856993 / 10000 * Real.log 72) ≤ (-489702538500659 / 1000000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_72_sin : (21797236632069 / 25000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 72) ∧ Real.sin (856993 / 10000 * Real.log 72) ≤ (871889600502901 / 1000000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_72 : (-489702673720153 / 1000000000000000 : ℝ) ≤ cC 72 ∧ cC 72 ≤ (-489702538500659 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_72_cos

theorem sCB_72 : (21797236632069 / 25000000000000 : ℝ) ≤ sC 72 ∧ sC 72 ≤ (871889600502901 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_72_sin

theorem thL_73_r_bounds : (12303028547623209901 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 ≤ (12303042252376790099 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_73
  have hl : (367689370755482041 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 73 ∧ 856993 / 10000 * Real.log 73 ≤ (14707574835699741 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_73_eq : (856993 / 10000 * Real.log 73) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 + π) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_73_cos_r : (992441239019231 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) ≤ (62027586004173 / 62500000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (61515177 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) (61515177 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 - (61515177 / 500000000 : ℝ)| ≤ (6852376790099 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 - (61515177 / 500000000 : ℝ))]

theorem thL_73_sin_r : (122720146120527 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) ≤ (122720283168063 / 1000000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (61515177 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234) (61515177 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 - (61515177 / 500000000 : ℝ)| ≤ (6852376790099 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 73) 234 - (61515177 / 500000000 : ℝ))]

theorem thL_73_cos : (-62027586004173 / 62500000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 73) ∧ Real.cos (856993 / 10000 * Real.log 73) ≤ (-992441239019231 / 1000000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_73_sin : (-122720283168063 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 73) ∧ Real.sin (856993 / 10000 * Real.log 73) ≤ (-122720146120527 / 1000000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_73 : (-62027586004173 / 62500000000000 : ℝ) ≤ cC 73 ∧ cC 73 ≤ (-992441239019231 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_73_cos

theorem sCB_73 : (-122720283168063 / 1000000000000000 : ℝ) ≤ sC 73 ∧ sC 73 ≤ (-122720146120527 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_73_sin

theorem thL_74_r_bounds : (-5635423698286329619 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 ≤ (-5635420901713670381 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_74
  have hl : (368855365612206411 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 74 ∧ 856993 / 10000 * Real.log 74 ≤ (184427682875857511 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_74_eq : (856993 / 10000 * Real.log 74) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 + π + π / 2) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_74_cos_r : (960564403675653 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) ≤ (30017641984509 / 31250000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(56354223 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) (-(56354223 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 - (-(56354223 / 200000000 : ℝ))| ≤ (1398286329619 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 - (-(56354223 / 200000000 : ℝ)))]

theorem thL_74_sin_r : (-69514355962099 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) ≤ (-139028642009881 / 500000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (56354223 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((833873806362114460221946634700676754622068434021427042893084958516132511946305427149937669880062143778975983482883 / 2998927360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(56354223 / 200000000 : ℝ)) ∧ Real.sin (-(56354223 / 200000000 : ℝ)) ≤ -((2806306079103269703668212274927065198960494089668252752445816098186629922174954816375970354521633 / 10092544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235) (-(56354223 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 - (-(56354223 / 200000000 : ℝ))| ≤ (1398286329619 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 74) 235 - (-(56354223 / 200000000 : ℝ)))]

theorem thL_74_cos : (-69514355962099 / 250000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 74) ∧ Real.cos (856993 / 10000 * Real.log 74) ≤ (-139028642009881 / 500000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_74_sin : (-30017641984509 / 31250000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 74) ∧ Real.sin (856993 / 10000 * Real.log 74) ≤ (-960564403675653 / 1000000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_74 : (-69514355962099 / 250000000000000 : ℝ) ≤ cC 74 ∧ cC 74 ≤ (-139028642009881 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_74_cos

theorem sCB_74 : (-30017641984509 / 31250000000000 : ℝ) ≤ sC 74 ∧ sC 74 ≤ (-960564403675653 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_74_sin

theorem thL_76_r_bounds : (21644129743780293027 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 ≤ (21644136956219706973 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_76
  have hl : (46392601964808901 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 76 ∧ 856993 / 10000 * Real.log 76 ≤ (23196300991406077 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_76_eq : (856993 / 10000 * Real.log 76) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) + ((59 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_76_cos_r : (907760202864177 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) ≤ (907760347113057 / 1000000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (432882667 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) (432882667 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 - (432882667 / 1000000000 : ℝ)| ≤ (3606219706973 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 - (432882667 / 1000000000 : ℝ))]

theorem thL_76_sin_r : (1677956960791 / 4000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) ≤ (419489384446543 / 1000000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (432882667 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236) (432882667 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 - (432882667 / 1000000000 : ℝ)| ≤ (3606219706973 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 76) 236 - (432882667 / 1000000000 : ℝ))]

theorem thL_76_cos : (907760202864177 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 76) ∧ Real.cos (856993 / 10000 * Real.log 76) ≤ (907760347113057 / 1000000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_76_sin : (1677956960791 / 4000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 76) ∧ Real.sin (856993 / 10000 * Real.log 76) ≤ (419489384446543 / 1000000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_76 : (907760202864177 / 1000000000000000 : ℝ) ≤ cC 76 ∧ cC 76 ≤ (907760347113057 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_76_cos

theorem sCB_76 : (1677956960791 / 4000000000000 : ℝ) ≤ sC 76 ∧ sC 76 ≤ (419489384446543 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_76_sin

theorem thL_77_r_bounds : (-3529098492626551739 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 ≤ (-3529069107373448261 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_77
  have hl : (186130541978963683 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 77 ∧ 856993 / 10000 * Real.log 77 ≤ (372261084103997803 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_77_eq : (856993 / 10000 * Real.log 77) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 + π / 2) + ((59 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_77_cos_r : (49992212508519 / 50000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) ≤ (999844397096647 / 1000000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(17645419 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) (-(17645419 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 - (-(17645419 / 1000000000 : ℝ))| ≤ (14692626551739 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 - (-(17645419 / 1000000000 : ℝ)))]

theorem thL_77_sin_r : (-17644576795391 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) ≤ (-141155438953 / 8000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (17645419 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((9988426295967378634662996739982942032977756683170770930133801928277446240003700307898926874327009413255932604358103398763569 / 566092800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(17645419 / 1000000000 : ℝ)) ∧ Real.sin (-(17645419 / 1000000000 : ℝ)) ≤ -((64028373692098580991429466281932566997570568710383538647989299226315250849535565419504715072219069225671 / 3628800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237) (-(17645419 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 - (-(17645419 / 1000000000 : ℝ))| ≤ (14692626551739 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 77) 237 - (-(17645419 / 1000000000 : ℝ)))]

theorem thL_77_cos : (141155438953 / 8000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 77) ∧ Real.cos (856993 / 10000 * Real.log 77) ≤ (17644576795391 / 1000000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_77_sin : (49992212508519 / 50000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 77) ∧ Real.sin (856993 / 10000 * Real.log 77) ≤ (999844397096647 / 1000000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_77 : (141155438953 / 8000000000000 : ℝ) ≤ cC 77 ∧ cC 77 ≤ (17644576795391 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_77_cos

theorem sCB_77 : (49992212508519 / 50000000000000 : ℝ) ≤ sC 77 ∧ sC 77 ≤ (999844397096647 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_77_sin

theorem thL_78_r_bounds : (-24131452919951581163 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 ≤ (-24131445480048418837 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_78
  have hl : (373366896719598117 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 78 ∧ 856993 / 10000 * Real.log 78 ≤ (373366896867584427 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_78_eq : (856993 / 10000 * Real.log 78) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 + π) + ((59 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_78_cos_r : (35431110978327 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) ≤ (885777923256573 / 1000000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(60328623 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) (-(60328623 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 - (-(60328623 / 125000000 : ℝ))| ≤ (3719951581163 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 - (-(60328623 / 125000000 : ℝ)))]

theorem thL_78_sin_r : (-92821909381763 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) ≤ (-232054699055369 / 500000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (60328623 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((21633393223504176119446818423306646958093483905247546214706983851058958473651234712683832972657817300596408738581 / 46612694859504699707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(60328623 / 125000000 : ℝ)) ∧ Real.sin (-(60328623 / 125000000 : ℝ)) ≤ -((26625714736619814264428135083406934603851674582631300325831140455947036460119827938906889568033 / 57369470596313476562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238) (-(60328623 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 - (-(60328623 / 125000000 : ℝ))| ≤ (3719951581163 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 78) 238 - (-(60328623 / 125000000 : ℝ)))]

theorem thL_78_cos : (-885777923256573 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 78) ∧ Real.cos (856993 / 10000 * Real.log 78) ≤ (-35431110978327 / 40000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_78_sin : (232054699055369 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 78) ∧ Real.sin (856993 / 10000 * Real.log 78) ≤ (92821909381763 / 200000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_78 : (-885777923256573 / 1000000000000000 : ℝ) ≤ cC 78 ∧ cC 78 ≤ (-35431110978327 / 40000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_78_cos

theorem sCB_78 : (232054699055369 / 500000000000000 : ℝ) ≤ sC 78 ∧ sC 78 ≤ (92821909381763 / 200000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_78_sin

theorem thL_79_r_bounds : (60909653386102862207 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 ≤ (60909668413897137793 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_79
  have hl : (46807327788880803 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 79 ∧ 856993 / 10000 * Real.log 79 ≤ (187229311230414823 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_79_eq : (856993 / 10000 * Real.log 79) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 + π) + ((59 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_79_cos_r : (820165131474709 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) ≤ (51260330109881 / 62500000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (609096609 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) (609096609 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 - (609096609 / 1000000000 : ℝ)| ≤ (7513897137793 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 - (609096609 / 1000000000 : ℝ))]

theorem thL_79_sin_r : (572126688656549 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) ≤ (143031709733687 / 250000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (609096609 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238) (609096609 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 - (609096609 / 1000000000 : ℝ)| ≤ (7513897137793 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 79) 238 - (609096609 / 1000000000 : ℝ))]

theorem thL_79_cos : (-51260330109881 / 62500000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 79) ∧ Real.cos (856993 / 10000 * Real.log 79) ≤ (-820165131474709 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_79_sin : (-143031709733687 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 79) ∧ Real.sin (856993 / 10000 * Real.log 79) ≤ (-572126688656549 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_79 : (-51260330109881 / 62500000000000 : ℝ) ≤ cC 79 ∧ cC 79 ≤ (-820165131474709 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_79_cos

theorem sCB_79 : (-143031709733687 / 250000000000000 : ℝ) ≤ sC 79 ∧ sC 79 ≤ (-572126688656549 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_79_sin

theorem thL_81_r_bounds : (-487377528455189231 / 1250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 ≤ (-487377336544810769 / 1250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_81
  have hl : (188300608204242453 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 81 ∧ 856993 / 10000 * Real.log 81 ≤ (18830060828076967 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_81_eq : (856993 / 10000 * Real.log 81) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_81_cos_r : (924946257641623 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) ≤ (28904575349061 / 31250000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(194950973 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) (-(194950973 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 - (-(194950973 / 500000000 : ℝ))| ≤ (95955189231 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 - (-(194950973 / 500000000 : ℝ)))]

theorem thL_81_sin_r : (-190048899513413 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) ≤ (-190048822749261 / 500000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (194950973 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((41275049221580208436718268203667894967939778797041759775306905235711789613817502003447674580405068580154895051292554563819 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(194950973 / 500000000 : ℝ)) ∧ Real.sin (-(194950973 / 500000000 : ℝ)) ≤ -((1058334595425131397533686141652165812135428087683554450485333269643056035260263662747632456104394623789 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240) (-(194950973 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 - (-(194950973 / 500000000 : ℝ))| ≤ (95955189231 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 81) 240 - (-(194950973 / 500000000 : ℝ)))]

theorem thL_81_cos : (924946257641623 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 81) ∧ Real.cos (856993 / 10000 * Real.log 81) ≤ (28904575349061 / 31250000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_81_sin : (-190048899513413 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 81) ∧ Real.sin (856993 / 10000 * Real.log 81) ≤ (-190048822749261 / 500000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_81 : (924946257641623 / 1000000000000000 : ℝ) ≤ cC 81 ∧ cC 81 ≤ (28904575349061 / 31250000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_81_cos

theorem sCB_81 : (-190048899513413 / 500000000000000 : ℝ) ≤ sC 81 ∧ sC 81 ≤ (-190048822749261 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_81_sin

theorem thL_82_r_bounds : (1654090808663660959 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 ≤ (1654091196336339041 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_82
  have hl : (377652754754240653 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 82 ∧ 856993 / 10000 * Real.log 82 ≤ (188826377454392371 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_82_eq : (856993 / 10000 * Real.log 82) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_82_cos_r : (788987791642647 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) ≤ (197246986681603 / 250000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (661636401 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) (661636401 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 - (661636401 / 1000000000 : ℝ)| ≤ (193836339041 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 - (661636401 / 1000000000 : ℝ))]

theorem thL_82_sin_r : (614408697034319 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) ≤ (614408852104139 / 1000000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (661636401 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240) (661636401 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 - (661636401 / 1000000000 : ℝ)| ≤ (193836339041 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 82) 240 - (661636401 / 1000000000 : ℝ))]

theorem thL_82_cos : (788987791642647 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 82) ∧ Real.cos (856993 / 10000 * Real.log 82) ≤ (197246986681603 / 250000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_82_sin : (614408697034319 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 82) ∧ Real.sin (856993 / 10000 * Real.log 82) ≤ (614408852104139 / 1000000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_82 : (788987791642647 / 1000000000000000 : ℝ) ≤ cC 82 ∧ cC 82 ≤ (197246986681603 / 250000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_82_cos

theorem sCB_82 : (614408697034319 / 1000000000000000 : ℝ) ≤ sC 82 ∧ sC 82 ≤ (614408852104139 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_82_sin

theorem thL_83_r_bounds : (12963210899453623443 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 ≤ (12963226500546376557 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_83
  have hl : (378691546866629927 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 83 ∧ 856993 / 10000 * Real.log 83 ≤ (378691547022575549 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_83_eq : (856993 / 10000 * Real.log 83) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 + π / 2) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_83_cos_r : (123951178719841 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) ≤ (123951198221207 / 125000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (129632187 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) (129632187 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 - (129632187 / 1000000000 : ℝ)| ≤ (7800546376557 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 - (129632187 / 1000000000 : ℝ))]

theorem thL_83_sin_r : (129269346498773 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) ≤ (129269502509701 / 1000000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (129632187 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241) (129632187 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 - (129632187 / 1000000000 : ℝ)| ≤ (7800546376557 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 83) 241 - (129632187 / 1000000000 : ℝ))]

theorem thL_83_cos : (-129269502509701 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 83) ∧ Real.cos (856993 / 10000 * Real.log 83) ≤ (-129269346498773 / 1000000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_83_sin : (123951178719841 / 125000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 83) ∧ Real.sin (856993 / 10000 * Real.log 83) ≤ (123951198221207 / 125000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_83 : (-129269502509701 / 1000000000000000 : ℝ) ≤ cC 83 ∧ cC 83 ≤ (-129269346498773 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_83_cos

theorem sCB_83 : (123951178719841 / 125000000000000 : ℝ) ≤ sC 83 ∧ sC 83 ≤ (123951198221207 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_83_sin

theorem thL_84_r_bounds : (-20740651431802407317 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 ≤ (-20740643568197592683 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_84
  have hl : (379717898055735813 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 84 ∧ 856993 / 10000 * Real.log 84 ≤ (37971789821300103 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_84_eq : (856993 / 10000 * Real.log 84) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 + π) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_84_cos_r : (915191642525659 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) ≤ (915191799797811 / 1000000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(8296259 / 20000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) (-(8296259 / 20000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 - (-(8296259 / 20000000 : ℝ))| ≤ (3931802407317 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 - (-(8296259 / 20000000 : ℝ)))]

theorem thL_84_sin_r : (-20150941473079 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) ≤ (-403018672189481 / 1000000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (8296259 / 20000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((205586935331274962439465691481867482334496560986146910570817851743648229540171112121847084779643009154579 / 510117543936000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(8296259 / 20000000 : ℝ)) ∧ Real.sin (-(8296259 / 20000000 : ℝ)) ≤ -((3294662425180674365973529425220691685703964123619939948285346611276825417404689687619141 / 8174960640000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242) (-(8296259 / 20000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 - (-(8296259 / 20000000 : ℝ))| ≤ (3931802407317 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 84) 242 - (-(8296259 / 20000000 : ℝ)))]

theorem thL_84_cos : (-915191799797811 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 84) ∧ Real.cos (856993 / 10000 * Real.log 84) ≤ (-915191642525659 / 1000000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_84_sin : (403018672189481 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 84) ∧ Real.sin (856993 / 10000 * Real.log 84) ≤ (20150941473079 / 50000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_84 : (-915191799797811 / 1000000000000000 : ℝ) ≤ cC 84 ∧ cC 84 ≤ (-915191642525659 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_84_cos

theorem sCB_84 : (403018672189481 / 1000000000000000 : ℝ) ≤ sC 84 ∧ sC 84 ≤ (20150941473079 / 50000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_84_sin

theorem thL_86_r_bounds : (6187560159651705179 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 ≤ (6187592240348294821 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_86
  have hl : (381734445211958137 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 86 ∧ 856993 / 10000 * Real.log 86 ≤ (381734445371638999 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_86_eq : (856993 / 10000 * Real.log 86) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 + π + π / 2) + ((60 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_86_cos_r : (999521381729191 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) ≤ (39980861685307 / 40000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (30937881 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) (30937881 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 - (30937881 / 1000000000 : ℝ)| ≤ (16040348294821 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 - (30937881 / 1000000000 : ℝ))]

theorem thL_86_sin_r : (3093286565619 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) ≤ (15466513029837 / 500000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (30937881 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243) (30937881 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 - (30937881 / 1000000000 : ℝ)| ≤ (16040348294821 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 86) 243 - (30937881 / 1000000000 : ℝ))]

theorem thL_86_cos : (3093286565619 / 100000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 86) ∧ Real.cos (856993 / 10000 * Real.log 86) ≤ (15466513029837 / 500000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_86_sin : (-39980861685307 / 40000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 86) ∧ Real.sin (856993 / 10000 * Real.log 86) ≤ (-999521381729191 / 1000000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_86 : (3093286565619 / 100000000000000 : ℝ) ≤ cC 86 ∧ cC 86 ≤ (15466513029837 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_86_cos

theorem sCB_86 : (-39980861685307 / 40000000000000 : ℝ) ≤ sC 86 ∧ sC 86 ≤ (-999521381729191 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_86_sin

theorem thL_87_r_bounds : (-13727603494140772697 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 ≤ (-13727599455859227303 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_87
  have hl : (95681299899733363 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 87 ∧ 856993 / 10000 * Real.log 87 ≤ (191362599879860203 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_87_eq : (856993 / 10000 * Real.log 87) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_87_cos_r : (426496197991579 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) ≤ (85299255751599 / 100000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(549104059 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) (-(549104059 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 - (-(549104059 / 1000000000 : ℝ))| ≤ (2019140772697 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 - (-(549104059 / 1000000000 : ℝ)))]

theorem thL_87_sin_r : (-130480822085617 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) ≤ (-521923126811139 / 1000000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (549104059 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((464289524226239866167058526788431265314348269944113943608012271398396147747058326083416333420352697840039726725021173340343997 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(549104059 / 1000000000 : ℝ)) ∧ Real.sin (-(549104059 / 1000000000 : ℝ)) ≤ -((2976214898885775165709624345566213058688246787666426825343639302400959087560995915059481526359926934344763 / 5702400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244) (-(549104059 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 - (-(549104059 / 1000000000 : ℝ))| ≤ (2019140772697 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 87) 244 - (-(549104059 / 1000000000 : ℝ)))]

theorem thL_87_cos : (426496197991579 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 87) ∧ Real.cos (856993 / 10000 * Real.log 87) ≤ (85299255751599 / 100000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_87_sin : (-130480822085617 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 87) ∧ Real.sin (856993 / 10000 * Real.log 87) ≤ (-521923126811139 / 1000000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_87 : (426496197991579 / 500000000000000 : ℝ) ≤ cC 87 ∧ cC 87 ≤ (85299255751599 / 100000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_87_cos

theorem sCB_87 : (-130480822085617 / 250000000000000 : ℝ) ≤ sC 87 ∧ sC 87 ≤ (-521923126811139 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_87_sin

theorem thL_88_r_bounds : (21516354638360495333 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 ≤ (21516362761639504667 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_88
  have hl : (76740926166144397 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 88 ∧ 856993 / 10000 * Real.log 88 ≤ (383704630992553253 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_88_eq : (856993 / 10000 * Real.log 88) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_88_cos_r : (908829230507399 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) ≤ (113603674121633 / 125000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (215163587 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) (215163587 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 - (215163587 / 500000000 : ℝ)| ≤ (4061639504667 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 - (215163587 / 500000000 : ℝ))]

theorem thL_88_sin_r : (208584044419891 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) ≤ (208584125652683 / 500000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (215163587 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244) (215163587 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 - (215163587 / 500000000 : ℝ)| ≤ (4061639504667 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 88) 244 - (215163587 / 500000000 : ℝ))]

theorem thL_88_cos : (908829230507399 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 88) ∧ Real.cos (856993 / 10000 * Real.log 88) ≤ (113603674121633 / 125000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_88_sin : (208584044419891 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 88) ∧ Real.sin (856993 / 10000 * Real.log 88) ≤ (208584125652683 / 500000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_88 : (908829230507399 / 1000000000000000 : ℝ) ≤ cC 88 ∧ cC 88 ≤ (113603674121633 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_88_cos

theorem sCB_88 : (208584044419891 / 500000000000000 : ℝ) ≤ sC 88 ∧ sC 88 ≤ (208584125652683 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_88_sin

theorem thL_89_r_bounds : (-6884210346063988503 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 ≤ (-6884203813936011497 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_89
  have hl : (48084124350762259 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 89 ∧ 856993 / 10000 * Real.log 89 ≤ (384672994968915971 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_89_eq : (856993 / 10000 * Real.log 89) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 + π / 2) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_89_cos_r : (492613171394587 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) ≤ (492613253046187 / 500000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(172105177 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) (-(172105177 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 - (-(172105177 / 1000000000 : ℝ))| ≤ (3266063988503 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 - (-(172105177 / 1000000000 : ℝ)))]

theorem thL_89_sin_r : (-21407110585051 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) ≤ (-21407090172151 / 125000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (172105177 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1066419674601890411949931242452681435250295097820621889549617127267465664503842686392409287563681266118712121009113347368292217 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(172105177 / 1000000000 : ℝ)) ∧ Real.sin (-(172105177 / 1000000000 : ℝ)) ≤ -((6836023555140323152780131180620707204060462881062356554300922315765755553296860432011064019740948868891127 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245) (-(172105177 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 - (-(172105177 / 1000000000 : ℝ))| ≤ (3266063988503 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 89) 245 - (-(172105177 / 1000000000 : ℝ)))]

theorem thL_89_cos : (21407090172151 / 125000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 89) ∧ Real.cos (856993 / 10000 * Real.log 89) ≤ (21407110585051 / 125000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_89_sin : (492613171394587 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 89) ∧ Real.sin (856993 / 10000 * Real.log 89) ≤ (492613253046187 / 500000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_89 : (21407090172151 / 125000000000000 : ℝ) ≤ cC 89 ∧ cC 89 ≤ (21407110585051 / 125000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_89_cos

theorem sCB_89 : (492613171394587 / 500000000000000 : ℝ) ≤ sC 89 ∧ sC 89 ≤ (492613253046187 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_89_sin

theorem thL_91_r_bounds : (16160568044441166819 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 ≤ (16160584555558833181 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_91
  have hl : (19328875103599449 / 50000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 91 ∧ 856993 / 10000 * Real.log 91 ≤ (96644375559155483 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_91_eq : (856993 / 10000 * Real.log 91) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 + π) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_91_cos_r : (986970100878503 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) ≤ (12337128324871 / 12500000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (161605763 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) (161605763 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 - (161605763 / 1000000000 : ℝ)| ≤ (8255558833181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 - (161605763 / 1000000000 : ℝ))]

theorem thL_91_sin_r : (160903171022689 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) ≤ (160903336133867 / 1000000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (161605763 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246) (161605763 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 - (161605763 / 1000000000 : ℝ)| ≤ (8255558833181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 91) 246 - (161605763 / 1000000000 : ℝ))]

theorem thL_91_cos : (-12337128324871 / 12500000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 91) ∧ Real.cos (856993 / 10000 * Real.log 91) ≤ (-986970100878503 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_91_sin : (-160903336133867 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 91) ∧ Real.sin (856993 / 10000 * Real.log 91) ≤ (-160903171022689 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_91 : (-12337128324871 / 12500000000000 : ℝ) ≤ cC 91 ∧ cC 91 ≤ (-986970100878503 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_91_cos

theorem sCB_91 : (-160903336133867 / 1000000000000000 : ℝ) ≤ sC 91 ∧ sC 91 ≤ (-160903171022689 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_91_sin

theorem thL_92_r_bounds : (-47257695320992205019 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 ≤ (-47257678679007794981 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_92
  have hl : (77502823153216257 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 92 ∧ 856993 / 10000 * Real.log 92 ≤ (387514115931549387 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_92_eq : (856993 / 10000 * Real.log 92) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 + π + π / 2) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_92_cos_r : (89039821707397 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) ≤ (445199191747037 / 500000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(47257687 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) (-(47257687 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 - (-(47257687 / 100000000 : ℝ))| ≤ (8320992205019 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 - (-(47257687 / 100000000 : ℝ)))]

theorem thL_92_sin_r : (-455182317980893 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) ≤ (-455182151561039 / 1000000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (47257687 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40491846338704556119943340310614139722329666183630939122762210176965974432841717575039706736886804502341811295121 / 88957440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(47257687 / 100000000 : ℝ)) ∧ Real.sin (-(47257687 / 100000000 : ℝ)) ≤ -((181694182289055147141774530806089317539662171913975117914575386368254783852183026595852172383737 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247) (-(47257687 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 - (-(47257687 / 100000000 : ℝ))| ≤ (8320992205019 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 92) 247 - (-(47257687 / 100000000 : ℝ)))]

theorem thL_92_cos : (-455182317980893 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 92) ∧ Real.cos (856993 / 10000 * Real.log 92) ≤ (-455182151561039 / 1000000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_92_sin : (-445199191747037 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 92) ∧ Real.sin (856993 / 10000 * Real.log 92) ≤ (-89039821707397 / 100000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_92 : (-455182317980893 / 1000000000000000 : ℝ) ≤ cC 92 ∧ cC 92 ≤ (-455182151561039 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_92_cos

theorem sCB_92 : (-445199191747037 / 500000000000000 : ℝ) ≤ sC 92 ∧ sC 92 ≤ (-89039821707397 / 100000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_92_sin

theorem thL_93_r_bounds : (45391098966729194981 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 ≤ (45391115633270805019 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_93
  have hl : (194220301854206549 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 93 ∧ 856993 / 10000 * Real.log 93 ≤ (388440603874672173 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_93_eq : (856993 / 10000 * Real.log 93) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 + π + π / 2) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_93_cos_r : (898738954568257 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) ≤ (449369560616917 / 500000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (453911073 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) (453911073 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 - (453911073 / 1000000000 : ℝ)| ≤ (8333270805019 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 - (453911073 / 1000000000 : ℝ))]

theorem thL_93_sin_r : (219241914715491 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) ≤ (87696799219281 / 200000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (453911073 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247) (453911073 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 - (453911073 / 1000000000 : ℝ)| ≤ (8333270805019 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 93) 247 - (453911073 / 1000000000 : ℝ))]

theorem thL_93_cos : (219241914715491 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 93) ∧ Real.cos (856993 / 10000 * Real.log 93) ≤ (87696799219281 / 200000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_93_sin : (-449369560616917 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 93) ∧ Real.sin (856993 / 10000 * Real.log 93) ≤ (-898738954568257 / 1000000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_93 : (219241914715491 / 500000000000000 : ℝ) ≤ cC 93 ∧ cC 93 ≤ (87696799219281 / 200000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_93_cos

theorem sCB_93 : (-449369560616917 / 500000000000000 : ℝ) ≤ sC 93 ∧ sC 93 ≤ (-898738954568257 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_93_sin

theorem thL_94_r_bounds : (-2503831834254817887 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 ≤ (-2503829740745182113 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_94
  have hl : (48669647812358263 / 125000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 94 ∧ 856993 / 10000 * Real.log 94 ≤ (389357182665874747 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_94_eq : (856993 / 10000 * Real.log 94) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_94_cos_r : (98000556327897 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) ≤ (490002865379871 / 500000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(200306463 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) (-(200306463 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 - (-(200306463 / 1000000000 : ℝ))| ≤ (1046754817887 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 - (-(200306463 / 1000000000 : ℝ)))]

theorem thL_94_sin_r : (-99484879672461 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) ≤ (-3979391837283 / 20000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (200306463 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((728388188453084034405649694354993621798948819582117672053585337691413768705128361315008717698952326626425214096842596534003 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(200306463 / 1000000000 : ℝ)) ∧ Real.sin (-(200306463 / 1000000000 : ℝ)) ≤ -((14007465162559308344507085325493362076407581772690737316005768733287657702286123457540336044672329374439 / 70400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248) (-(200306463 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 - (-(200306463 / 1000000000 : ℝ))| ≤ (1046754817887 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 94) 248 - (-(200306463 / 1000000000 : ℝ)))]

theorem thL_94_cos : (98000556327897 / 100000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 94) ∧ Real.cos (856993 / 10000 * Real.log 94) ≤ (490002865379871 / 500000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_94_sin : (-99484879672461 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 94) ∧ Real.sin (856993 / 10000 * Real.log 94) ≤ (-3979391837283 / 20000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_94 : (98000556327897 / 100000000000000 : ℝ) ≤ cC 94 ∧ cC 94 ≤ (490002865379871 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_94_cos

theorem sCB_94 : (-99484879672461 / 500000000000000 : ℝ) ≤ sC 94 ∧ sC 94 ≤ (-3979391837283 / 20000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_94_sin

theorem thL_96_r_bounds : (6631911505526762097 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 ≤ (6631945294473237903 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_96
  have hl : (97790361232364223 / 250000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 96 ∧ 856993 / 10000 * Real.log 96 ≤ (391161445097850573 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_96_eq : (856993 / 10000 * Real.log 96) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 + π / 2) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_96_cos_r : (499725092486757 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) ≤ (124931294239781 / 125000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (16579821 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) (16579821 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 - (16579821 / 500000000 : ℝ)| ≤ (16894473237903 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 - (16579821 / 500000000 : ℝ))]

theorem thL_96_sin_r : (33153481015459 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) ≤ (129506445157 / 3906250000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (16579821 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249) (16579821 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 - (16579821 / 500000000 : ℝ)| ≤ (16894473237903 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 96) 249 - (16579821 / 500000000 : ℝ))]

theorem thL_96_cos : (-129506445157 / 3906250000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 96) ∧ Real.cos (856993 / 10000 * Real.log 96) ≤ (-33153481015459 / 1000000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_96_sin : (499725092486757 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 96) ∧ Real.sin (856993 / 10000 * Real.log 96) ≤ (124931294239781 / 125000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_96 : (-129506445157 / 3906250000000 : ℝ) ≤ cC 96 ∧ cC 96 ≤ (-33153481015459 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_96_cos

theorem sCB_96 : (499725092486757 / 500000000000000 : ℝ) ≤ sC 96 ∧ sC 96 ≤ (124931294239781 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_96_sin

theorem thL_97_r_bounds : (-259821269853559677 / 400000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 ≤ (-259821202146440323 / 400000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_97
  have hl : (196024764262162147 / 500000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 97 ∧ 856993 / 10000 * Real.log 97 ≤ (196024764346679027 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_97_eq : (856993 / 10000 * Real.log 97) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 + π) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_97_cos_r : (796354098250661 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) ≤ (398177133765119 / 500000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(64955309 / 100000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) (-(64955309 / 100000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 - (-(64955309 / 100000000 : ℝ))| ≤ (33853559677 / 400000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 - (-(64955309 / 100000000 : ℝ)))]

theorem thL_97_sin_r : (-302415326067437 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) ≤ (-302415241433243 / 500000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (64955309 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((53804178918633869326936534545985727645687822256091963654523913592443099649453682033189423624234726796447747842747 / 88957440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(64955309 / 100000000 : ℝ)) ∧ Real.sin (-(64955309 / 100000000 : ℝ)) ≤ -((241429007967994010088230331558473883601883417769350467182700416280273134764038801723099358362091 / 399168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250) (-(64955309 / 100000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 - (-(64955309 / 100000000 : ℝ))| ≤ (33853559677 / 400000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 97) 250 - (-(64955309 / 100000000 : ℝ)))]

theorem thL_97_cos : (-398177133765119 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 97) ∧ Real.cos (856993 / 10000 * Real.log 97) ≤ (-796354098250661 / 1000000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_97_sin : (302415241433243 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 97) ∧ Real.sin (856993 / 10000 * Real.log 97) ≤ (302415326067437 / 500000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_97 : (-398177133765119 / 500000000000000 : ℝ) ≤ cC 97 ∧ cC 97 ≤ (-796354098250661 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_97_cos

theorem sCB_97 : (302415241433243 / 500000000000000 : ℝ) ≤ sC 97 ∧ sC 97 ≤ (302415326067437 / 500000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_97_sin

theorem thL_98_r_bounds : (91768684040710723 / 400000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 ≤ (91768751959289277 / 400000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_98
  have hl : (3929285034089807 / 10000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 98 ∧ 856993 / 10000 * Real.log 98 ≤ (196464251789311189 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_98_eq : (856993 / 10000 * Real.log 98) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 + π) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_98_cos_r : (486898982542617 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) ≤ (486899067440841 / 500000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (45884359 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) (45884359 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 - (45884359 / 200000000 : ℝ)| ≤ (33959289277 / 400000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 - (45884359 / 200000000 : ℝ))]

theorem thL_98_sin_r : (56853605445393 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) ≤ (227414591578019 / 1000000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (45884359 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250) (45884359 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 - (45884359 / 200000000 : ℝ)| ≤ (33959289277 / 400000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 98) 250 - (45884359 / 200000000 : ℝ))]

theorem thL_98_cos : (-486899067440841 / 500000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 98) ∧ Real.cos (856993 / 10000 * Real.log 98) ≤ (-486898982542617 / 500000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_98_sin : (-227414591578019 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 98) ∧ Real.sin (856993 / 10000 * Real.log 98) ≤ (-56853605445393 / 250000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_98 : (-486899067440841 / 500000000000000 : ℝ) ≤ cC 98 ∧ cC 98 ≤ (-486898982542617 / 500000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_98_cos

theorem sCB_98 : (-227414591578019 / 1000000000000000 : ℝ) ≤ sC 98 ∧ sC 98 ≤ (-56853605445393 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_98_sin

theorem thL_99_r_bounds : (-47132348937178957327 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 ≤ (-47132331862821042673 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_99
  have hl : (393798554536671483 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 99 ∧ 856993 / 10000 * Real.log 99 ≤ (393798554706890841 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_99_eq : (856993 / 10000 * Real.log 99) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 + π + π / 2) + ((62 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_99_cos_r : (890968070731213 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) ≤ (222742060368761 / 250000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(117830851 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) (-(117830851 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 - (-(117830851 / 250000000 : ℝ))| ≤ (8537178957327 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 - (-(117830851 / 250000000 : ℝ)))]

theorem thL_99_sin_r : (-454065878853273 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) ≤ (-454065708109683 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (117830851 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((42132692643667705529445578304471858397755346340853939536323206191674148802663003844234651969980852914556888830992156051 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(117830851 / 250000000 : ℝ)) ∧ Real.sin (-(117830851 / 250000000 : ℝ)) ≤ -((4321301809606857587832545695327495079444376316304721129475814987530960338500290653396996228915998149 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251) (-(117830851 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 - (-(117830851 / 250000000 : ℝ))| ≤ (8537178957327 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 99) 251 - (-(117830851 / 250000000 : ℝ)))]

theorem thL_99_cos : (-454065878853273 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 99) ∧ Real.cos (856993 / 10000 * Real.log 99) ≤ (-454065708109683 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_99_sin : (-222742060368761 / 250000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 99) ∧ Real.sin (856993 / 10000 * Real.log 99) ≤ (-890968070731213 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_99 : (-454065878853273 / 1000000000000000 : ℝ) ≤ cC 99 ∧ cC 99 ≤ (-454065708109683 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_99_cos

theorem sCB_99 : (-222742060368761 / 250000000000000 : ℝ) ≤ sC 99 ∧ sC 99 ≤ (-890968070731213 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_99_sin

theorem thL_101_r_bounds : (-8201916993227848851 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 ≤ (-8201912706772151149 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_101
  have hl : (79102519534550407 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 101 ∧ 856993 / 10000 * Real.log 101 ≤ (197756298922021531 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_101_eq : (856993 / 10000 * Real.log 101) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_101_cos_r : (946663773783189 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) ≤ (946663945241421 / 1000000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(164038297 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) (-(164038297 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 - (-(164038297 / 500000000 : ℝ))| ≤ (2143227848851 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 - (-(164038297 / 500000000 : ℝ)))]

theorem thL_101_sin_r : (-161111446164621 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) ≤ (-322222720871013 / 1000000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (164038297 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((244932631705733926354502926258702568012023357172398718880488449638273134297821181122918894629453196803129835121073632139577 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(164038297 / 500000000 : ℝ)) ∧ Real.sin (-(164038297 / 500000000 : ℝ)) ≤ -((6280323889890611899568046336702045026296724051993296501151366742182698888885624657537528279461344683447 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252) (-(164038297 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 - (-(164038297 / 500000000 : ℝ))| ≤ (2143227848851 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 101) 252 - (-(164038297 / 500000000 : ℝ)))]

theorem thL_101_cos : (946663773783189 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 101) ∧ Real.cos (856993 / 10000 * Real.log 101) ≤ (946663945241421 / 1000000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_101_sin : (-161111446164621 / 500000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 101) ∧ Real.sin (856993 / 10000 * Real.log 101) ≤ (-322222720871013 / 1000000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_101 : (946663773783189 / 1000000000000000 : ℝ) ≤ cC 101 ∧ cC 101 ≤ (946663945241421 / 1000000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_101_cos

theorem sCB_101 : (-161111446164621 / 500000000000000 : ℝ) ≤ sC 101 ∧ sC 101 ≤ (-322222720871013 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_101_sin

theorem thL_102_r_bounds : (25812911444861597639 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 ≤ (25812920055138402361 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_102
  have hl : (19817846629060559 / 50000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 102 ∧ 856993 / 10000 * Real.log 102 ≤ (49544616594124927 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_102_eq : (856993 / 10000 * Real.log 102) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_102_cos_r : (869672183377747 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) ≤ (27177261112001 / 31250000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (103251663 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) (103251663 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 - (103251663 / 200000000 : ℝ)| ≤ (4305138402361 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 - (103251663 / 200000000 : ℝ))]

theorem thL_102_sin_r : (493629475102069 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) ≤ (123407411826909 / 250000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (103251663 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252) (103251663 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 - (103251663 / 200000000 : ℝ)| ≤ (4305138402361 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 102) 252 - (103251663 / 200000000 : ℝ))]

theorem thL_102_cos : (869672183377747 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 102) ∧ Real.cos (856993 / 10000 * Real.log 102) ≤ (27177261112001 / 31250000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_102_sin : (493629475102069 / 1000000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 102) ∧ Real.sin (856993 / 10000 * Real.log 102) ≤ (123407411826909 / 250000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_102 : (869672183377747 / 1000000000000000 : ℝ) ≤ cC 102 ∧ cC 102 ≤ (27177261112001 / 31250000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_102_cos

theorem sCB_102 : (493629475102069 / 1000000000000000 : ℝ) ≤ sC 102 ∧ sC 102 ≤ (123407411826909 / 250000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_102_sin

theorem thL_103_r_bounds : (-43688146899411133291 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 ≤ (-43688112300588866709 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_103
  have hl : (397193029944611789 / 1000000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 103 ∧ 856993 / 10000 * Real.log 103 ≤ (198596515058436723 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_103_eq : (856993 / 10000 * Real.log 103) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 + π / 2) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_103_cos_r : (122029559126173 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) ≤ (976236646003497 / 1000000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(27305081 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) (-(27305081 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 - (-(27305081 / 125000000 : ℝ))| ≤ (17299411133291 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 - (-(27305081 / 125000000 : ℝ)))]

theorem thL_103_sin_r : (-5417691930851 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) ≤ (-216707504239927 / 1000000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (27305081 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2454621926585029627498476948585715054539760054647877940550880587348478137417982444129842886117547635936423186297241 / 11326884850859642028808593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(27305081 / 125000000 : ℝ)) ∧ Real.sin (-(27305081 / 125000000 : ℝ)) ≤ -((1007024380137448050382999206866701568057863667992442751921592205659716274852174531615284989412119 / 4646927118301391601562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253) (-(27305081 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 - (-(27305081 / 125000000 : ℝ))| ≤ (17299411133291 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 103) 253 - (-(27305081 / 125000000 : ℝ)))]

theorem thL_103_cos : (216707504239927 / 1000000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 103) ∧ Real.cos (856993 / 10000 * Real.log 103) ≤ (5417691930851 / 25000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_103_sin : (122029559126173 / 125000000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 103) ∧ Real.sin (856993 / 10000 * Real.log 103) ≤ (976236646003497 / 1000000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_103 : (216707504239927 / 1000000000000000 : ℝ) ≤ cC 103 ∧ cC 103 ≤ (5417691930851 / 25000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_103_cos

theorem sCB_103 : (122029559126173 / 125000000000000 : ℝ) ≤ sC 103 ∧ sC 103 ≤ (976236646003497 / 1000000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_103_sin

theorem thL_104_r_bounds : (121915653442192066709 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 ∧ PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 ≤ (121915688157807933291 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_104
  have hl : (79604209789263961 / 200000000000000 : ℝ) ≤ 856993 / 10000 * Real.log 104 ∧ 856993 / 10000 * Real.log 104 ≤ (398021049119032451 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_104_eq : (856993 / 10000 * Real.log 104) = (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 + π / 2) + ((63 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_104_cos_r : (51243087841011 / 62500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) ∧ Real.cos (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) ≤ (102486197379969 / 125000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (304789177 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) (304789177 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 - (304789177 / 500000000 : ℝ)| ≤ (17357807933291 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 - (304789177 / 500000000 : ℝ))]

theorem thL_104_sin_r : (143130430272393 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) ∧ Real.sin (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) ≤ (57252189466791 / 100000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (304789177 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253) (304789177 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 - (304789177 / 500000000 : ℝ)| ≤ (17357807933291 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (856993 / 10000 * Real.log 104) 253 - (304789177 / 500000000 : ℝ))]

theorem thL_104_cos : (-57252189466791 / 100000000000000 : ℝ) ≤ Real.cos (856993 / 10000 * Real.log 104) ∧ Real.cos (856993 / 10000 * Real.log 104) ≤ (-143130430272393 / 250000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_104_sin : (51243087841011 / 62500000000000 : ℝ) ≤ Real.sin (856993 / 10000 * Real.log 104) ∧ Real.sin (856993 / 10000 * Real.log 104) ≤ (102486197379969 / 125000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_104 : (-57252189466791 / 100000000000000 : ℝ) ≤ cC 104 ∧ cC 104 ≤ (-143130430272393 / 250000000000000 : ℝ) := by
  unfold cC
  simp only [Nat.cast_ofNat]
  exact thL_104_cos

theorem sCB_104 : (51243087841011 / 62500000000000 : ℝ) ≤ sC 104 ∧ sC 104 ≤ (102486197379969 / 125000000000000 : ℝ) := by
  unfold sC
  simp only [Nat.cast_ofNat]
  exact thL_104_sin

end PsiOmega.Locate

#print axioms PsiOmega.Locate.cCB_104
#print axioms PsiOmega.Locate.sCB_104
