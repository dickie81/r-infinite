import DHLocate4Exp

/-! # Generated (`gen_locate_zero.py 4`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 17670246 / 100000`, `n ∈ NS` (part 1 of 2: `2 ≤ n ≤ 104`)

Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by
`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/

open Real Finset

namespace PsiOmega.Locate.Z4

theorem thL_2_r_bounds : (-4130156105635830033 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 ≤ (-4130152494364169967 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_2
  have hl : (61240405964472789 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 2 ∧ 17670246 / 100000 * Real.log 2 ≤ (122480811964286071 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_2_eq : (17670246 / 100000 * Real.log 2) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 + π) + ((19 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_2_cos_r : (999147194451873 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) ≤ (999147230564591 / 1000000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(41301543 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) (-(41301543 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 - (-(41301543 / 1000000000 : ℝ))| ≤ (1805635830033 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 - (-(41301543 / 1000000000 : ℝ)))]

theorem thL_2_sin_r : (-20644909954497 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) ≤ (-10322445949069 / 250000000000000 : ℝ) := by
  have hr := thL_2_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (41301543 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((151153706622126619750227380656210595195192804117382072558679777072752257216811713363015779963977579104435855406572896211643 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(41301543 / 1000000000 : ℝ)) ∧ Real.sin (-(41301543 / 1000000000 : ℝ)) ≤ -((20347614352978583427915224238576332364587049641418846738370778181651814593621498575024950756248053354553 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78) (-(41301543 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 - (-(41301543 / 1000000000 : ℝ))| ≤ (1805635830033 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 2) 78 - (-(41301543 / 1000000000 : ℝ)))]

theorem thL_2_cos : (-999147230564591 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 2) ∧ Real.cos (17670246 / 100000 * Real.log 2) ≤ (-999147194451873 / 1000000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_2_sin : (10322445949069 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 2) ∧ Real.sin (17670246 / 100000 * Real.log 2) ≤ (20644909954497 / 500000000000000 : ℝ) := by
  have hc := thL_2_cos_r
  have hs := thL_2_sin_r
  rw [thL_2_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_2 : (-999147230564591 / 1000000000000000 : ℝ) ≤ cCG cZ 2 ∧ cCG cZ 2 ≤ (-999147194451873 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_cos

theorem sCB_2 : (10322445949069 / 250000000000000 : ℝ) ≤ sCG cZ 2 ∧ sCG cZ 2 ≤ (20644909954497 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_2_sin

theorem thL_3_r_bounds : (-16281263696502155387 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 ≤ (-16281262503497844613 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_3
  have hl : (97063746987511943 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 3 ∧ 17670246 / 100000 * Real.log 3 ≤ (194127494022427267 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_3_eq : (17670246 / 100000 * Real.log 3) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) + ((31 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_3_cos_r : (795326352287317 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) ≤ (397663200009821 / 500000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(162812631 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) (-(162812631 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 - (-(162812631 / 250000000 : ℝ))| ≤ (596502155387 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 - (-(162812631 / 250000000 : ℝ)))]

theorem thL_3_sin_r : (-303090739017229 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) ≤ (-151545357578419 / 250000000000000 : ℝ) := by
  have hr := thL_3_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (162812631 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((231471113444727343983946822837121573417007759426163142960076059653620384967111524724159469893945184652582675679497837 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(162812631 / 250000000 : ℝ)) ∧ Real.sin (-(162812631 / 250000000 : ℝ)) ≤ -((71221881059844581215666465314930163018303304787395451482154257644679752055198967546744609847604649 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124) (-(162812631 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 - (-(162812631 / 250000000 : ℝ))| ≤ (596502155387 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 3) 124 - (-(162812631 / 250000000 : ℝ)))]

theorem thL_3_cos : (795326352287317 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 3) ∧ Real.cos (17670246 / 100000 * Real.log 3) ≤ (397663200009821 / 500000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_3_sin : (-303090739017229 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 3) ∧ Real.sin (17670246 / 100000 * Real.log 3) ≤ (-151545357578419 / 250000000000000 : ℝ) := by
  have hc := thL_3_cos_r
  have hs := thL_3_sin_r
  rw [thL_3_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_3 : (795326352287317 / 1000000000000000 : ℝ) ≤ cCG cZ 3 ∧ cCG cZ 3 ≤ (397663200009821 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_cos

theorem sCB_3 : (-303090739017229 / 500000000000000 : ℝ) ≤ sCG cZ 3 ∧ sCG cZ 3 ≤ (-151545357578419 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_3_sin

theorem thL_4_r_bounds : (-2065077649729910003 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 ≤ (-2065076350270089997 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_4
  have hl : (9798464954994647 / 40000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 4 ∧ 17670246 / 100000 * Real.log 4 ≤ (244961623925993069 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_4_eq : (17670246 / 100000 * Real.log 4) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) + ((39 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_4_cos_r : (498295139515899 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) ≤ (62286895688137 / 62500000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(2065077 / 25000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) (-(2065077 / 25000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 - (-(2065077 / 25000000 : ℝ))| ≤ (649729910003 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 - (-(2065077 / 25000000 : ℝ)))]

theorem thL_4_sin_r : (-8250920086181 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) ≤ (-10313643610427 / 125000000000000 : ℝ) := by
  have hr := thL_4_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (2065077 / 25000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((450088958999012524423191716510158398541649477480272243677064888179474531002422554832389816743689906017 / 5455017089843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(2065077 / 25000000 : ℝ)) ∧ Real.sin (-(2065077 / 25000000 : ℝ)) ≤ -((13848891046123462289944135818094092184032170830593465544955934640825675245226040997381 / 167846679687500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156) (-(2065077 / 25000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 - (-(2065077 / 25000000 : ℝ))| ≤ (649729910003 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 4) 156 - (-(2065077 / 25000000 : ℝ)))]

theorem thL_4_cos : (498295139515899 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 4) ∧ Real.cos (17670246 / 100000 * Real.log 4) ≤ (62286895688137 / 62500000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_4_sin : (-8250920086181 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 4) ∧ Real.sin (17670246 / 100000 * Real.log 4) ≤ (-10313643610427 / 125000000000000 : ℝ) := by
  have hc := thL_4_cos_r
  have hs := thL_4_sin_r
  rw [thL_4_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_4 : (498295139515899 / 500000000000000 : ℝ) ≤ cCG cZ 4 ∧ cCG cZ 4 ≤ (62286895688137 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_cos

theorem sCB_4 : (-8250920086181 / 100000000000000 : ℝ) ≤ sCG cZ 4 ∧ sCG cZ 4 ≤ (-10313643610427 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_4_sin

theorem thL_6_r_bounds : (-69255209197235308547 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 ≤ (-69255202802764691453 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_6
  have hl : (79152076480149191 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 6 ∧ 17670246 / 100000 * Real.log 6 ≤ (158304152992187571 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_6_eq : (17670246 / 100000 * Real.log 6) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 + π) + ((50 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_6_cos_r : (153923798423257 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) ≤ (769619056086407 / 1000000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(34627603 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) (-(34627603 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 - (-(34627603 / 50000000 : ℝ))| ≤ (3197235308547 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 - (-(34627603 / 50000000 : ℝ)))]

theorem thL_6_sin_r : (-319251702638667 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) ≤ (-79812917666409 / 125000000000000 : ℝ) := by
  have hr := thL_6_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (34627603 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((6933548037179608948524451945277020325390724920392488711141021837726851762792790356254646044154667043504083589 / 10859062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(34627603 / 50000000 : ℝ)) ∧ Real.sin (-(34627603 / 50000000 : ℝ)) ≤ -((124448298102959857899240520360011785956453499075935678209389674233278158179810298695068746453 / 194906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202) (-(34627603 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 - (-(34627603 / 50000000 : ℝ))| ≤ (3197235308547 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 6) 202 - (-(34627603 / 50000000 : ℝ)))]

theorem thL_6_cos : (-769619056086407 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 6) ∧ Real.cos (17670246 / 100000 * Real.log 6) ≤ (-153923798423257 / 200000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_6_sin : (79812917666409 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 6) ∧ Real.sin (17670246 / 100000 * Real.log 6) ≤ (319251702638667 / 500000000000000 : ℝ) := by
  have hc := thL_6_cos_r
  have hs := thL_6_sin_r
  rw [thL_6_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_6 : (-769619056086407 / 1000000000000000 : ℝ) ≤ cCG cZ 6 ∧ cCG cZ 6 ≤ (-153923798423257 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_cos

theorem sCB_6 : (79812917666409 / 125000000000000 : ℝ) ≤ sCG cZ 6 ∧ sCG cZ 6 ≤ (319251702638667 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_6_sin

theorem thL_7_r_bounds : (-31457062270938922493 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 ≤ (-31457049329061077507 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_7
  have hl : (68769422051345533 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 7 ∧ 17670246 / 100000 * Real.log 7 ≤ (343847110320704411 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_7_eq : (17670246 / 100000 * Real.log 7) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 + π + π / 2) + ((54 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_7_cos_r : (987656117183661 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) ≤ (987656181893051 / 1000000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(157285279 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) (-(157285279 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 - (-(157285279 / 1000000000 : ℝ))| ≤ (6470938922493 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 - (-(157285279 / 1000000000 : ℝ)))]

theorem thL_7_sin_r : (-15663760855871 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) ≤ (-3915938596233 / 25000000000000 : ℝ) := by
  have hr := thL_7_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (157285279 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((139340777869140774374374748118956612754630835085133193112141212173342107810176240925236986858148266201874967403932251648180777 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(157285279 / 1000000000 : ℝ)) ∧ Real.sin (-(157285279 / 1000000000 : ℝ)) ≤ -((6252470801820419362721602170179403426364181790835247904291015161467747302929947032422875114269196736293921 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219) (-(157285279 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 - (-(157285279 / 1000000000 : ℝ))| ≤ (6470938922493 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 7) 219 - (-(157285279 / 1000000000 : ℝ)))]

theorem thL_7_cos : (-15663760855871 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 7) ∧ Real.cos (17670246 / 100000 * Real.log 7) ≤ (-3915938596233 / 25000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_7_sin : (-987656181893051 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 7) ∧ Real.sin (17670246 / 100000 * Real.log 7) ≤ (-987656117183661 / 1000000000000000 : ℝ) := by
  have hc := thL_7_cos_r
  have hs := thL_7_sin_r
  rw [thL_7_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_7 : (-15663760855871 / 100000000000000 : ℝ) ≤ cCG cZ 7 ∧ cCG cZ 7 ≤ (-3915938596233 / 25000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_cos

theorem sCB_7 : (-987656181893051 / 1000000000000000 : ℝ) ≤ sCG cZ 7 ∧ sCG cZ 7 ≤ (-987656117183661 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_7_sin

theorem thL_8_r_bounds : (-6195232544318005009 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 ≤ (-6195228855681994991 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_8
  have hl : (36744243581968151 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 8 ∧ 17670246 / 100000 * Real.log 8 ≤ (367442435892892169 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_8_eq : (17670246 / 100000 * Real.log 8) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 + π) + ((58 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_8_cos_r : (992333602018871 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) ≤ (992333675791593 / 1000000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(61952307 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) (-(61952307 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 - (-(61952307 / 500000000 : ℝ))| ≤ (1844318005009 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 - (-(61952307 / 500000000 : ℝ)))]

theorem thL_8_sin_r : (-61793928129129 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) ≤ (-123587782485537 / 1000000000000000 : ℝ) := by
  have hr := thL_8_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (61952307 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((386598147472716119364294146103205077591114741794574344041010643287954664006859408433373724278452270068166509948757268849 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(61952307 / 500000000 : ℝ)) ∧ Real.sin (-(61952307 / 500000000 : ℝ)) ≤ -((29738319036362778412575321326962689659230992063753380003050507242975287723426921488159516682246989797 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234) (-(61952307 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 - (-(61952307 / 500000000 : ℝ))| ≤ (1844318005009 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 8) 234 - (-(61952307 / 500000000 : ℝ)))]

theorem thL_8_cos : (-992333675791593 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 8) ∧ Real.cos (17670246 / 100000 * Real.log 8) ≤ (-992333602018871 / 1000000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_8_sin : (123587782485537 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 8) ∧ Real.sin (17670246 / 100000 * Real.log 8) ≤ (61793928129129 / 500000000000000 : ℝ) := by
  have hc := thL_8_cos_r
  have hs := thL_8_sin_r
  rw [thL_8_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_8 : (-992333675791593 / 1000000000000000 : ℝ) ≤ cCG cZ 8 ∧ cCG cZ 8 ≤ (-992333602018871 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_cos

theorem sCB_8 : (123587782485537 / 1000000000000000 : ℝ) ≤ sCG cZ 8 ∧ sCG cZ 8 ≤ (61793928129129 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_8_sin

theorem thL_9_r_bounds : (53659049552130609791 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 ≤ (53659064847869390209 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_9
  have hl : (194127493983050059 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 9 ∧ 17670246 / 100000 * Real.log 9 ≤ (194127494021150617 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_9_eq : (17670246 / 100000 * Real.log 9) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 + π + π / 2) + ((61 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_9_cos_r : (482112079168947 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) ≤ (964224234816589 / 1000000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (134147643 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) (134147643 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 - (134147643 / 500000000 : ℝ)| ≤ (7647869390209 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 - (134147643 / 500000000 : ℝ))]

theorem thL_9_sin_r : (265088057938079 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) ≤ (132544067208387 / 500000000000000 : ℝ) := by
  have hr := thL_9_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (134147643 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247) (134147643 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 - (134147643 / 500000000 : ℝ)| ≤ (7647869390209 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 9) 247 - (134147643 / 500000000 : ℝ))]

theorem thL_9_cos : (265088057938079 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 9) ∧ Real.cos (17670246 / 100000 * Real.log 9) ≤ (132544067208387 / 500000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_9_sin : (-964224234816589 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 9) ∧ Real.sin (17670246 / 100000 * Real.log 9) ≤ (-482112079168947 / 500000000000000 : ℝ) := by
  have hc := thL_9_cos_r
  have hs := thL_9_sin_r
  rw [thL_9_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_9 : (265088057938079 / 1000000000000000 : ℝ) ≤ cCG cZ 9 ∧ cCG cZ 9 ≤ (132544067208387 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_cos

theorem sCB_9 : (-964224234816589 / 1000000000000000 : ℝ) ≤ sCG cZ 9 ∧ sCG cZ 9 ≤ (-482112079168947 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_9_sin

theorem thL_11_r_bounds : (-4010147311247828079 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 ≤ (-4010146528752171921 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_11
  have hl : (423713993504001571 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 11 ∧ 17670246 / 100000 * Real.log 11 ≤ (42371399358174687 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_11_eq : (17670246 / 100000 * Real.log 11) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 + π) + ((67 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_11_cos_r : (460332670553593 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) ≤ (230166354839197 / 250000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(100253673 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) (-(100253673 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 - (-(100253673 / 250000000 : ℝ))| ≤ (391247828079 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 - (-(100253673 / 250000000 : ℝ)))]

theorem thL_11_sin_r : (-390352774022667 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) ≤ (-3903526957731 / 10000000000000 : ℝ) := by
  have hr := thL_11_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (100253673 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((11465896830420327560256656062473321276434620803944190628857432523013782168322562687885470065190297626093023617301087 / 29373168945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(100253673 / 250000000 : ℝ)) ∧ Real.sin (-(100253673 / 250000000 : ℝ)) ≤ -((45863587321681179378840072165693978575296068158620160073691307383413503864741307672239494654274583 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270) (-(100253673 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 - (-(100253673 / 250000000 : ℝ))| ≤ (391247828079 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 11) 270 - (-(100253673 / 250000000 : ℝ)))]

theorem thL_11_cos : (-230166354839197 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 11) ∧ Real.cos (17670246 / 100000 * Real.log 11) ≤ (-460332670553593 / 500000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_11_sin : (3903526957731 / 10000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 11) ∧ Real.sin (17670246 / 100000 * Real.log 11) ≤ (390352774022667 / 1000000000000000 : ℝ) := by
  have hc := thL_11_cos_r
  have hs := thL_11_sin_r
  rw [thL_11_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_11 : (-230166354839197 / 250000000000000 : ℝ) ≤ cCG cZ 11 ∧ cCG cZ 11 ≤ (-460332670553593 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_cos

theorem sCB_11 : (3903526957731 / 10000000000000 : ℝ) ≤ sCG cZ 11 ∧ sCG cZ 11 ≤ (390352774022667 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_11_sin

theorem thL_12_r_bounds : (-1834634093513844039 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 ≤ (-1834633896486155961 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_12
  have hl : (43908911786603471 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 12 ∧ 17670246 / 100000 * Real.log 12 ≤ (439089117943976591 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_12_eq : (17670246 / 100000 * Real.log 12) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) + ((70 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_12_cos_r : (742598988763157 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) ≤ (185649766906291 / 250000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(366926799 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) (-(366926799 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 - (-(366926799 / 500000000 : ℝ))| ≤ (98513844039 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 - (-(366926799 / 500000000 : ℝ)))]

theorem thL_12_sin_r : (-334868159157503 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) ≤ (-133947247900211 / 200000000000000 : ℝ) := by
  have hr := thL_12_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (366926799 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2095018797463679160128143127252508020375983131317160887705722798878090036567958475475992030663586125040136337377050120693 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(366926799 / 500000000 : ℝ)) ∧ Real.sin (-(366926799 / 500000000 : ℝ)) ≤ -((161155292111898900746318781403753077715220144000009175254643069915840998382124766597291293796017123521 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280) (-(366926799 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 - (-(366926799 / 500000000 : ℝ))| ≤ (98513844039 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 12) 280 - (-(366926799 / 500000000 : ℝ)))]

theorem thL_12_cos : (742598988763157 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 12) ∧ Real.cos (17670246 / 100000 * Real.log 12) ≤ (185649766906291 / 250000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_12_sin : (-334868159157503 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 12) ∧ Real.sin (17670246 / 100000 * Real.log 12) ≤ (-133947247900211 / 200000000000000 : ℝ) := by
  have hc := thL_12_cos_r
  have hs := thL_12_sin_r
  rw [thL_12_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_12 : (742598988763157 / 1000000000000000 : ℝ) ≤ cCG cZ 12 ∧ cCG cZ 12 ≤ (185649766906291 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_cos

theorem sCB_12 : (-334868159157503 / 500000000000000 : ℝ) ≤ sCG cZ 12 ∧ sCG cZ 12 ≤ (-133947247900211 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_12_sin

theorem thL_13_r_bounds : (-72727722730871604253 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 ≤ (-72727714869128395747 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_13
  have hl : (226616430608499583 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 13 ∧ 17670246 / 100000 * Real.log 13 ≤ (453232861295033839 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_13_eq : (17670246 / 100000 * Real.log 13) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 + π / 2) + ((72 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_13_cos_r : (14939747182833 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) ≤ (746987437804799 / 1000000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(181819297 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) (-(181819297 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 - (-(181819297 / 250000000 : ℝ))| ≤ (3930871604253 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 - (-(181819297 / 250000000 : ℝ)))]

theorem thL_13_sin_r : (-83104779378593 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) ≤ (-332419078204377 / 500000000000000 : ℝ) := by
  have hr := thL_13_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (181819297 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((5608202751906193357237097601373575149154693138409648464794450171111808117577334870898995556403198510807409655427637507 / 8435440063476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(181819297 / 250000000 : ℝ)) ∧ Real.sin (-(181819297 / 250000000 : ℝ)) ≤ -((575200282244576363154784961076215914193831109962790063731092101414259829950563006061990230173247677 / 865173339843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289) (-(181819297 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 - (-(181819297 / 250000000 : ℝ))| ≤ (3930871604253 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 13) 289 - (-(181819297 / 250000000 : ℝ)))]

theorem thL_13_cos : (332419078204377 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 13) ∧ Real.cos (17670246 / 100000 * Real.log 13) ≤ (83104779378593 / 125000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_13_sin : (14939747182833 / 20000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 13) ∧ Real.sin (17670246 / 100000 * Real.log 13) ≤ (746987437804799 / 1000000000000000 : ℝ) := by
  have hc := thL_13_cos_r
  have hs := thL_13_sin_r
  rw [thL_13_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_13 : (332419078204377 / 500000000000000 : ℝ) ≤ cCG cZ 13 ∧ cCG cZ 13 ≤ (83104779378593 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_cos

theorem sCB_13 : (14939747182833 / 20000000000000 : ℝ) ≤ sCG cZ 13 ∧ sCG cZ 13 ≤ (746987437804799 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_13_sin

theorem thL_14_r_bounds : (-19858685616495008869 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 ≤ (-19858677783504991131 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_14
  have hl : (93265584440433633 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 14 ∧ 17670246 / 100000 * Real.log 14 ≤ (233163961140124623 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_14_eq : (17670246 / 100000 * Real.log 14) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 + π / 2) + ((74 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_14_cos_r : (980346316065191 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) ≤ (245086598598773 / 250000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(198586817 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) (-(198586817 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 - (-(198586817 / 1000000000 : ℝ))| ≤ (3916495008869 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 - (-(198586817 / 1000000000 : ℝ)))]

theorem thL_14_sin_r : (-197284158614481 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) ≤ (-9864204014229 / 50000000000000 : ℝ) := by
  have hr := thL_14_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (198586817 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((8590855351901483840091458491975107735415819188244807543624119136915151750242142587534245647016576374259487924179543276989359 / 43545600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(198586817 / 1000000000 : ℝ)) ∧ Real.sin (-(198586817 / 1000000000 : ℝ)) ≤ -((715904612658456986238938647553539146981715678171812524437381853341175718552411410882781809905934675735197 / 3628800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297) (-(198586817 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 - (-(198586817 / 1000000000 : ℝ))| ≤ (3916495008869 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 14) 297 - (-(198586817 / 1000000000 : ℝ)))]

theorem thL_14_cos : (9864204014229 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 14) ∧ Real.cos (17670246 / 100000 * Real.log 14) ≤ (197284158614481 / 1000000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_14_sin : (980346316065191 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 14) ∧ Real.sin (17670246 / 100000 * Real.log 14) ≤ (245086598598773 / 250000000000000 : ℝ) := by
  have hc := thL_14_cos_r
  have hs := thL_14_sin_r
  rw [thL_14_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_14 : (9864204014229 / 50000000000000 : ℝ) ≤ cCG cZ 14 ∧ cCG cZ 14 ≤ (197284158614481 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_cos

theorem sCB_14 : (980346316065191 / 1000000000000000 : ℝ) ≤ sCG cZ 14 ∧ sCG cZ 14 ≤ (245086598598773 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_14_sin

theorem thL_16_r_bounds : (-4130154892495005033 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 ≤ (-4130152607504994967 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_16
  have hl : (97984649552861589 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 16 ∧ 17670246 / 100000 * Real.log 16 ≤ (61240405981908999 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_16_eq : (17670246 / 100000 * Real.log 16) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) + ((78 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_16_cos_r : (986384428068437 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) ≤ (986384519468039 / 1000000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(3304123 / 20000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) (-(3304123 / 20000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 - (-(3304123 / 20000000 : ℝ))| ≤ (1142495005033 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 - (-(3304123 / 20000000 : ℝ)))]

theorem thL_16_sin_r : (-164455723342613 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) ≤ (-164455631943011 / 1000000000000000 : ℝ) := by
  have hr := thL_16_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (3304123 / 20000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((11984532337925979331135610422213432712250939326689585704969675814652705902632995947769216757294935476669 / 72873934848000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(3304123 / 20000000 : ℝ)) ∧ Real.sin (-(3304123 / 20000000 : ℝ)) ≤ -((1344418691754516912056973831929188608397390253708034613962821693488160361037417366166173 / 8174960640000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312) (-(3304123 / 20000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 - (-(3304123 / 20000000 : ℝ))| ≤ (1142495005033 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 16) 312 - (-(3304123 / 20000000 : ℝ)))]

theorem thL_16_cos : (986384428068437 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 16) ∧ Real.cos (17670246 / 100000 * Real.log 16) ≤ (986384519468039 / 1000000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_16_sin : (-164455723342613 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 16) ∧ Real.sin (17670246 / 100000 * Real.log 16) ≤ (-164455631943011 / 1000000000000000 : ℝ) := by
  have hc := thL_16_cos_r
  have hs := thL_16_sin_r
  rw [thL_16_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_16 : (986384428068437 / 1000000000000000 : ℝ) ≤ cCG cZ 16 ∧ cCG cZ 16 ≤ (986384519468039 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_cos

theorem sCB_16 : (-164455723342613 / 1000000000000000 : ℝ) ≤ sCG cZ 16 ∧ sCG cZ 16 ≤ (-164455631943011 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_16_sin

theorem thL_17_r_bounds : (-89652134583166507193 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 ≤ (-89652114616833492807 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_17
  have hl : (500635767574656189 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 17 ∧ 17670246 / 100000 * Real.log 17 ≤ (250317883836960079 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_17_eq : (17670246 / 100000 * Real.log 17) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 + π + π / 2) + ((79 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_17_cos_r : (901202258980489 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) ≤ (225300589703073 / 250000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(448260623 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) (-(448260623 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 - (-(448260623 / 1000000000 : ℝ))| ≤ (9983166507193 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 - (-(448260623 / 1000000000 : ℝ)))]

theorem thL_17_sin_r : (-433398709858029 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) ≤ (-216699305013179 / 500000000000000 : ℝ) := by
  have hr := thL_17_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (448260623 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2698782470152179635651708178281181880226064073101849571452224868039389903960657800856987419257420745137120393197004635450111183 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(448260623 / 1000000000 : ℝ)) ∧ Real.sin (-(448260623 / 1000000000 : ℝ)) ≤ -((17299887629180449554564279901550545990918528197928716093450743353004141747407209831360199994851180036462673 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319) (-(448260623 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 - (-(448260623 / 1000000000 : ℝ))| ≤ (9983166507193 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 17) 319 - (-(448260623 / 1000000000 : ℝ)))]

theorem thL_17_cos : (-433398709858029 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 17) ∧ Real.cos (17670246 / 100000 * Real.log 17) ≤ (-216699305013179 / 500000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_17_sin : (-225300589703073 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 17) ∧ Real.sin (17670246 / 100000 * Real.log 17) ≤ (-901202258980489 / 1000000000000000 : ℝ) := by
  have hc := thL_17_cos_r
  have hs := thL_17_sin_r
  rw [thL_17_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_17 : (-433398709858029 / 1000000000000000 : ℝ) ≤ cCG cZ 17 ∧ cCG cZ 17 ≤ (-216699305013179 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_cos

theorem sCB_17 : (-225300589703073 / 250000000000000 : ℝ) ≤ sCG cZ 17 ∧ sCG cZ 17 ≤ (-901202258980489 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_17_sin

theorem thL_18_r_bounds : (907974801968588999 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 ≤ (907975222031411001 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_18
  have hl : (510735799909087967 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 18 ∧ 17670246 / 100000 * Real.log 18 ≤ (255367900006924627 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_18_eq : (17670246 / 100000 * Real.log 18) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 + π / 2) + ((81 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_18_cos_r : (243586824612363 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) ≤ (487173701732579 / 500000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (226993753 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) (226993753 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 - (226993753 / 1000000000 : ℝ)| ≤ (210031411001 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 - (226993753 / 1000000000 : ℝ))]

theorem thL_18_sin_r : (225049363582219 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) ≤ (112524734298963 / 500000000000000 : ℝ) := by
  have hr := thL_18_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (226993753 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325) (226993753 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 - (226993753 / 1000000000 : ℝ)| ≤ (210031411001 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 18) 325 - (226993753 / 1000000000 : ℝ))]

theorem thL_18_cos : (-112524734298963 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 18) ∧ Real.cos (17670246 / 100000 * Real.log 18) ≤ (-225049363582219 / 1000000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_18_sin : (243586824612363 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 18) ∧ Real.sin (17670246 / 100000 * Real.log 18) ≤ (487173701732579 / 500000000000000 : ℝ) := by
  have hc := thL_18_cos_r
  have hs := thL_18_sin_r
  rw [thL_18_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_18 : (-112524734298963 / 500000000000000 : ℝ) ≤ cCG cZ 18 ∧ cCG cZ 18 ≤ (-225049363582219 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_cos

theorem sCB_18 : (243586824612363 / 250000000000000 : ℝ) ≤ sCG cZ 18 ∧ sCG cZ 18 ≤ (487173701732579 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_18_sin

theorem thL_19_r_bounds : (71205348653423806643 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 ≤ (71205370546576193357 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_19
  have hl : (5202896109123779 / 10000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 19 ∧ 17670246 / 100000 * Real.log 19 ≤ (52028961102086463 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_19_eq : (17670246 / 100000 * Real.log 19) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 + π + π / 2) + ((82 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_19_cos_r : (468644517385201 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) ≤ (937289144236173 / 1000000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (178013399 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) (178013399 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 - (178013399 / 500000000 : ℝ)| ≤ (10946576193357 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 - (178013399 / 500000000 : ℝ))]

theorem thL_19_sin_r : (348552900638451 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) ≤ (174276505052107 / 500000000000000 : ℝ) := by
  have hr := thL_19_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (178013399 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331) (178013399 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 - (178013399 / 500000000 : ℝ)| ≤ (10946576193357 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 19) 331 - (178013399 / 500000000 : ℝ))]

theorem thL_19_cos : (348552900638451 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 19) ∧ Real.cos (17670246 / 100000 * Real.log 19) ≤ (174276505052107 / 500000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_19_sin : (-937289144236173 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 19) ∧ Real.sin (17670246 / 100000 * Real.log 19) ≤ (-468644517385201 / 500000000000000 : ℝ) := by
  have hc := thL_19_cos_r
  have hs := thL_19_sin_r
  rw [thL_19_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_19 : (348552900638451 / 1000000000000000 : ℝ) ≤ cCG cZ 19 ∧ cCG cZ 19 ≤ (174276505052107 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_cos

theorem sCB_19 : (-937289144236173 / 1000000000000000 : ℝ) ≤ sCG cZ 19 ∧ sCG cZ 19 ≤ (-468644517385201 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_19_sin

theorem thL_21_r_bounds : (76226048022268722163 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 ≤ (76226059377731277837 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_21
  have hl : (537974604244077331 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 21 ∧ 17670246 / 100000 * Real.log 21 ≤ (537974604356956711 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_21_eq : (17670246 / 100000 * Real.log 21) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 + π) + ((85 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_21_cos_r : (361638385413943 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) ≤ (2825300329933 / 3906250000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (762260537 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) (762260537 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 - (762260537 / 1000000000 : ℝ)| ≤ (5677731277837 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 - (762260537 / 1000000000 : ℝ))]

theorem thL_21_sin_r : (690558145351249 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) ≤ (345279129455293 / 500000000000000 : ℝ) := by
  have hr := thL_21_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (762260537 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342) (762260537 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 - (762260537 / 1000000000 : ℝ)| ≤ (5677731277837 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 21) 342 - (762260537 / 1000000000 : ℝ))]

theorem thL_21_cos : (-2825300329933 / 3906250000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 21) ∧ Real.cos (17670246 / 100000 * Real.log 21) ≤ (-361638385413943 / 500000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_21_sin : (-345279129455293 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 21) ∧ Real.sin (17670246 / 100000 * Real.log 21) ≤ (-690558145351249 / 1000000000000000 : ℝ) := by
  have hc := thL_21_cos_r
  have hs := thL_21_sin_r
  rw [thL_21_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_21 : (-2825300329933 / 3906250000000 : ℝ) ≤ cCG cZ 21 ∧ cCG cZ 21 ≤ (-361638385413943 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_cos

theorem sCB_21 : (-345279129455293 / 500000000000000 : ℝ) ≤ sCG cZ 21 ∧ sCG cZ 21 ≤ (-690558145351249 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_21_sin

theorem thL_22_r_bounds : (-11057906984293912699 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 ≤ (-11057904115706087301 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_22
  have hl : (546194805445815547 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 22 ∧ 17670246 / 100000 * Real.log 22 ≤ (27309740277999789 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_22_eq : (17670246 / 100000 * Real.log 22) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) + ((87 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_22_cos_r : (903762609427639 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) ≤ (90376272417127 / 100000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(221158111 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) (-(221158111 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 - (-(221158111 / 500000000 : ℝ))| ≤ (1434293912699 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 - (-(221158111 / 500000000 : ℝ)))]

theorem thL_22_sin_r : (-107008495928347 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) ≤ (-42803386896987 / 100000000000000 : ℝ) := by
  have hr := thL_22_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (221158111 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((325363301078492035507473400162227978359923628749068214645935896649160410317718623317125533195344234622358326722891027195231 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(221158111 / 500000000 : ℝ)) ∧ Real.sin (-(221158111 / 500000000 : ℝ)) ≤ -((8342648745602282247095329781824304943681450463259904168676444987948116446256874520486426710222060680289 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348) (-(221158111 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 - (-(221158111 / 500000000 : ℝ))| ≤ (1434293912699 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 22) 348 - (-(221158111 / 500000000 : ℝ)))]

theorem thL_22_cos : (903762609427639 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 22) ∧ Real.cos (17670246 / 100000 * Real.log 22) ≤ (90376272417127 / 100000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_22_sin : (-107008495928347 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 22) ∧ Real.sin (17670246 / 100000 * Real.log 22) ≤ (-42803386896987 / 100000000000000 : ℝ) := by
  have hc := thL_22_cos_r
  have hs := thL_22_sin_r
  rw [thL_22_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_22 : (903762609427639 / 1000000000000000 : ℝ) ≤ cCG cZ 22 ∧ cCG cZ 22 ≤ (90376272417127 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_cos

theorem sCB_22 : (-107008495928347 / 250000000000000 : ℝ) ≤ sCG cZ 22 ∧ sCG cZ 22 ≤ (-42803386896987 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_22_sin

theorem thL_23_r_bounds : (-44156211581061141181 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 ≤ (-44156200018938858819 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_23
  have hl : (69256192655410331 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 23 ∧ 17670246 / 100000 * Real.log 23 ≤ (277024770679204559 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_23_eq : (17670246 / 100000 * Real.log 23) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 + π / 2) + ((88 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_23_cos_r : (14126330620667 / 15625000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) ≤ (452042637672013 / 500000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(220781029 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) (-(220781029 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 - (-(220781029 / 500000000 : ℝ))| ≤ (5781061141181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 - (-(220781029 / 500000000 : ℝ)))]

theorem thL_23_sin_r : (-106838069306003 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) ≤ (-85470432320557 / 200000000000000 : ℝ) := by
  have hr := thL_23_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (220781029 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((46406444601238300691106703356238107915868644127101397694075713420277345345673303684815955360233785311020078008655939125027 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(220781029 / 500000000 : ℝ)) ∧ Real.sin (-(220781029 / 500000000 : ℝ)) ≤ -((1189908835929176349445974778594407175073245558740264674129452039885009034892957748694129063220827500453 / 2784375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353) (-(220781029 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 - (-(220781029 / 500000000 : ℝ))| ≤ (5781061141181 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 23) 353 - (-(220781029 / 500000000 : ℝ)))]

theorem thL_23_cos : (85470432320557 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 23) ∧ Real.cos (17670246 / 100000 * Real.log 23) ≤ (106838069306003 / 250000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_23_sin : (14126330620667 / 15625000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 23) ∧ Real.sin (17670246 / 100000 * Real.log 23) ≤ (452042637672013 / 500000000000000 : ℝ) := by
  have hc := thL_23_cos_r
  have hs := thL_23_sin_r
  rw [thL_23_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_23 : (85470432320557 / 200000000000000 : ℝ) ≤ cCG cZ 23 ∧ cCG cZ 23 ≤ (106838069306003 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_cos

theorem sCB_23 : (14126330620667 / 15625000000000 : ℝ) ≤ sCG cZ 23 ∧ sCG cZ 23 ≤ (452042637672013 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_23_sin

theorem thL_24_r_bounds : (-77515518493731868613 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 ≤ (-77515506906268131387 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_24
  have hl : (561569929807635671 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 24 ∧ 17670246 / 100000 * Real.log 24 ≤ (280784964961730013 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_24_eq : (17670246 / 100000 * Real.log 24) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 + π) + ((89 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_24_cos_r : (14286248451389 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) ≤ (714312538542337 / 1000000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(775155127 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) (-(775155127 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 - (-(775155127 / 1000000000 : ℝ))| ≤ (5793731868613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 - (-(775155127 / 1000000000 : ℝ)))]

theorem thL_24_sin_r : (-349913475428063 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) ≤ (-699826834975629 / 1000000000000000 : ℝ) := by
  have hr := thL_24_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (775155127 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((4357836618604783121902296664740829083625072889726502879824524597231542193015128324252537809663163347993198941981100270407588567 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(775155127 / 1000000000 : ℝ)) ∧ Real.sin (-(775155127 / 1000000000 : ℝ)) ≤ -((27934850119027585578973744425205650500982178460821449267522483981050119791122789645414441028347840209935577 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358) (-(775155127 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 - (-(775155127 / 1000000000 : ℝ))| ≤ (5793731868613 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 24) 358 - (-(775155127 / 1000000000 : ℝ)))]

theorem thL_24_cos : (-714312538542337 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 24) ∧ Real.cos (17670246 / 100000 * Real.log 24) ≤ (-14286248451389 / 20000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_24_sin : (699826834975629 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 24) ∧ Real.sin (17670246 / 100000 * Real.log 24) ≤ (349913475428063 / 500000000000000 : ℝ) := by
  have hc := thL_24_cos_r
  have hs := thL_24_sin_r
  rw [thL_24_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_24 : (-714312538542337 / 1000000000000000 : ℝ) ≤ cCG cZ 24 ∧ cCG cZ 24 ≤ (-14286248451389 / 20000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_cos

theorem sCB_24 : (699826834975629 / 1000000000000000 : ℝ) ≤ sCG cZ 24 ∧ sCG cZ 24 ≤ (349913475428063 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_24_sin

theorem thL_26_r_bounds : (-76857877549224074259 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 ≤ (-76857865850775925741 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_26
  have hl : (575713673158479697 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 26 ∧ 17670246 / 100000 * Real.log 26 ≤ (5757136732752193 / 10000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_26_eq : (17670246 / 100000 * Real.log 26) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 + π + π / 2) + ((91 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_26_cos_r : (359449645385803 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) ≤ (179724851961197 / 250000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(768578717 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) (-(768578717 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 - (-(768578717 / 1000000000 : ℝ))| ≤ (5849224074259 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 - (-(768578717 / 1000000000 : ℝ)))]

theorem thL_26_sin_r : (-2172232000377 / 3125000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) ≤ (-695114123130913 / 1000000000000000 : ℝ) := by
  have hr := thL_26_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (768578717 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((618355781053573737064336960792201948936584697999014708526291170296125131169044706390156153818322049819684136911082311714849291 / 889574400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(768578717 / 1000000000 : ℝ)) ∧ Real.sin (-(768578717 / 1000000000 : ℝ)) ≤ -((27746733765015136160464470702243087153709739283617427046080572192951979412501434115691697754923419352343067 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367) (-(768578717 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 - (-(768578717 / 1000000000 : ℝ))| ≤ (5849224074259 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 26) 367 - (-(768578717 / 1000000000 : ℝ)))]

theorem thL_26_cos : (-2172232000377 / 3125000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 26) ∧ Real.cos (17670246 / 100000 * Real.log 26) ≤ (-695114123130913 / 1000000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_26_sin : (-179724851961197 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 26) ∧ Real.sin (17670246 / 100000 * Real.log 26) ≤ (-359449645385803 / 500000000000000 : ℝ) := by
  have hc := thL_26_cos_r
  have hs := thL_26_sin_r
  rw [thL_26_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_26 : (-2172232000377 / 3125000000000 : ℝ) ≤ cCG cZ 26 ∧ cCG cZ 26 ≤ (-695114123130913 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_cos

theorem sCB_26 : (-179724851961197 / 250000000000000 : ℝ) ≤ sCG cZ 26 ∧ sCG cZ 26 ≤ (-359449645385803 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_26_sin

theorem thL_27_r_bounds : (-76591057338806147237 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 ≤ (-76591033861193852763 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_27
  have hl : (116476496390842523 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 27 ∧ 17670246 / 100000 * Real.log 27 ≤ (58238248207125317 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_27_eq : (17670246 / 100000 * Real.log 27) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 + π + π / 2) + ((92 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_27_cos_r : (463782184368419 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) ≤ (927564486124921 / 1000000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(95738807 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) (-(95738807 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 - (-(95738807 / 250000000 : ℝ))| ≤ (11738806147237 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 - (-(95738807 / 250000000 : ℝ)))]

theorem thL_27_sin_r : (-373663320153873 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) ≤ (-37366320276581 / 100000000000000 : ℝ) := by
  have hr := thL_27_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (95738807 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((34672154505644325193890593836743138950588074744409958301616426894769877662947131229991285674072111473038676778195054807 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(95738807 / 250000000 : ℝ)) ∧ Real.sin (-(95738807 / 250000000 : ℝ)) ≤ -((3556118410835309581598900901419667348532242017948704187208641317422358912929905802447618588169700057 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371) (-(95738807 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 - (-(95738807 / 250000000 : ℝ))| ≤ (11738806147237 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 27) 371 - (-(95738807 / 250000000 : ℝ)))]

theorem thL_27_cos : (-373663320153873 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 27) ∧ Real.cos (17670246 / 100000 * Real.log 27) ≤ (-37366320276581 / 100000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_27_sin : (-927564486124921 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 27) ∧ Real.sin (17670246 / 100000 * Real.log 27) ≤ (-463782184368419 / 500000000000000 : ℝ) := by
  have hc := thL_27_cos_r
  have hs := thL_27_sin_r
  rw [thL_27_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_27 : (-373663320153873 / 1000000000000000 : ℝ) ≤ cCG cZ 27 ∧ cCG cZ 27 ≤ (-37366320276581 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_cos

theorem sCB_27 : (-927564486124921 / 1000000000000000 : ℝ) ≤ sCG cZ 27 ∧ sCG cZ 27 ≤ (-463782184368419 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_27_sin

theorem thL_28_r_bounds : (-191910723811377431 / 800000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 ≤ (-191910629788622569 / 800000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_28
  have hl : (588808734143577691 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 28 ∧ 17670246 / 100000 * Real.log 28 ≤ (294404367130425227 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_28_eq : (17670246 / 100000 * Real.log 28) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 + π + π / 2) + ((93 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_28_cos_r : (194272890096431 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) ≤ (971364568010599 / 1000000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(119944173 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) (-(119944173 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 - (-(119944173 / 500000000 : ℝ))| ≤ (47011377431 / 800000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 - (-(119944173 / 500000000 : ℝ)))]

theorem thL_28_sin_r : (-14849639371229 / 62500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) ≤ (-11879705620561 / 50000000000000 : ℝ) := by
  have hr := thL_28_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (119944173 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((743224266708179988369394498042102640003323733041767354732498277528539398153000902197770667060202901434263047403162059631 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(119944173 / 500000000 : ℝ)) ∧ Real.sin (-(119944173 / 500000000 : ℝ)) ≤ -((57171097439090767999456678178490706312378643759151500884031153681759284793896151716974084140521105083 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375) (-(119944173 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 - (-(119944173 / 500000000 : ℝ))| ≤ (47011377431 / 800000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 28) 375 - (-(119944173 / 500000000 : ℝ)))]

theorem thL_28_cos : (-14849639371229 / 62500000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 28) ∧ Real.cos (17670246 / 100000 * Real.log 28) ≤ (-11879705620561 / 50000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_28_sin : (-971364568010599 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 28) ∧ Real.sin (17670246 / 100000 * Real.log 28) ≤ (-194272890096431 / 200000000000000 : ℝ) := by
  have hc := thL_28_cos_r
  have hs := thL_28_sin_r
  rw [thL_28_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_28 : (-14849639371229 / 62500000000000 : ℝ) ≤ cCG cZ 28 ∧ cCG cZ 28 ≤ (-11879705620561 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_cos

theorem sCB_28 : (-971364568010599 / 1000000000000000 : ℝ) ≤ sCG cZ 28 ∧ sCG cZ 28 ≤ (-194272890096431 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_28_sin

theorem thL_29_r_bounds : (-32235117703780131183 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 ≤ (-32235105896219868817 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_29
  have hl : (297504728339425011 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 29 ∧ 17670246 / 100000 * Real.log 29 ≤ (29750472839815181 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_29_eq : (17670246 / 100000 * Real.log 29) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 + π + π / 2) + ((94 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_29_cos_r : (948493153053537 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) ≤ (948493271129143 / 1000000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(161175559 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) (-(161175559 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 - (-(161175559 / 500000000 : ℝ))| ≤ (5903780131183 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 - (-(161175559 / 500000000 : ℝ)))]

theorem thL_29_sin_r : (-316797512652331 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) ≤ (-316797394576727 / 1000000000000000 : ℝ) := by
  have hr := thL_29_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (161175559 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((240808634404871473004665082614268085106007000380807723552386949823925690635477890529139606828405840342158188861604127797479 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(161175559 / 500000000 : ℝ)) ∧ Real.sin (-(161175559 / 500000000 : ℝ)) ≤ -((6174580369355677524929770569055066128716157997666786899864052427913662236542325174412467709515080276841 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379) (-(161175559 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 - (-(161175559 / 500000000 : ℝ))| ≤ (5903780131183 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 29) 379 - (-(161175559 / 500000000 : ℝ)))]

theorem thL_29_cos : (-316797512652331 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 29) ∧ Real.cos (17670246 / 100000 * Real.log 29) ≤ (-316797394576727 / 1000000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_29_sin : (-948493271129143 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 29) ∧ Real.sin (17670246 / 100000 * Real.log 29) ≤ (-948493153053537 / 1000000000000000 : ℝ) := by
  have hc := thL_29_cos_r
  have hs := thL_29_sin_r
  rw [thL_29_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_29 : (-316797512652331 / 1000000000000000 : ℝ) ≤ cCG cZ 29 ∧ cCG cZ 29 ≤ (-316797394576727 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_cos

theorem sCB_29 : (-948493271129143 / 1000000000000000 : ℝ) ≤ sCG cZ 29 ∧ sCG cZ 29 ≤ (-948493153053537 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_29_sin

theorem thL_31_r_bounds : (46660447068021597529 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 ≤ (46660458931978402471 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_31
  have hl : (606793986613510311 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 31 ∧ 17670246 / 100000 * Real.log 31 ≤ (606793986731218437 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_31_eq : (17670246 / 100000 * Real.log 31) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 + π) + ((96 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_31_cos_r : (446550424089447 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) ≤ (446550483409343 / 500000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (46660453 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) (46660453 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 - (46660453 / 100000000 : ℝ)| ≤ (5931978402471 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 - (46660453 / 100000000 : ℝ))]

theorem thL_31_sin_r : (224928163895647 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) ≤ (449856446430871 / 1000000000000000 : ℝ) := by
  have hr := thL_31_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (46660453 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386) (46660453 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 - (46660453 / 100000000 : ℝ)| ≤ (5931978402471 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 31) 386 - (46660453 / 100000000 : ℝ))]

theorem thL_31_cos : (-446550483409343 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 31) ∧ Real.cos (17670246 / 100000 * Real.log 31) ≤ (-446550424089447 / 500000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_31_sin : (-449856446430871 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 31) ∧ Real.sin (17670246 / 100000 * Real.log 31) ≤ (-224928163895647 / 500000000000000 : ℝ) := by
  have hc := thL_31_cos_r
  have hs := thL_31_sin_r
  rw [thL_31_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_31 : (-446550483409343 / 500000000000000 : ℝ) ≤ cCG cZ 31 ∧ cCG cZ 31 ≤ (-446550424089447 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_cos

theorem sCB_31 : (-449856446430871 / 1000000000000000 : ℝ) ≤ sCG cZ 31 ∧ sCG cZ 31 ≤ (-224928163895647 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_31_sin

theorem thL_32_r_bounds : (-2065077432698715003 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 ≤ (-2065076247301284997 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_32
  have hl : (153101014926870421 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 32 ∧ 17670246 / 100000 * Real.log 32 ≤ (612404059825279553 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_32_eq : (17670246 / 100000 * Real.log 32) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 + π) + ((97 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_32_cos_r : (978752897659037 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) ≤ (978753016198781 / 1000000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(51626921 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) (-(51626921 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 - (-(51626921 / 250000000 : ℝ))| ≤ (592698715003 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 - (-(51626921 / 250000000 : ℝ)))]

theorem thL_32_sin_r : (-20504310183147 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) ≤ (-102521491645863 / 500000000000000 : ℝ) := by
  have hr := thL_32_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (51626921 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((19025911255573550308852557227199160945411922940747274246707393577353789023112511803905157959760910516727627592893457161 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(51626921 / 250000000 : ℝ)) ∧ Real.sin (-(51626921 / 250000000 : ℝ)) ≤ -((1951375513392159004137765919323821978831224250956749386872737928387027947051707007386037075919631879 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390) (-(51626921 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 - (-(51626921 / 250000000 : ℝ))| ≤ (592698715003 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 32) 390 - (-(51626921 / 250000000 : ℝ)))]

theorem thL_32_cos : (-978753016198781 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 32) ∧ Real.cos (17670246 / 100000 * Real.log 32) ≤ (-978752897659037 / 1000000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_32_sin : (102521491645863 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 32) ∧ Real.sin (17670246 / 100000 * Real.log 32) ≤ (20504310183147 / 100000000000000 : ℝ) := by
  have hc := thL_32_cos_r
  have hs := thL_32_sin_r
  rw [thL_32_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_32 : (-978753016198781 / 1000000000000000 : ℝ) ≤ cCG cZ 32 ∧ cCG cZ 32 ≤ (-978752897659037 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_cos

theorem sCB_32 : (102521491645863 / 500000000000000 : ℝ) ≤ sCG cZ 32 ∧ sCG cZ 32 ≤ (20504310183147 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_32_sin

theorem thL_33_r_bounds : (103706212354541928129 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 ≤ (103706236045458071871 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_33
  have hl : (617841487492167081 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 33 ∧ 17670246 / 100000 * Real.log 33 ≤ (617841487610037057 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_33_eq : (17670246 / 100000 * Real.log 33) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 + π / 2) + ((98 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_33_cos_r : (434274020390777 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) ≤ (217137039809231 / 250000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (518531121 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) (518531121 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 - (518531121 / 1000000000 : ℝ)| ≤ (11845458071871 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 - (518531121 / 1000000000 : ℝ))]

theorem thL_33_sin_r : (495604821670413 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) ≤ (247802470062513 / 500000000000000 : ℝ) := by
  have hr := thL_33_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (518531121 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393) (518531121 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 - (518531121 / 1000000000 : ℝ)| ≤ (11845458071871 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 33) 393 - (518531121 / 1000000000 : ℝ))]

theorem thL_33_cos : (-247802470062513 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 33) ∧ Real.cos (17670246 / 100000 * Real.log 33) ≤ (-495604821670413 / 1000000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_33_sin : (434274020390777 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 33) ∧ Real.sin (17670246 / 100000 * Real.log 33) ≤ (217137039809231 / 250000000000000 : ℝ) := by
  have hc := thL_33_cos_r
  have hs := thL_33_sin_r
  rw [thL_33_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_33 : (-247802470062513 / 500000000000000 : ℝ) ≤ cCG cZ 33 ∧ cCG cZ 33 ≤ (-495604821670413 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_cos

theorem sCB_33 : (434274020390777 / 500000000000000 : ℝ) ≤ sCG cZ 33 ∧ sCG cZ 33 ≤ (217137039809231 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_33_sin

theorem thL_34_r_bounds : (-48956221935110016569 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 ≤ (-48956210064889983431 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_34
  have hl : (623116579518996757 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 34 ∧ 17670246 / 100000 * Real.log 34 ≤ (311558289818462529 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_34_eq : (17670246 / 100000 * Real.log 34) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 + π / 2) + ((99 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_34_cos_r : (88253877351761 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) ≤ (882538892220207 / 1000000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(6119527 / 12500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) (-(6119527 / 12500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 - (-(6119527 / 12500000 : ℝ))| ≤ (5935110016569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 - (-(6119527 / 12500000 : ℝ)))]

theorem thL_34_sin_r : (-117559895451347 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) ≤ (-117559865775793 / 250000000000000 : ℝ) := by
  have hr := thL_34_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (6119527 / 12500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((76090698902327672447287052596329100070331945959847276255571219077125912406234282047509299444337135681 / 161812640726566314697265625000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(6119527 / 12500000 : ℝ)) ∧ Real.sin (-(6119527 / 12500000 : ℝ)) ≤ -((21851687889898536561978358985604098866824481104143522721147529261786679827351437083977 / 46469271183013916015625000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397) (-(6119527 / 12500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 - (-(6119527 / 12500000 : ℝ))| ≤ (5935110016569 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 34) 397 - (-(6119527 / 12500000 : ℝ)))]

theorem thL_34_cos : (117559865775793 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 34) ∧ Real.cos (17670246 / 100000 * Real.log 34) ≤ (117559895451347 / 250000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_34_sin : (88253877351761 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 34) ∧ Real.sin (17670246 / 100000 * Real.log 34) ≤ (882538892220207 / 1000000000000000 : ℝ) := by
  have hc := thL_34_cos_r
  have hs := thL_34_sin_r
  rw [thL_34_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_34 : (117559865775793 / 250000000000000 : ℝ) ≤ cCG cZ 34 ∧ cCG cZ 34 ≤ (117559895451347 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_cos

theorem sCB_34 : (88253877351761 / 100000000000000 : ℝ) ≤ sCG cZ 34 ∧ sCG cZ 34 ≤ (882538892220207 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_34_sin

theorem thL_36_r_bounds : (37138431171610489659 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 ≤ (37138454828389510341 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_36
  have hl : (63321661185420139 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 36 ∧ 17670246 / 100000 * Real.log 36 ≤ (25328664478888641 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_36_eq : (17670246 / 100000 * Real.log 36) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 + π + π / 2) + ((100 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_36_cos_r : (982808625456099 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) ≤ (196561748747999 / 200000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (37138443 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) (37138443 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 - (37138443 / 200000000 : ℝ)| ≤ (11828389510341 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 - (37138443 / 200000000 : ℝ))]

theorem thL_36_sin_r : (18462683347843 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) ≤ (92313475881163 / 500000000000000 : ℝ) := by
  have hr := thL_36_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (37138443 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403) (37138443 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 - (37138443 / 200000000 : ℝ)| ≤ (11828389510341 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 36) 403 - (37138443 / 200000000 : ℝ))]

theorem thL_36_cos : (18462683347843 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 36) ∧ Real.cos (17670246 / 100000 * Real.log 36) ≤ (92313475881163 / 500000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_36_sin : (-196561748747999 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 36) ∧ Real.sin (17670246 / 100000 * Real.log 36) ≤ (-982808625456099 / 1000000000000000 : ℝ) := by
  have hc := thL_36_cos_r
  have hs := thL_36_sin_r
  rw [thL_36_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_36 : (18462683347843 / 100000000000000 : ℝ) ≤ cCG cZ 36 ∧ cCG cZ 36 ≤ (92313475881163 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_cos

theorem sCB_36 : (-196561748747999 / 200000000000000 : ℝ) ≤ sCG cZ 36 ∧ sCG cZ 36 ≤ (-982808625456099 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_36_sin

theorem thL_37_r_bounds : (15738465798412620369 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 ≤ (15738471701587379631 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_37
  have hl : (127611615598942629 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 37 ∧ 17670246 / 100000 * Real.log 37 ≤ (25522323124510391 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_37_eq : (17670246 / 100000 * Real.log 37) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 + π) + ((101 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_37_cos_r : (11885846825249 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) ≤ (475433932041709 / 500000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (503631 / 1600000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) (503631 / 1600000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 - (503631 / 1600000 : ℝ)| ≤ (2951587379631 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 - (503631 / 1600000 : ℝ))]

theorem thL_37_sin_r : (309597126543669 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) ≤ (61919448921433 / 200000000000000 : ℝ) := by
  have hr := thL_37_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (503631 / 1600000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406) (503631 / 1600000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 - (503631 / 1600000 : ℝ)| ≤ (2951587379631 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 37) 406 - (503631 / 1600000 : ℝ))]

theorem thL_37_cos : (-475433932041709 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 37) ∧ Real.cos (17670246 / 100000 * Real.log 37) ≤ (-11885846825249 / 12500000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_37_sin : (-61919448921433 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 37) ∧ Real.sin (17670246 / 100000 * Real.log 37) ≤ (-309597126543669 / 1000000000000000 : ℝ) := by
  have hc := thL_37_cos_r
  have hs := thL_37_sin_r
  rw [thL_37_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_37 : (-475433932041709 / 500000000000000 : ℝ) ≤ cCG cZ 37 ∧ cCG cZ 37 ≤ (-11885846825249 / 12500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_cos

theorem sCB_37 : (-61919448921433 / 200000000000000 : ℝ) ≤ sCG cZ 37 ∧ sCG cZ 37 ≤ (-309597126543669 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_37_sin

theorem thL_38_r_bounds : (62945039780474546577 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 ≤ (62945063419525453423 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_38
  have hl : (64277042285801509 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 38 ∧ 17670246 / 100000 * Real.log 38 ≤ (642770422976088201 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_38_eq : (17670246 / 100000 * Real.log 38) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 + π / 2) + ((102 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_38_cos_r : (95088140352773 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) ≤ (237720380430747 / 250000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (157362629 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) (157362629 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 - (157362629 / 500000000 : ℝ)| ≤ (11819525453423 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 - (157362629 / 500000000 : ℝ))]

theorem thL_38_sin_r : (154777588370781 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) ≤ (309555294936817 / 1000000000000000 : ℝ) := by
  have hr := thL_38_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (157362629 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409) (157362629 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 - (157362629 / 500000000 : ℝ)| ≤ (11819525453423 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 38) 409 - (157362629 / 500000000 : ℝ))]

theorem thL_38_cos : (-309555294936817 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 38) ∧ Real.cos (17670246 / 100000 * Real.log 38) ≤ (-154777588370781 / 500000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_38_sin : (95088140352773 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 38) ∧ Real.sin (17670246 / 100000 * Real.log 38) ≤ (237720380430747 / 250000000000000 : ℝ) := by
  have hc := thL_38_cos_r
  have hs := thL_38_sin_r
  rw [thL_38_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_38 : (-309555294936817 / 1000000000000000 : ℝ) ≤ cCG cZ 38 ∧ cCG cZ 38 ≤ (-154777588370781 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_cos

theorem sCB_38 : (95088140352773 / 100000000000000 : ℝ) ≤ sCG cZ 38 ∧ sCG cZ 38 ≤ (237720380430747 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_38_sin

theorem thL_39_r_bounds : (9613428283362343759 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 ≤ (9613434216637656241 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_39
  have hl : (323680177602582327 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 39 ∧ 17670246 / 100000 * Real.log 39 ≤ (64736035532325979 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_39_eq : (17670246 / 100000 * Real.log 39) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) + ((103 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_39_cos_r : (12269664989023 / 12500000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) ≤ (981573317787347 / 1000000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (1538149 / 8000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) (1538149 / 8000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 - (1538149 / 8000000 : ℝ)| ≤ (2966637656241 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 - (1538149 / 8000000 : ℝ))]

theorem thL_39_sin_r : (47771536773673 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) ≤ (191086265760199 / 1000000000000000 : ℝ) := by
  have hr := thL_39_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (1538149 / 8000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412) (1538149 / 8000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 - (1538149 / 8000000 : ℝ)| ≤ (2966637656241 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 39) 412 - (1538149 / 8000000 : ℝ))]

theorem thL_39_cos : (12269664989023 / 12500000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 39) ∧ Real.cos (17670246 / 100000 * Real.log 39) ≤ (981573317787347 / 1000000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_39_sin : (47771536773673 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 39) ∧ Real.sin (17670246 / 100000 * Real.log 39) ≤ (191086265760199 / 1000000000000000 : ℝ) := by
  have hc := thL_39_cos_r
  have hs := thL_39_sin_r
  rw [thL_39_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_39 : (12269664989023 / 12500000000000 : ℝ) ≤ cCG cZ 39 ∧ cCG cZ 39 ≤ (981573317787347 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_cos

theorem sCB_39 : (47771536773673 / 250000000000000 : ℝ) ≤ sCG cZ 39 ∧ sCG cZ 39 ≤ (191086265760199 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_39_sin

theorem thL_41_r_bounds : (-19777252709965108093 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 ≤ (-19777246790034891907 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_41
  have hl : (656197319546337097 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 41 ∧ 17670246 / 100000 * Real.log 41 ≤ (656197319664466089 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_41_eq : (17670246 / 100000 * Real.log 41) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 + π) + ((104 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_41_cos_r : (922786649561297 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) ≤ (922786767959933 / 1000000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(79108999 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) (-(79108999 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 - (-(79108999 / 200000000 : ℝ))| ≤ (2959965108093 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 - (-(79108999 / 200000000 : ℝ)))]

theorem thL_41_sin_r : (-77062243869493 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) ≤ (-385311100948859 / 1000000000000000 : ℝ) := by
  have hr := thL_41_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (79108999 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1965539826659113776657389078616782252433372062229801310111107548851261529940076857400777982194626914460063052310416999 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(79108999 / 200000000 : ℝ)) ∧ Real.sin (-(79108999 / 200000000 : ℝ)) ≤ -((314990356836395676922985440925456680289819624263520119077423202413390744584122529644148077584801001 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418) (-(79108999 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 - (-(79108999 / 200000000 : ℝ))| ≤ (2959965108093 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 41) 418 - (-(79108999 / 200000000 : ℝ)))]

theorem thL_41_cos : (-922786767959933 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 41) ∧ Real.cos (17670246 / 100000 * Real.log 41) ≤ (-922786649561297 / 1000000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_41_sin : (385311100948859 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 41) ∧ Real.sin (17670246 / 100000 * Real.log 41) ≤ (77062243869493 / 200000000000000 : ℝ) := by
  have hc := thL_41_cos_r
  have hs := thL_41_sin_r
  rw [thL_41_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_41 : (-922786767959933 / 1000000000000000 : ℝ) ≤ cCG cZ 41 ∧ cCG cZ 41 ≤ (-922786649561297 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_cos

theorem sCB_41 : (385311100948859 / 1000000000000000 : ℝ) ≤ sCG cZ 41 ∧ sCG cZ 41 ≤ (77062243869493 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_41_sin

theorem thL_42_r_bounds : (7209589364755309213 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 ≤ (7209590555244690787 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_42
  have hl : (660455416190332111 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 42 ∧ 17670246 / 100000 * Real.log 42 ≤ (41278463519279633 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_42_eq : (17670246 / 100000 * Real.log 42) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) + ((105 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_42_cos_r : (751172976701603 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) ≤ (751173095791713 / 1000000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (180239749 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) (180239749 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 - (180239749 / 250000000 : ℝ)| ≤ (595244690787 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 - (180239749 / 250000000 : ℝ))]

theorem thL_42_sin_r : (330052643906007 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) ≤ (165026351715809 / 250000000000000 : ℝ) := by
  have hr := thL_42_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (180239749 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420) (180239749 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 - (180239749 / 250000000 : ℝ)| ≤ (595244690787 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 42) 420 - (180239749 / 250000000 : ℝ))]

theorem thL_42_cos : (751172976701603 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 42) ∧ Real.cos (17670246 / 100000 * Real.log 42) ≤ (751173095791713 / 1000000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_42_sin : (330052643906007 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 42) ∧ Real.sin (17670246 / 100000 * Real.log 42) ≤ (165026351715809 / 250000000000000 : ℝ) := by
  have hc := thL_42_cos_r
  have hs := thL_42_sin_r
  rw [thL_42_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_42 : (751172976701603 / 1000000000000000 : ℝ) ≤ cCG cZ 42 ∧ cCG cZ 42 ≤ (751173095791713 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_cos

theorem sCB_42 : (330052643906007 / 500000000000000 : ℝ) ≤ sCG cZ 42 ∧ sCG cZ 42 ≤ (165026351715809 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_42_sin

theorem thL_43_r_bounds : (33293346698839212719 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 ≤ (33293370501160787281 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_43
  have hl : (332306656483867733 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 43 ∧ 17670246 / 100000 * Real.log 43 ≤ (664613313085888509 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_43_eq : (17670246 / 100000 * Real.log 43) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 + π + π / 2) + ((105 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_43_cos_r : (986176310627271 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) ≤ (6163602685243 / 6250000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (166466793 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) (166466793 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 - (166466793 / 1000000000 : ℝ)| ≤ (11901160787281 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 - (166466793 / 1000000000 : ℝ))]

theorem thL_43_sin_r : (4142474145291 / 25000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) ≤ (165699084823249 / 1000000000000000 : ℝ) := by
  have hr := thL_43_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (166466793 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423) (166466793 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 - (166466793 / 1000000000 : ℝ)| ≤ (11901160787281 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 43) 423 - (166466793 / 1000000000 : ℝ))]

theorem thL_43_cos : (4142474145291 / 25000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 43) ∧ Real.cos (17670246 / 100000 * Real.log 43) ≤ (165699084823249 / 1000000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_43_sin : (-6163602685243 / 6250000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 43) ∧ Real.sin (17670246 / 100000 * Real.log 43) ≤ (-986176310627271 / 1000000000000000 : ℝ) := by
  have hc := thL_43_cos_r
  have hs := thL_43_sin_r
  rw [thL_43_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_43 : (4142474145291 / 25000000000000 : ℝ) ≤ cCG cZ 43 ∧ cCG cZ 43 ≤ (165699084823249 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_cos

theorem sCB_43 : (-6163602685243 / 6250000000000 : ℝ) ≤ sCG cZ 43 ∧ sCG cZ 43 ≤ (-986176310627271 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_43_sin

theorem thL_44_r_bounds : (-48361782237273279411 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 ≤ (-48361770362726720589 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_44
  have hl : (668675617392253227 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 44 ∧ 17670246 / 100000 * Real.log 44 ≤ (668675617510415639 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_44_eq : (17670246 / 100000 * Real.log 44) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 + π) + ((106 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_44_cos_r : (885318454853783 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) ≤ (110664821699949 / 125000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(483617763 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) (-(483617763 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 - (-(483617763 / 1000000000 : ℝ))| ≤ (5937273279411 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 - (-(483617763 / 1000000000 : ℝ)))]

theorem thL_44_sin_r : (-116246285849813 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) ≤ (-464985024653773 / 1000000000000000 : ℝ) := by
  have hr := thL_44_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (483617763 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((11915521769229962269441983693674435176044598610203497806131424796272017334148511185458810659694319405386151149584744751760321 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(483617763 / 1000000000 : ℝ)) ∧ Real.sin (-(483617763 / 1000000000 : ℝ)) ≤ -((229144649408262240203536851650209731313511809716646441800755035318294695792300365327379989281388056316373 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426) (-(483617763 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 - (-(483617763 / 1000000000 : ℝ))| ≤ (5937273279411 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 44) 426 - (-(483617763 / 1000000000 : ℝ)))]

theorem thL_44_cos : (-110664821699949 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 44) ∧ Real.cos (17670246 / 100000 * Real.log 44) ≤ (-885318454853783 / 1000000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_44_sin : (464985024653773 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 44) ∧ Real.sin (17670246 / 100000 * Real.log 44) ≤ (116246285849813 / 250000000000000 : ℝ) := by
  have hc := thL_44_cos_r
  have hs := thL_44_sin_r
  rw [thL_44_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_44 : (-110664821699949 / 125000000000000 : ℝ) ≤ cCG cZ 44 ∧ cCG cZ 44 ≤ (-885318454853783 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_cos

theorem sCB_44 : (464985024653773 / 1000000000000000 : ℝ) ≤ sCG cZ 44 ∧ sCG cZ 44 ≤ (116246285849813 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_44_sin

theorem thL_46_r_bounds : (-48286365943017111187 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 ≤ (-48286354056982888813 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_46
  have hl : (169132588297463343 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 46 ∧ 17670246 / 100000 * Real.log 46 ≤ (338265176654015307 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_46_eq : (17670246 / 100000 * Real.log 46) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 + π + π / 2) + ((107 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_46_cos_r : (885668877541357 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) ≤ (177133799280407 / 200000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(1207159 / 2500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) (-(1207159 / 2500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 - (-(1207159 / 2500000 : ℝ))| ≤ (5943017111187 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 - (-(1207159 / 2500000 : ℝ)))]

theorem thL_46_sin_r : (-464317336820459 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) ≤ (-58039652245013 / 125000000000000 : ℝ) := by
  have hr := thL_46_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (1207159 / 2500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((430839262024863321752441412560081514309536129254610439892226382997904246428135214265402832279 / 927898406982421875000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(1207159 / 2500000 : ℝ)) ∧ Real.sin (-(1207159 / 2500000 : ℝ)) ≤ -((441886422589591551051437623952151574315095442305678256638083997308263636089241 / 951690673828125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431) (-(1207159 / 2500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 - (-(1207159 / 2500000 : ℝ))| ≤ (5943017111187 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 46) 431 - (-(1207159 / 2500000 : ℝ)))]

theorem thL_46_cos : (-464317336820459 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 46) ∧ Real.cos (17670246 / 100000 * Real.log 46) ≤ (-58039652245013 / 125000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_46_sin : (-177133799280407 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 46) ∧ Real.sin (17670246 / 100000 * Real.log 46) ≤ (-885668877541357 / 1000000000000000 : ℝ) := by
  have hc := thL_46_cos_r
  have hs := thL_46_sin_r
  rw [thL_46_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_46 : (-464317336820459 / 1000000000000000 : ℝ) ≤ cCG cZ 46 ∧ cCG cZ 46 ≤ (-58039652245013 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_cos

theorem sCB_46 : (-177133799280407 / 200000000000000 : ℝ) ≤ sCG cZ 46 ∧ sCG cZ 46 ≤ (-885668877541357 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_46_sin

theorem thL_47_r_bounds : (35148611094281174249 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 ≤ (35148634905718825751 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_47
  have hl : (340165276278830821 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 47 ∧ 17670246 / 100000 * Real.log 47 ≤ (680330552675844759 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_47_eq : (17670246 / 100000 * Real.log 47) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 + π / 2) + ((108 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_47_cos_r : (492298412563397 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) ≤ (61537309011499 / 62500000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (35148623 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) (35148623 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 - (35148623 / 200000000 : ℝ)| ≤ (11905718825751 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 - (35148623 / 200000000 : ℝ))]

theorem thL_47_sin_r : (174839794986623 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) ≤ (43709978510953 / 250000000000000 : ℝ) := by
  have hr := thL_47_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (35148623 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433) (35148623 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 - (35148623 / 200000000 : ℝ)| ≤ (11905718825751 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 47) 433 - (35148623 / 200000000 : ℝ))]

theorem thL_47_cos : (-43709978510953 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 47) ∧ Real.cos (17670246 / 100000 * Real.log 47) ≤ (-174839794986623 / 1000000000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_47_sin : (492298412563397 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 47) ∧ Real.sin (17670246 / 100000 * Real.log 47) ≤ (61537309011499 / 62500000000000 : ℝ) := by
  have hc := thL_47_cos_r
  have hs := thL_47_sin_r
  rw [thL_47_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_47 : (-43709978510953 / 250000000000000 : ℝ) ≤ cCG cZ 47 ∧ cCG cZ 47 ≤ (-174839794986623 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_cos

theorem sCB_47 : (492298412563397 / 500000000000000 : ℝ) ≤ sCG cZ 47 ∧ sCG cZ 47 ≤ (61537309011499 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_47_sin

theorem thL_48_r_bounds : (30173583940979665311 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 ≤ (30173588699020334689 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_48
  have hl : (684050741754304521 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 48 ∧ 17670246 / 100000 * Real.log 48 ≤ (684050741872492699 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_48_eq : (17670246 / 100000 * Real.log 48) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 + π + π / 2) + ((108 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_48_cos_r : (182180962427929 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) ≤ (182180992183401 / 250000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (377169829 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) (377169829 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 - (377169829 / 500000000 : ℝ)| ≤ (2379020334689 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 - (377169829 / 500000000 : ℝ))]

theorem thL_48_sin_r : (684807551514837 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) ≤ (684807670469967 / 1000000000000000 : ℝ) := by
  have hr := thL_48_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (377169829 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435) (377169829 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 - (377169829 / 500000000 : ℝ)| ≤ (2379020334689 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 48) 435 - (377169829 / 500000000 : ℝ))]

theorem thL_48_cos : (684807551514837 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 48) ∧ Real.cos (17670246 / 100000 * Real.log 48) ≤ (684807670469967 / 1000000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_48_sin : (-182180992183401 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 48) ∧ Real.sin (17670246 / 100000 * Real.log 48) ≤ (-182180962427929 / 250000000000000 : ℝ) := by
  have hc := thL_48_cos_r
  have hs := thL_48_sin_r
  rw [thL_48_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_48 : (684807551514837 / 1000000000000000 : ℝ) ≤ cCG cZ 48 ∧ cCG cZ 48 ≤ (684807670469967 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_cos

theorem sCB_48 : (-182180992183401 / 250000000000000 : ℝ) ≤ sCG cZ 48 ∧ sCG cZ 48 ≤ (-182180962427929 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_48_sin

theorem thL_49_r_bounds : (-15728530525082138863 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 ≤ (-15728524574917861137 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_49
  have hl : (687694220526473809 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 49 ∧ 17670246 / 100000 * Real.log 49 ≤ (343847110322333181 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_49_eq : (17670246 / 100000 * Real.log 49) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 + π) + ((109 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_49_cos_r : (38037171284243 / 40000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) ≤ (950929401109363 / 1000000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(314570551 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) (-(314570551 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 - (-(314570551 / 1000000000 : ℝ))| ≤ (2975082138863 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 - (-(314570551 / 1000000000 : ℝ)))]

theorem thL_49_sin_r : (-154704091809247 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) ≤ (-38676008076901 / 125000000000000 : ℝ) := by
  have hr := thL_49_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (314570551 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1926690824564611794779234159980283790657261082494558179947683576416019275214538177233278855847297167329111736472746233183512151 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(314570551 / 1000000000 : ℝ)) ∧ Real.sin (-(314570551 / 1000000000 : ℝ)) ≤ -((12350582208747509611735256737465451771508333337835870768841089049984221218325837075270413365229863773711449 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438) (-(314570551 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 - (-(314570551 / 1000000000 : ℝ))| ≤ (2975082138863 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 49) 438 - (-(314570551 / 1000000000 : ℝ)))]

theorem thL_49_cos : (-950929401109363 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 49) ∧ Real.cos (17670246 / 100000 * Real.log 49) ≤ (-38037171284243 / 40000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_49_sin : (38676008076901 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 49) ∧ Real.sin (17670246 / 100000 * Real.log 49) ≤ (154704091809247 / 500000000000000 : ℝ) := by
  have hc := thL_49_cos_r
  have hs := thL_49_sin_r
  rw [thL_49_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_49 : (-950929401109363 / 1000000000000000 : ℝ) ≤ cCG cZ 49 ∧ cCG cZ 49 ≤ (-38037171284243 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_cos

theorem sCB_49 : (38676008076901 / 125000000000000 : ℝ) ≤ sCG cZ 49 ∧ sCG cZ 49 ≤ (154704091809247 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_49_sin

theorem thL_51_r_bounds : (47128512249228229813 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 ≤ (47128524150771770187 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_51
  have hl : (173690815391459147 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 51 ∧ 17670246 / 100000 * Real.log 51 ≤ (694763261684036229 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_51_eq : (17670246 / 100000 * Real.log 51) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 + π) + ((110 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_51_cos_r : (445492725623611 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) ≤ (890985570262909 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (235642591 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) (235642591 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 - (235642591 / 500000000 : ℝ)| ≤ (5950771770187 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 - (235642591 / 500000000 : ℝ))]

theorem thL_51_sin_r : (56753959882153 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) ≤ (454031798072669 / 1000000000000000 : ℝ) := by
  have hr := thL_51_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (235642591 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442) (235642591 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 - (235642591 / 500000000 : ℝ)| ≤ (5950771770187 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 51) 442 - (235642591 / 500000000 : ℝ))]

theorem thL_51_cos : (-890985570262909 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 51) ∧ Real.cos (17670246 / 100000 * Real.log 51) ≤ (-445492725623611 / 500000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_51_sin : (-454031798072669 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 51) ∧ Real.sin (17670246 / 100000 * Real.log 51) ≤ (-56753959882153 / 125000000000000 : ℝ) := by
  have hc := thL_51_cos_r
  have hs := thL_51_sin_r
  rw [thL_51_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_51 : (-890985570262909 / 1000000000000000 : ℝ) ≤ cCG cZ 51 ∧ cCG cZ 51 ≤ (-445492725623611 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_cos

theorem sCB_51 : (-454031798072669 / 1000000000000000 : ℝ) ≤ sCG cZ 51 ∧ sCG cZ 51 ≤ (-56753959882153 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_51_sin

theorem thL_52_r_bounds : (19022900186358698453 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 ≤ (19022903163641301547 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_52
  have hl : (174548621276319309 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 52 ∧ 17670246 / 100000 * Real.log 52 ≤ (698194485223479751 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_52_eq : (17670246 / 100000 * Real.log 52) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) + ((111 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_52_cos_r : (362102274435097 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) ≤ (14484093360803 / 20000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (760916067 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) (760916067 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 - (760916067 / 1000000000 : ℝ)| ≤ (1488641301547 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 - (760916067 / 1000000000 : ℝ))]

theorem thL_52_sin_r : (689585094753193 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) ≤ (689585213849101 / 1000000000000000 : ℝ) := by
  have hr := thL_52_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (760916067 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444) (760916067 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 - (760916067 / 1000000000 : ℝ)| ≤ (1488641301547 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 52) 444 - (760916067 / 1000000000 : ℝ))]

theorem thL_52_cos : (362102274435097 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 52) ∧ Real.cos (17670246 / 100000 * Real.log 52) ≤ (14484093360803 / 20000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_52_sin : (689585094753193 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 52) ∧ Real.sin (17670246 / 100000 * Real.log 52) ≤ (689585213849101 / 1000000000000000 : ℝ) := by
  have hc := thL_52_cos_r
  have hs := thL_52_sin_r
  rw [thL_52_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_52 : (362102274435097 / 500000000000000 : ℝ) ≤ cCG cZ 52 ∧ cCG cZ 52 ≤ (14484093360803 / 20000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_cos

theorem sCB_52 : (689585094753193 / 1000000000000000 : ℝ) ≤ sCG cZ 52 ∧ sCG cZ 52 ≤ (689585213849101 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_52_sin

theorem thL_53_r_bounds : (-117122012432113759609 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 ≤ (-117121988767886240391 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_53
  have hl : (35078017400757911 / 50000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 53 ∧ 17670246 / 100000 * Real.log 53 ≤ (350780174066681623 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_53_eq : (17670246 / 100000 * Real.log 53) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 + π + π / 2) + ((111 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_53_cos_r : (166675005670099 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) ≤ (833375146675029 / 1000000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(585610003 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) (-(585610003 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 - (-(585610003 / 1000000000 : ℝ))| ≤ (11832113759609 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 - (-(585610003 / 1000000000 : ℝ)))]

theorem thL_53_sin_r : (-276353952797541 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) ≤ (-552707787273791 / 1000000000000000 : ℝ) := by
  have hr := thL_53_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (585610003 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((312883932370083400175925038424905608484340711373161215841924351501846254505062065377263220755285512564760288884144829248520393 / 566092800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(585610003 / 1000000000 : ℝ)) ∧ Real.sin (-(585610003 / 1000000000 : ℝ)) ≤ -((2005666233141005129656781473313398431984573836154312415704647759100773985523336879298848506296971542366623 / 3628800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447) (-(585610003 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 - (-(585610003 / 1000000000 : ℝ))| ≤ (11832113759609 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 53) 447 - (-(585610003 / 1000000000 : ℝ)))]

theorem thL_53_cos : (-276353952797541 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 53) ∧ Real.cos (17670246 / 100000 * Real.log 53) ≤ (-552707787273791 / 1000000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_53_sin : (-833375146675029 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 53) ∧ Real.sin (17670246 / 100000 * Real.log 53) ≤ (-166675005670099 / 200000000000000 : ℝ) := by
  have hc := thL_53_cos_r
  have hs := thL_53_sin_r
  rw [thL_53_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_53 : (-276353952797541 / 500000000000000 : ℝ) ≤ cCG cZ 53 ∧ cCG cZ 53 ≤ (-552707787273791 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_cos

theorem sCB_53 : (-833375146675029 / 1000000000000000 : ℝ) ≤ sCG cZ 53 ∧ sCG cZ 53 ≤ (-166675005670099 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_53_sin

theorem thL_54_r_bounds : (-42425683035111596573 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 ≤ (-42425671164888403427 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_54
  have hl : (704863293901052471 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 54 ∧ 17670246 / 100000 * Real.log 54 ≤ (352431647009629849 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_54_eq : (17670246 / 100000 * Real.log 54) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 + π / 2) + ((112 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_54_cos_r : (455672435356447 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) ≤ (455672494707599 / 500000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(424256771 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) (-(424256771 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 - (-(424256771 / 1000000000 : ℝ))| ≤ (5935111596573 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 - (-(424256771 / 1000000000 : ℝ)))]

theorem thL_54_sin_r : (-205821808434813 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) ≤ (-411643498167391 / 1000000000000000 : ℝ) := by
  have hr := thL_54_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (424256771 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2563312994853757075509321146068276592782175871905046472740061098254523122221586321264548911940811757244759654951243730660992211 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(424256771 / 1000000000 : ℝ)) ∧ Real.sin (-(424256771 / 1000000000 : ℝ)) ≤ -((16431493556754760567764079068300272594120972929387479921355411558943353975502321095609376453976896354721029 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449) (-(424256771 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 - (-(424256771 / 1000000000 : ℝ))| ≤ (5935111596573 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 54) 449 - (-(424256771 / 1000000000 : ℝ)))]

theorem thL_54_cos : (411643498167391 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 54) ∧ Real.cos (17670246 / 100000 * Real.log 54) ≤ (205821808434813 / 500000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_54_sin : (455672435356447 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 54) ∧ Real.sin (17670246 / 100000 * Real.log 54) ≤ (455672494707599 / 500000000000000 : ℝ) := by
  have hc := thL_54_cos_r
  have hs := thL_54_sin_r
  rw [thL_54_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_54 : (411643498167391 / 1000000000000000 : ℝ) ≤ cCG cZ 54 ∧ cCG cZ 54 ≤ (205821808434813 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_cos

theorem sCB_54 : (455672435356447 / 500000000000000 : ℝ) ≤ sCG cZ 54 ∧ sCG cZ 54 ≤ (455672494707599 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_54_sin

theorem thL_56_r_bounds : (-28118994857289248881 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 ≤ (-28118982942710751119 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_56
  have hl : (711289546090450197 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 56 ∧ 17670246 / 100000 * Real.log 56 ≤ (711289546208661061 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_56_eq : (17670246 / 100000 * Real.log 56) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 + π / 2) + ((113 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_56_cos_r : (240181466480219 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) ≤ (480362992533331 / 500000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(281189889 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) (-(281189889 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 - (-(281189889 / 1000000000 : ℝ))| ≤ (5957289248881 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 - (-(281189889 / 1000000000 : ℝ)))]

theorem thL_56_sin_r : (-55499812304901 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) ≤ (-277498942378719 / 1000000000000000 : ℝ) := by
  have hr := thL_56_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (281189889 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((7111078424411223461383839831729665352546351659316469558555057314642187120512868131062869473348270210070345042297003227380283 / 25625600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(281189889 / 1000000000 : ℝ)) ∧ Real.sin (-(281189889 / 1000000000 : ℝ)) ≤ -((136751508161754291896964659310093976499836456323633002876249171717754364270323165719795461985915454033231 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453) (-(281189889 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 - (-(281189889 / 1000000000 : ℝ))| ≤ (5957289248881 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 56) 453 - (-(281189889 / 1000000000 : ℝ)))]

theorem thL_56_cos : (277498942378719 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 56) ∧ Real.cos (17670246 / 100000 * Real.log 56) ≤ (55499812304901 / 200000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_56_sin : (240181466480219 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 56) ∧ Real.sin (17670246 / 100000 * Real.log 56) ≤ (480362992533331 / 500000000000000 : ℝ) := by
  have hc := thL_56_cos_r
  have hs := thL_56_sin_r
  rw [thL_56_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_56 : (277498942378719 / 1000000000000000 : ℝ) ≤ cCG cZ 56 ∧ cCG cZ 56 ≤ (55499812304901 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_cos

theorem sCB_56 : (240181466480219 / 250000000000000 : ℝ) ≤ sCG cZ 56 ∧ sCG cZ 56 ≤ (480362992533331 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_56_sin

theorem thL_57_r_bounds : (-5904475748163865007 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 ≤ (-5904473371836134993 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_57
  have hl : (71441710490487379 / 100000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 57 ∧ 17670246 / 100000 * Real.log 57 ≤ (142883421004617231 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_57_eq : (17670246 / 100000 * Real.log 57) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 + π + π / 2) + ((113 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_57_cos_r : (478368506161091 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) ≤ (95673713113857 / 100000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(18451483 / 62500000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) (-(18451483 / 62500000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 - (-(18451483 / 62500000 : ℝ))| ≤ (1188163865007 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 - (-(18451483 / 62500000 : ℝ)))]

theorem thL_57_sin_r : (-29095396568337 / 100000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) ≤ (-145476923433491 / 500000000000000 : ℝ) := by
  have hr := thL_57_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (18451483 / 62500000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((402295091953946558535758527078651693126819877896827951467534891203790395031894526757276529136901955615381783563 / 1382676373395952396094799041748046875000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(18451483 / 62500000 : ℝ)) ∧ Real.sin (-(18451483 / 62500000 : ℝ)) ≤ -((660176561155194305314564184755123613976998160542105048869810416101761129532189702053293099133 / 2269007381983101367950439453125000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455) (-(18451483 / 62500000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 - (-(18451483 / 62500000 : ℝ))| ≤ (1188163865007 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 57) 455 - (-(18451483 / 62500000 : ℝ)))]

theorem thL_57_cos : (-29095396568337 / 100000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 57) ∧ Real.cos (17670246 / 100000 * Real.log 57) ≤ (-145476923433491 / 500000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_57_sin : (-95673713113857 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 57) ∧ Real.sin (17670246 / 100000 * Real.log 57) ≤ (-478368506161091 / 500000000000000 : ℝ) := by
  have hc := thL_57_cos_r
  have hs := thL_57_sin_r
  rw [thL_57_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_57 : (-29095396568337 / 100000000000000 : ℝ) ≤ cCG cZ 57 ∧ cCG cZ 57 ≤ (-145476923433491 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_cos

theorem sCB_57 : (-95673713113857 / 100000000000000 : ℝ) ≤ sCG cZ 57 ∧ sCG cZ 57 ≤ (-478368506161091 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_57_sin

theorem thL_58_r_bounds : (-72730544606778598079 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 ≤ (-72730517393221401921 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_58
  have hl : (358745134311116931 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 58 ∧ 17670246 / 100000 * Real.log 58 ≤ (358745134379009013 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_58_eq : (17670246 / 100000 * Real.log 58) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 + π / 2) + ((114 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_58_cos_r : (934603778957117 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) ≤ (233650978756229 / 250000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(72730531 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) (-(72730531 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 - (-(72730531 / 200000000 : ℝ))| ≤ (13606778598079 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 - (-(72730531 / 200000000 : ℝ)))]

theorem thL_58_sin_r : (-177845225960377 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) ≤ (-355690315852967 / 1000000000000000 : ℝ) := by
  have hr := thL_58_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (72730531 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1814439050300182039179857989585973572616493344988152936314320472033378588790174216611415200200645657426007559340879091 / 5101175439360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(72730531 / 200000000 : ℝ)) ∧ Real.sin (-(72730531 / 200000000 : ℝ)) ≤ -((290775488830157122725220095891494951328963956061915580645820733541860143737987793030861426983909669 / 817496064000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457) (-(72730531 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 - (-(72730531 / 200000000 : ℝ))| ≤ (13606778598079 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 58) 457 - (-(72730531 / 200000000 : ℝ)))]

theorem thL_58_cos : (355690315852967 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 58) ∧ Real.cos (17670246 / 100000 * Real.log 58) ≤ (177845225960377 / 500000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_58_sin : (934603778957117 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 58) ∧ Real.sin (17670246 / 100000 * Real.log 58) ≤ (233650978756229 / 250000000000000 : ℝ) := by
  have hc := thL_58_cos_r
  have hs := thL_58_sin_r
  rw [thL_58_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_58 : (355690315852967 / 1000000000000000 : ℝ) ≤ cCG cZ 58 ∧ cCG cZ 58 ≤ (177845225960377 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_cos

theorem sCB_58 : (934603778957117 / 1000000000000000 : ℝ) ≤ sCG cZ 58 ∧ sCG cZ 58 ≤ (233650978756229 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_58_sin

theorem thL_59_r_bounds : (-96923390590659845773 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 ≤ (-96923360209340154227 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_59
  have hl : (720510897045904249 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 59 ∧ 17670246 / 100000 * Real.log 59 ≤ (45031931074863049 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_59_eq : (17670246 / 100000 * Real.log 59) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 + π + π / 2) + ((114 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_59_cos_r : (442426711684041 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) ≤ (110606696909379 / 125000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(484616877 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) (-(484616877 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 - (-(484616877 / 1000000000 : ℝ))| ≤ (15190659845773 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 - (-(484616877 / 1000000000 : ℝ)))]

theorem thL_59_sin_r : (-14558420683561 / 31250000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) ≤ (-23293465498367 / 50000000000000 : ℝ) := by
  have hr := thL_59_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (484616877 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1705454647978324588720593947779726884129055022019386775161615491443351519819929178339612735334951387954566571923440854587417 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(484616877 / 1000000000 : ℝ)) ∧ Real.sin (-(484616877 / 1000000000 : ℝ)) ≤ -((229580433381691105451754643264319881631408738577322182181240026132200225824460183538913099722897991417467 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459) (-(484616877 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 - (-(484616877 / 1000000000 : ℝ))| ≤ (15190659845773 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 59) 459 - (-(484616877 / 1000000000 : ℝ)))]

theorem thL_59_cos : (-14558420683561 / 31250000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 59) ∧ Real.cos (17670246 / 100000 * Real.log 59) ≤ (-23293465498367 / 50000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_59_sin : (-110606696909379 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 59) ∧ Real.sin (17670246 / 100000 * Real.log 59) ≤ (-442426711684041 / 500000000000000 : ℝ) := by
  have hc := thL_59_cos_r
  have hs := thL_59_sin_r
  rw [thL_59_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_59 : (-14558420683561 / 31250000000000 : ℝ) ≤ cCG cZ 59 ∧ cCG cZ 59 ≤ (-23293465498367 / 50000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_cos

theorem sCB_59 : (-110606696909379 / 125000000000000 : ℝ) ≤ sCG cZ 59 ∧ sCG cZ 59 ≤ (-442426711684041 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_59_sin

theorem thL_61_r_bounds : (34681076490333504213 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 ≤ (34681085509666495787 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_61
  have hl : (181600381127273589 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 61 ∧ 17670246 / 100000 * Real.log 61 ≤ (45400095293089723 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_61_eq : (17670246 / 100000 * Real.log 61) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 + π) + ((115 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_61_cos_r : (768935576150981 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) ≤ (192233939140883 / 250000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (34681081 / 50000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) (34681081 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 - (34681081 / 50000000 : ℝ)| ≤ (4509666495787 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 - (34681081 / 50000000 : ℝ))]

theorem thL_61_sin_r : (319663035733041 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) ≤ (159831562963531 / 250000000000000 : ℝ) := by
  have hr := thL_61_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (34681081 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462) (34681081 / 50000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 - (34681081 / 50000000 : ℝ)| ≤ (4509666495787 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 61) 462 - (34681081 / 50000000 : ℝ))]

theorem thL_61_cos : (-192233939140883 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 61) ∧ Real.cos (17670246 / 100000 * Real.log 61) ≤ (-768935576150981 / 1000000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_61_sin : (-159831562963531 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 61) ∧ Real.sin (17670246 / 100000 * Real.log 61) ≤ (-319663035733041 / 500000000000000 : ℝ) := by
  have hc := thL_61_cos_r
  have hs := thL_61_sin_r
  rw [thL_61_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_61 : (-192233939140883 / 250000000000000 : ℝ) ≤ cCG cZ 61 ∧ cCG cZ 61 ≤ (-768935576150981 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_cos

theorem sCB_61 : (-159831562963531 / 250000000000000 : ℝ) ≤ sCG cZ 61 ∧ sCG cZ 61 ≤ (-319663035733041 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_61_sin

theorem thL_62_r_bounds : (2658143202677745767 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 ≤ (2658144409822254233 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_62
  have hl : (145854959709101713 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 62 ∧ 17670246 / 100000 * Real.log 62 ≤ (91159349842300449 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_62_eq : (17670246 / 100000 * Real.log 62) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) + ((116 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_62_cos_r : (455456828826647 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) ≤ (91091385079649 / 100000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (425303009 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) (425303009 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 - (425303009 / 1000000000 : ℝ)| ≤ (603572254233 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 - (425303009 / 1000000000 : ℝ))]

theorem thL_62_sin_r : (412596719174567 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) ≤ (103149228079423 / 250000000000000 : ℝ) := by
  have hr := thL_62_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (425303009 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464) (425303009 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 - (425303009 / 1000000000 : ℝ)| ≤ (603572254233 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 62) 464 - (425303009 / 1000000000 : ℝ))]

theorem thL_62_cos : (455456828826647 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 62) ∧ Real.cos (17670246 / 100000 * Real.log 62) ≤ (91091385079649 / 100000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_62_sin : (412596719174567 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 62) ∧ Real.sin (17670246 / 100000 * Real.log 62) ≤ (103149228079423 / 250000000000000 : ℝ) := by
  have hc := thL_62_cos_r
  have hs := thL_62_sin_r
  rw [thL_62_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_62 : (455456828826647 / 500000000000000 : ℝ) ≤ cCG cZ 62 ∧ cCG cZ 62 ≤ (91091385079649 / 100000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_cos

theorem sCB_62 : (412596719174567 / 1000000000000000 : ℝ) ≤ sCG cZ 62 ∧ sCG cZ 62 ≤ (103149228079423 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_62_sin

theorem thL_63_r_bounds : (11100993352642043649 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 ≤ (11101013847357956351 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_63
  have hl : (146420419643989649 / 200000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 63 ∧ 17670246 / 100000 * Real.log 63 ≤ (366051049212212193 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_63_eq : (17670246 / 100000 * Real.log 63) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 + π) + ((116 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_63_cos_r : (9938446084627 / 10000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) ≤ (49692240670493 / 50000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (27752509 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) (27752509 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 - (27752509 / 250000000 : ℝ)| ≤ (10247357956351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 - (27752509 / 250000000 : ℝ))]

theorem thL_63_sin_r : (27695518409461 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) ≤ (27695569646251 / 250000000000000 : ℝ) := by
  have hr := thL_63_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (27752509 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466) (27752509 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 - (27752509 / 250000000 : ℝ)| ≤ (10247357956351 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 63) 466 - (27752509 / 250000000 : ℝ))]

theorem thL_63_cos : (-49692240670493 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 63) ∧ Real.cos (17670246 / 100000 * Real.log 63) ≤ (-9938446084627 / 10000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_63_sin : (-27695569646251 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 63) ∧ Real.sin (17670246 / 100000 * Real.log 63) ≤ (-27695518409461 / 250000000000000 : ℝ) := by
  have hc := thL_63_cos_r
  have hs := thL_63_sin_r
  rw [thL_63_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_63 : (-49692240670493 / 50000000000000 : ℝ) ≤ cCG cZ 63 ∧ cCG cZ 63 ≤ (-9938446084627 / 10000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_cos

theorem sCB_63 : (-27695569646251 / 250000000000000 : ℝ) ≤ sCG cZ 63 ∧ sCG cZ 63 ≤ (-27695518409461 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_63_sin

theorem thL_64_r_bounds : (-12390465248724790099 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 ≤ (-12390454451275209901 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_64
  have hl : (367442435817518561 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 64 ∧ 17670246 / 100000 * Real.log 64 ≤ (734884871850210729 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_64_eq : (17670246 / 100000 * Real.log 64) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) + ((117 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_64_cos_r : (969452001435003 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) ≤ (242363054345999 / 250000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(247809197 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) (-(247809197 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 - (-(247809197 / 1000000000 : ℝ))| ≤ (5398724790099 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 - (-(247809197 / 1000000000 : ℝ)))]

theorem thL_64_sin_r : (-61320194741209 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) ≤ (-245280563015843 / 1000000000000000 : ℝ) := by
  have hr := thL_64_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (247809197 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1527367840094799932558470316435788520994868567486115867995725984654318153359695954142914032267473614770004319709501358585909277 / 6227020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(247809197 / 1000000000 : ℝ)) ∧ Real.sin (-(247809197 / 1000000000 : ℝ)) ≤ -((9790819487787178969669390332345149360932005763252325591285745389126971819703673388281307113012476641818347 / 39916800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468) (-(247809197 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 - (-(247809197 / 1000000000 : ℝ))| ≤ (5398724790099 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 64) 468 - (-(247809197 / 1000000000 : ℝ)))]

theorem thL_64_cos : (969452001435003 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 64) ∧ Real.cos (17670246 / 100000 * Real.log 64) ≤ (242363054345999 / 250000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_64_sin : (-61320194741209 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 64) ∧ Real.sin (17670246 / 100000 * Real.log 64) ≤ (-245280563015843 / 1000000000000000 : ℝ) := by
  have hc := thL_64_cos_r
  have hs := thL_64_sin_r
  rw [thL_64_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_64 : (969452001435003 / 1000000000000000 : ℝ) ≤ cCG cZ 64 ∧ cCG cZ 64 ≤ (242363054345999 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_cos

theorem sCB_64 : (-61320194741209 / 250000000000000 : ℝ) ≤ sCG cZ 64 ∧ sCG cZ 64 ≤ (-245280563015843 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_64_sin

theorem thL_66_r_bounds : (95445899105136268063 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 ≤ (95445946094863731937 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_66
  have hl : (740322299415921989 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 66 ∧ 17670246 / 100000 * Real.log 66 ≤ (740322299650150069 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_66_eq : (17670246 / 100000 * Real.log 66) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 + π + π / 2) + ((117 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_66_cos_r : (888270706832599 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) ≤ (111033867722691 / 125000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (477229613 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) (477229613 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 - (477229613 / 1000000000 : ℝ)| ≤ (23494863731937 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 - (477229613 / 1000000000 : ℝ))]

theorem thL_66_sin_r : (91863993984143 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) ≤ (114830051217341 / 250000000000000 : ℝ) := by
  have hr := thL_66_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (477229613 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471) (477229613 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 - (477229613 / 1000000000 : ℝ)| ≤ (23494863731937 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 66) 471 - (477229613 / 1000000000 : ℝ))]

theorem thL_66_cos : (91863993984143 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 66) ∧ Real.cos (17670246 / 100000 * Real.log 66) ≤ (114830051217341 / 250000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_66_sin : (-111033867722691 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 66) ∧ Real.sin (17670246 / 100000 * Real.log 66) ≤ (-888270706832599 / 1000000000000000 : ℝ) := by
  have hc := thL_66_cos_r
  have hs := thL_66_sin_r
  rw [thL_66_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_66 : (91863993984143 / 200000000000000 : ℝ) ≤ cCG cZ 66 ∧ cCG cZ 66 ≤ (114830051217341 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_cos

theorem sCB_66 : (-111033867722691 / 125000000000000 : ℝ) ≤ sCG cZ 66 ∧ sCG cZ 66 ≤ (-888270706832599 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_66_sin

theorem thL_67_r_bounds : (-713323645067410421 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 ≤ (-713299354932589579 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_67
  have hl : (742979529337716129 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 67 ∧ 17670246 / 100000 * Real.log 67 ≤ (29719181183217471 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_67_eq : (17670246 / 100000 * Real.log 67) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 + π / 2) + ((118 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_67_cos_r : (199994887598479 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) ≤ (62498417555859 / 62500000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(1426623 / 200000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) (-(1426623 / 200000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 - (-(1426623 / 200000000 : ℝ))| ≤ (12145067410421 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 - (-(1426623 / 200000000 : ℝ)))]

theorem thL_67_sin_r : (-7133175960433 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) ≤ (-7132933059083 / 1000000000000000 : ℝ) := by
  have hr := thL_67_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (1426623 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1944682939062238276607720503488466304901782795841613392377746917603191833602548049656673226039678394883846662553 / 272629760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(1426623 / 200000000 : ℝ)) ∧ Real.sin (-(1426623 / 200000000 : ℝ)) ≤ -((6544606044920994200122136309816953892489977826257163821071442343720703239277859696814491446003 / 917504000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473) (-(1426623 / 200000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 - (-(1426623 / 200000000 : ℝ))| ≤ (12145067410421 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 67) 473 - (-(1426623 / 200000000 : ℝ)))]

theorem thL_67_cos : (7132933059083 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 67) ∧ Real.cos (17670246 / 100000 * Real.log 67) ≤ (7133175960433 / 1000000000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_67_sin : (199994887598479 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 67) ∧ Real.sin (17670246 / 100000 * Real.log 67) ≤ (62498417555859 / 62500000000000 : ℝ) := by
  have hc := thL_67_cos_r
  have hs := thL_67_sin_r
  rw [thL_67_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_67 : (7132933059083 / 1000000000000000 : ℝ) ≤ cCG cZ 67 ∧ cCG cZ 67 ≤ (7133175960433 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_cos

theorem sCB_67 : (199994887598479 / 200000000000000 : ℝ) ≤ sCG cZ 67 ∧ sCG cZ 67 ≤ (62498417555859 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_67_sin

theorem thL_68_r_bounds : (-2123455154047039463 / 4000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 ≤ (-2123454149952960537 / 4000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_68
  have hl : (46599836964967823 / 62500000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 68 ∧ 17670246 / 100000 * Real.log 68 ≤ (372798695845043827 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_68_eq : (17670246 / 100000 * Real.log 68) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 + π + π / 2) + ((118 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_68_cos_r : (17247400256487 / 20000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) ≤ (215592565962229 / 250000000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(530863663 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) (-(530863663 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 - (-(530863663 / 1000000000 : ℝ))| ≤ (502047039463 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 - (-(530863663 / 1000000000 : ℝ)))]

theorem thL_68_sin_r : (-25313922631239 / 50000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) ≤ (-7910596900019 / 15625000000000 : ℝ) := by
  have hr := thL_68_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (530863663 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((286600515774725008181671812543261491916315503096100907430359141326977674703191092831529028613844403344110973875158124589420973 / 566092800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(530863663 / 1000000000 : ℝ)) ∧ Real.sin (-(530863663 / 1000000000 : ℝ)) ≤ -((1837182793427569436398224710117125209345116017557594395811681476639613572723691558271641133816297315783283 / 3628800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475) (-(530863663 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 - (-(530863663 / 1000000000 : ℝ))| ≤ (502047039463 / 4000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 68) 475 - (-(530863663 / 1000000000 : ℝ)))]

theorem thL_68_cos : (-25313922631239 / 50000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 68) ∧ Real.cos (17670246 / 100000 * Real.log 68) ≤ (-7910596900019 / 15625000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_68_sin : (-215592565962229 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 68) ∧ Real.sin (17670246 / 100000 * Real.log 68) ≤ (-17247400256487 / 20000000000000 : ℝ) := by
  have hc := thL_68_cos_r
  have hs := thL_68_sin_r
  rw [thL_68_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_68 : (-25313922631239 / 50000000000000 : ℝ) ≤ cCG cZ 68 ∧ cCG cZ 68 ≤ (-7910596900019 / 15625000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_cos

theorem sCB_68 : (-215592565962229 / 250000000000000 : ℝ) ≤ sCG cZ 68 ∧ sCG cZ 68 ≤ (-17247400256487 / 20000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_68_sin

theorem thL_69_r_bounds : (11949591341510193837 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 ≤ (11949597808489806163 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_69
  have hl : (748177035208784833 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 69 ∧ 17670246 / 100000 * Real.log 69 ≤ (748177035466710383 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_69_eq : (17670246 / 100000 * Real.log 69) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) + ((119 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_69_cos_r : (887924036957899 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) ≤ (887924295637381 / 1000000000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (477983783 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) (477983783 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 - (477983783 / 1000000000 : ℝ)| ≤ (3233489806163 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 - (477983783 / 1000000000 : ℝ))]

theorem thL_69_sin_r : (459989734575219 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) ≤ (28749374578401 / 62500000000000 : ℝ) := by
  have hr := thL_69_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (477983783 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476) (477983783 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 - (477983783 / 1000000000 : ℝ)| ≤ (3233489806163 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 69) 476 - (477983783 / 1000000000 : ℝ))]

theorem thL_69_cos : (887924036957899 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 69) ∧ Real.cos (17670246 / 100000 * Real.log 69) ≤ (887924295637381 / 1000000000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_69_sin : (459989734575219 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 69) ∧ Real.sin (17670246 / 100000 * Real.log 69) ≤ (28749374578401 / 62500000000000 : ℝ) := by
  have hc := thL_69_cos_r
  have hs := thL_69_sin_r
  rw [thL_69_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_69 : (887924036957899 / 1000000000000000 : ℝ) ≤ cCG cZ 69 ∧ cCG cZ 69 ≤ (887924295637381 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_cos

theorem sCB_69 : (459989734575219 / 1000000000000000 : ℝ) ≤ sCG cZ 69 ∧ sCG cZ 69 ≤ (28749374578401 / 62500000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_69_sin

theorem thL_71_r_bounds : (-945270567543930291 / 1250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 ≤ (-945270227456069709 / 1250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_71
  have hl : (753226020407515233 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 71 ∧ 17670246 / 100000 * Real.log 71 ≤ (94153252584824193 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_71_eq : (17670246 / 100000 * Real.log 71) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) + ((120 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_71_cos_r : (727437339624269 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) ≤ (363718805883787 / 500000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(378108159 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) (-(378108159 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 - (-(378108159 / 500000000 : ℝ))| ≤ (170043930291 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 - (-(378108159 / 500000000 : ℝ)))]

theorem thL_71_sin_r : (-686174107342991 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) ≤ (-343086917634227 / 500000000000000 : ℝ) := by
  have hr := thL_71_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (378108159 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2144293660337018647056267999163986806413723380506704528954962618701592859661457476381079541194658155500713187485193853 / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(378108159 / 500000000 : ℝ)) ∧ Real.sin (-(378108159 / 500000000 : ℝ)) ≤ -((15010055622266219702690422681251930964491831840619046183848658597254830218616117322513297492464220851 / 21875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480) (-(378108159 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 - (-(378108159 / 500000000 : ℝ))| ≤ (170043930291 / 1250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 71) 480 - (-(378108159 / 500000000 : ℝ)))]

theorem thL_71_cos : (727437339624269 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 71) ∧ Real.cos (17670246 / 100000 * Real.log 71) ≤ (363718805883787 / 500000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_71_sin : (-686174107342991 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 71) ∧ Real.sin (17670246 / 100000 * Real.log 71) ≤ (-343086917634227 / 500000000000000 : ℝ) := by
  have hc := thL_71_cos_r
  have hs := thL_71_sin_r
  rw [thL_71_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_71 : (727437339624269 / 1000000000000000 : ℝ) ≤ cCG cZ 71 ∧ cCG cZ 71 ≤ (363718805883787 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_cos

theorem sCB_71 : (-686174107342991 / 1000000000000000 : ℝ) ≤ sCG cZ 71 ∧ sCG cZ 71 ≤ (-343086917634227 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_71_sin

theorem thL_72_r_bounds : (28878116215940229593 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 ≤ (28878171784059770407 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_72
  have hl : (30227896950776999 / 40000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 72 ∧ 17670246 / 100000 * Real.log 72 ≤ (377848712023206821 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_72_eq : (17670246 / 100000 * Real.log 72) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 + π / 2) + ((120 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_72_cos_r : (989593619630989 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) ≤ (247398474367897 / 250000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (451221 / 3125000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) (451221 / 3125000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 - (451221 / 3125000 : ℝ)| ≤ (27784059770407 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 - (451221 / 3125000 : ℝ))]

theorem thL_72_sin_r : (71944688924903 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) ≤ (28777931138081 / 200000000000000 : ℝ) := by
  have hr := thL_72_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (451221 / 3125000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481) (451221 / 3125000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 - (451221 / 3125000 : ℝ)| ≤ (27784059770407 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 72) 481 - (451221 / 3125000 : ℝ))]

theorem thL_72_cos : (-28777931138081 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 72) ∧ Real.cos (17670246 / 100000 * Real.log 72) ≤ (-71944688924903 / 500000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_72_sin : (989593619630989 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 72) ∧ Real.sin (17670246 / 100000 * Real.log 72) ≤ (247398474367897 / 250000000000000 : ℝ) := by
  have hc := thL_72_cos_r
  have hs := thL_72_sin_r
  rw [thL_72_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_72 : (-28777931138081 / 200000000000000 : ℝ) ≤ cCG cZ 72 ∧ cCG cZ 72 ≤ (-71944688924903 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_cos

theorem sCB_72 : (989593619630989 / 1000000000000000 : ℝ) ≤ sCG cZ 72 ∧ sCG cZ 72 ≤ (247398474367897 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_72_sin

theorem thL_73_r_bounds : (-111977624251331618101 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 ≤ (-111977567748668381899 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_73
  have hl : (758134737720678409 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 73 ∧ 17670246 / 100000 * Real.log 73 ≤ (94766842250397613 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_73_eq : (17670246 / 100000 * Real.log 73) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 + π + π / 2) + ((120 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_73_cos_r : (169462893583333 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) ≤ (847314750431963 / 1000000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(27994399 / 50000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) (-(27994399 / 50000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 - (-(27994399 / 50000000 : ℝ))| ≤ (28251331618101 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 - (-(27994399 / 50000000 : ℝ)))]

theorem thL_73_sin_r : (-106218285265483 / 200000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) ≤ (-531091143814013 / 1000000000000000 : ℝ) := by
  have hr := thL_73_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (27994399 / 50000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((40370074204520633052703578255905278524623608411679941070304331575181584828972120025533248487991075288541847199 / 76013437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(27994399 / 50000000 : ℝ)) ∧ Real.sin (-(27994399 / 50000000 : ℝ)) ≤ -((103513010780805507255155538756823211118501998606894557773680209050906992035028137618056861601 / 194906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483) (-(27994399 / 50000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 - (-(27994399 / 50000000 : ℝ))| ≤ (28251331618101 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 73) 483 - (-(27994399 / 50000000 : ℝ)))]

theorem thL_73_cos : (-106218285265483 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 73) ∧ Real.cos (17670246 / 100000 * Real.log 73) ≤ (-531091143814013 / 1000000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_73_sin : (-847314750431963 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 73) ∧ Real.sin (17670246 / 100000 * Real.log 73) ≤ (-169462893583333 / 200000000000000 : ℝ) := by
  have hc := thL_73_cos_r
  have hs := thL_73_sin_r
  rw [thL_73_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_73 : (-106218285265483 / 200000000000000 : ℝ) ≤ cCG cZ 73 ∧ cCG cZ 73 ≤ (-531091143814013 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_cos

theorem sCB_73 : (-847314750431963 / 1000000000000000 : ℝ) ≤ sCG cZ 73 ∧ sCG cZ 73 ≤ (-169462893583333 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_73_sin

theorem thL_74_r_bounds : (13673386953941964513 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 ≤ (13673401346058035487 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_74
  have hl : (760538889907808803 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 74 ∧ 17670246 / 100000 * Real.log 74 ≤ (380269445097730049 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_74_eq : (17670246 / 100000 * Real.log 74) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_74_cos_r : (120354995704113 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) ≤ (481420126737613 / 500000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (273467883 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) (273467883 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 - (273467883 / 1000000000 : ℝ)| ≤ (7196058035487 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 - (273467883 / 1000000000 : ℝ))]

theorem thL_74_sin_r : (270071926893123 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) ≤ (135036107367723 / 500000000000000 : ℝ) := by
  have hr := thL_74_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (273467883 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484) (273467883 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 - (273467883 / 1000000000 : ℝ)| ≤ (7196058035487 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 74) 484 - (273467883 / 1000000000 : ℝ))]

theorem thL_74_cos : (120354995704113 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 74) ∧ Real.cos (17670246 / 100000 * Real.log 74) ≤ (481420126737613 / 500000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_74_sin : (270071926893123 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 74) ∧ Real.sin (17670246 / 100000 * Real.log 74) ≤ (135036107367723 / 500000000000000 : ℝ) := by
  have hc := thL_74_cos_r
  have hs := thL_74_sin_r
  rw [thL_74_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_74 : (120354995704113 / 125000000000000 : ℝ) ≤ cCG cZ 74 ∧ cCG cZ 74 ≤ (481420126737613 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_cos

theorem sCB_74 : (270071926893123 / 1000000000000000 : ℝ) ≤ sCG cZ 74 ∧ sCG cZ 74 ≤ (135036107367723 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_74_sin

theorem thL_76_r_bounds : (54684724027404086511 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 ≤ (54684783572595913489 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_76
  have hl : (382625617384625837 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 76 ∧ 17670246 / 100000 * Real.log 76 ≤ (382625617533108687 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_76_eq : (17670246 / 100000 * Real.log 76) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 + π + π / 2) + ((121 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_76_cos_r : (240712968428387 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) ≤ (240713042859877 / 250000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (273423769 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) (273423769 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 - (273423769 / 1000000000 : ℝ)| ≤ (29772595913489 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 - (273423769 / 1000000000 : ℝ))]

theorem thL_76_sin_r : (270029446959939 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) ≤ (270029744685899 / 1000000000000000 : ℝ) := by
  have hr := thL_76_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (273423769 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487) (273423769 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 - (273423769 / 1000000000 : ℝ)| ≤ (29772595913489 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 76) 487 - (273423769 / 1000000000 : ℝ))]

theorem thL_76_cos : (270029446959939 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 76) ∧ Real.cos (17670246 / 100000 * Real.log 76) ≤ (270029744685899 / 1000000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_76_sin : (-240713042859877 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 76) ∧ Real.sin (17670246 / 100000 * Real.log 76) ≤ (-240712968428387 / 250000000000000 : ℝ) := by
  have hc := thL_76_cos_r
  have hs := thL_76_sin_r
  rw [thL_76_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_76 : (270029446959939 / 1000000000000000 : ℝ) ≤ cCG cZ 76 ∧ cCG cZ 76 ≤ (270029744685899 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_cos

theorem sCB_76 : (-240713042859877 / 250000000000000 : ℝ) ≤ sCG cZ 76 ∧ sCG cZ 76 ≤ (-240712968428387 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_76_sin

theorem thL_77_r_bounds : (-111660012804788561183 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 ≤ (-111659952395211438817 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_77
  have hl : (95945137967335063 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 77 ∧ 17670246 / 100000 * Real.log 77 ≤ (767561104039861557 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_77_eq : (17670246 / 100000 * Real.log 77) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 + π / 2) + ((122 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_77_cos_r : (424078398946777 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) ≤ (169631419988671 / 200000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(558299913 / 1000000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) (-(558299913 / 1000000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 - (-(558299913 / 1000000000 : ℝ))| ≤ (30204788561183 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 - (-(558299913 / 1000000000 : ℝ)))]

theorem thL_77_sin_r : (-529745174596341 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) ≤ (-132436218137093 / 250000000000000 : ℝ) := by
  have hr := thL_77_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (558299913 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((1939290582293833328010393673224130536992093225619680508589126769807878632037560445639094696975208717942468588279308061476853 / 3660800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(558299913 / 1000000000 : ℝ)) ∧ Real.sin (-(558299913 / 1000000000 : ℝ)) ≤ -((261058347616437043458010586481725881970728916573477843050417598819625532500982455833818248323219050948023 / 492800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489) (-(558299913 / 1000000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 - (-(558299913 / 1000000000 : ℝ))| ≤ (30204788561183 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 77) 489 - (-(558299913 / 1000000000 : ℝ)))]

theorem thL_77_cos : (132436218137093 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 77) ∧ Real.cos (17670246 / 100000 * Real.log 77) ≤ (529745174596341 / 1000000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_77_sin : (424078398946777 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 77) ∧ Real.sin (17670246 / 100000 * Real.log 77) ≤ (169631419988671 / 200000000000000 : ℝ) := by
  have hc := thL_77_cos_r
  have hs := thL_77_sin_r
  rw [thL_77_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_77 : (132436218137093 / 250000000000000 : ℝ) ≤ cCG cZ 77 ∧ cCG cZ 77 ≤ (529745174596341 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_cos

theorem sCB_77 : (424078398946777 / 500000000000000 : ℝ) ≤ sCG cZ 77 ∧ sCG cZ 77 ≤ (169631419988671 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_77_sin

theorem thL_78_r_bounds : (3019339705438511497 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 ≤ (3019345814561488503 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_78
  have hl : (769841167114771269 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 78 ∧ 17670246 / 100000 * Real.log 78 ≤ (384920583709951321 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_78_eq : (17670246 / 100000 * Real.log 78) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 + π) + ((122 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_78_cos_r : (494312967753767 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) ≤ (247156560240921 / 250000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (75483569 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) (75483569 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 - (75483569 / 500000000 : ℝ)| ≤ (3054561488503 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 - (75483569 / 500000000 : ℝ))]

theorem thL_78_sin_r : (75197093895153 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) ≤ (18799311655807 / 125000000000000 : ℝ) := by
  have hr := thL_78_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (75483569 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490) (75483569 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 - (75483569 / 500000000 : ℝ)| ≤ (3054561488503 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 78) 490 - (75483569 / 500000000 : ℝ))]

theorem thL_78_cos : (-247156560240921 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 78) ∧ Real.cos (17670246 / 100000 * Real.log 78) ≤ (-494312967753767 / 500000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_78_sin : (-18799311655807 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 78) ∧ Real.sin (17670246 / 100000 * Real.log 78) ≤ (-75197093895153 / 500000000000000 : ℝ) := by
  have hc := thL_78_cos_r
  have hs := thL_78_sin_r
  rw [thL_78_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_78 : (-247156560240921 / 250000000000000 : ℝ) ≤ cCG cZ 78 ∧ cCG cZ 78 ≤ (-494312967753767 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_cos

theorem sCB_78 : (-18799311655807 / 125000000000000 : ℝ) ≤ sCG cZ 78 ∧ sCG cZ 78 ≤ (-75197093895153 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_78_sin

theorem thL_79_r_bounds : (-18490211916319733471 / 25000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 ≤ (-18490204183680266529 / 25000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_79
  have hl : (386046092153452761 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 79 ∧ 17670246 / 100000 * Real.log 79 ≤ (386046092307870963 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_79_eq : (17670246 / 100000 * Real.log 79) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) + ((123 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_79_cos_r : (738732451110087 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) ≤ (369366380235801 / 500000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(369804161 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) (-(369804161 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 - (-(369804161 / 500000000 : ℝ))| ≤ (3866319733471 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 - (-(369804161 / 500000000 : ℝ)))]

theorem thL_79_sin_r : (-673998772678381 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) ≤ (-673998463369619 / 1000000000000000 : ℝ) := by
  have hr := thL_79_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (369804161 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((512329518263746319518662963558912969671156811401675528746152178351693149907203344524398749293180742880307036737762285546881 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(369804161 / 500000000 : ℝ)) ∧ Real.sin (-(369804161 / 500000000 : ℝ)) ≤ -((13136654314393008557402853134924314829675049687277924635155245376401309582741678399231728844461184506239 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492) (-(369804161 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 - (-(369804161 / 500000000 : ℝ))| ≤ (3866319733471 / 25000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 79) 492 - (-(369804161 / 500000000 : ℝ)))]

theorem thL_79_cos : (738732451110087 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 79) ∧ Real.cos (17670246 / 100000 * Real.log 79) ≤ (369366380235801 / 500000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_79_sin : (-673998772678381 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 79) ∧ Real.sin (17670246 / 100000 * Real.log 79) ≤ (-673998463369619 / 1000000000000000 : ℝ) := by
  have hc := thL_79_cos_r
  have hs := thL_79_sin_r
  rw [thL_79_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_79 : (738732451110087 / 1000000000000000 : ℝ) ≤ cCG cZ 79 ∧ cCG cZ 79 ≤ (369366380235801 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_cos

theorem sCB_79 : (-673998772678381 / 1000000000000000 : ℝ) ≤ sCG cZ 79 ∧ sCG cZ 79 ≤ (-673998463369619 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_79_sin

theorem thL_81_r_bounds : (53659047177828909791 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 ≤ (53659078822171090209 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_81
  have hl : (776509975908457219 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 81 ∧ 17670246 / 100000 * Real.log 81 ≤ (776509976224038501 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_81_eq : (17670246 / 100000 * Real.log 81) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 + π) + ((123 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_81_cos_r : (859456414657049 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) ≤ (429728365550831 / 500000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (53659063 / 100000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) (53659063 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 - (53659063 / 100000000 : ℝ)| ≤ (15822171090209 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 - (53659063 / 100000000 : ℝ))]

theorem thL_81_sin_r : (511208604744461 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) ≤ (127802230296983 / 250000000000000 : ℝ) := by
  have hr := thL_81_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (53659063 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494) (53659063 / 100000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 - (53659063 / 100000000 : ℝ)| ≤ (15822171090209 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 81) 494 - (53659063 / 100000000 : ℝ))]

theorem thL_81_cos : (-429728365550831 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 81) ∧ Real.cos (17670246 / 100000 * Real.log 81) ≤ (-859456414657049 / 1000000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_81_sin : (-127802230296983 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 81) ∧ Real.sin (17670246 / 100000 * Real.log 81) ≤ (-511208604744461 / 1000000000000000 : ℝ) := by
  have hc := thL_81_cos_r
  have hs := thL_81_sin_r
  rw [thL_81_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_81 : (-429728365550831 / 500000000000000 : ℝ) ≤ cCG cZ 81 ∧ cCG cZ 81 ≤ (-859456414657049 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_cos

theorem sCB_81 : (-127802230296983 / 250000000000000 : ℝ) ≤ sCG cZ 81 ∧ sCG cZ 81 ≤ (-511208604744461 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_81_sin

theorem thL_82_r_bounds : (-2730291485177236637 / 6250000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 ≤ (-2730289489822763363 / 6250000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_82
  have hl : (97334766431655537 / 125000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 82 ∧ 17670246 / 100000 * Real.log 82 ≤ (778678131771897081 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_82_eq : (17670246 / 100000 * Real.log 82) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_82_cos_r : (453045106050149 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) ≤ (181218106271423 / 200000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(218423239 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) (-(218423239 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 - (-(218423239 / 500000000 : ℝ))| ≤ (997677236637 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 - (-(218423239 / 500000000 : ℝ)))]

theorem thL_82_sin_r : (-211542178615129 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) ≤ (-211542018986769 / 500000000000000 : ℝ) := by
  have hr := thL_82_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (218423239 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((321600842116496501724880160819103879918607195549148471748546337083311024211059795322175966237586243581044664414575862353319 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(218423239 / 500000000 : ℝ)) ∧ Real.sin (-(218423239 / 500000000 : ℝ)) ≤ -((8246175438884459643232844475133528284907104187274137350330050583621141868738551501419276420253589752361 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496) (-(218423239 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 - (-(218423239 / 500000000 : ℝ))| ≤ (997677236637 / 6250000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 82) 496 - (-(218423239 / 500000000 : ℝ)))]

theorem thL_82_cos : (453045106050149 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 82) ∧ Real.cos (17670246 / 100000 * Real.log 82) ≤ (181218106271423 / 200000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_82_sin : (-211542178615129 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 82) ∧ Real.sin (17670246 / 100000 * Real.log 82) ≤ (-211542018986769 / 500000000000000 : ℝ) := by
  have hc := thL_82_cos_r
  have hs := thL_82_sin_r
  rw [thL_82_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_82 : (453045106050149 / 500000000000000 : ℝ) ≤ cCG cZ 82 ∧ cCG cZ 82 ≤ (181218106271423 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_cos

theorem sCB_82 : (-211542178615129 / 500000000000000 : ℝ) ≤ sCG cZ 82 ∧ sCG cZ 82 ≤ (-211542018986769 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_82_sin

theorem thL_83_r_bounds : (26846252042991648041 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 ≤ (26846316357008351959 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_83
  have hl : (390410002838639289 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 83 ∧ 17670246 / 100000 * Real.log 83 ≤ (78082000599882117 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_83_eq : (17670246 / 100000 * Real.log 83) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 + π / 2) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_83_cos_r : (495502160513247 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) ≤ (991004642596579 / 1000000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (134231421 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) (134231421 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 - (134231421 / 1000000000 : ℝ)| ≤ (32157008351959 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 - (134231421 / 1000000000 : ℝ))]

theorem thL_83_sin_r : (133828524590883 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) ≤ (16728605770121 / 125000000000000 : ℝ) := by
  have hr := thL_83_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (134231421 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497) (134231421 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 - (134231421 / 1000000000 : ℝ)| ≤ (32157008351959 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 83) 497 - (134231421 / 1000000000 : ℝ))]

theorem thL_83_cos : (-16728605770121 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 83) ∧ Real.cos (17670246 / 100000 * Real.log 83) ≤ (-133828524590883 / 1000000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_83_sin : (495502160513247 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 83) ∧ Real.sin (17670246 / 100000 * Real.log 83) ≤ (991004642596579 / 1000000000000000 : ℝ) := by
  have hc := thL_83_cos_r
  have hs := thL_83_sin_r
  rw [thL_83_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_83 : (-16728605770121 / 125000000000000 : ℝ) ≤ cCG cZ 83 ∧ cCG cZ 83 ≤ (-133828524590883 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_cos

theorem sCB_83 : (495502160513247 / 500000000000000 : ℝ) ≤ sCG cZ 83 ∧ sCG cZ 83 ≤ (991004642596579 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_83_sin

theorem thL_84_r_bounds : (33982867573800868827 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 ≤ (33982883826199131173 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_84
  have hl : (15658724561922381 / 20000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 84 ∧ 17670246 / 100000 * Real.log 84 ≤ (782936228420382499 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_84_eq : (17670246 / 100000 * Real.log 84) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 + π) + ((124 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_84_cos_r : (388893931703393 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) ≤ (155557637695007 / 200000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (339828757 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) (339828757 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 - (339828757 / 500000000 : ℝ)| ≤ (8126199131173 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 - (339828757 / 500000000 : ℝ))]

theorem thL_84_sin_r : (628526516850819 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) ≤ (314263420949923 / 500000000000000 : ℝ) := by
  have hr := thL_84_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (339828757 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498) (339828757 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 - (339828757 / 500000000 : ℝ)| ≤ (8126199131173 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 84) 498 - (339828757 / 500000000 : ℝ))]

theorem thL_84_cos : (-155557637695007 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 84) ∧ Real.cos (17670246 / 100000 * Real.log 84) ≤ (-388893931703393 / 500000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_84_sin : (-314263420949923 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 84) ∧ Real.sin (17670246 / 100000 * Real.log 84) ≤ (-628526516850819 / 1000000000000000 : ℝ) := by
  have hc := thL_84_cos_r
  have hs := thL_84_sin_r
  rw [thL_84_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_84 : (-155557637695007 / 200000000000000 : ℝ) ≤ cCG cZ 84 ∧ cCG cZ 84 ≤ (-388893931703393 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_cos

theorem sCB_84 : (-314263420949923 / 500000000000000 : ℝ) ≤ sCG cZ 84 ∧ sCG cZ 84 ≤ (-628526516850819 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_84_sin

theorem thL_86_r_bounds : (25033029656924952653 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 ≤ (25033095543075047347 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_86
  have hl : (787094124872527831 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 86 ∧ 17670246 / 100000 * Real.log 86 ≤ (98386765650221509 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_86_eq : (17670246 / 100000 * Real.log 86) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 + π / 2) + ((125 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_86_cos_r : (496088439301133 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) ≤ (992177208033017 / 1000000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (125165313 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) (125165313 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 - (125165313 / 1000000000 : ℝ)| ≤ (32943075047347 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 - (125165313 / 1000000000 : ℝ))]

theorem thL_86_sin_r : (15604823767311 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) ≤ (124838919569239 / 1000000000000000 : ℝ) := by
  have hr := thL_86_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (125165313 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501) (125165313 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 - (125165313 / 1000000000 : ℝ)| ≤ (32943075047347 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 86) 501 - (125165313 / 1000000000 : ℝ))]

theorem thL_86_cos : (-124838919569239 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 86) ∧ Real.cos (17670246 / 100000 * Real.log 86) ≤ (-15604823767311 / 125000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_86_sin : (496088439301133 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 86) ∧ Real.sin (17670246 / 100000 * Real.log 86) ≤ (992177208033017 / 1000000000000000 : ℝ) := by
  have hc := thL_86_cos_r
  have hs := thL_86_sin_r
  rw [thL_86_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_86 : (-124838919569239 / 1000000000000000 : ℝ) ≤ cCG cZ 86 ∧ cCG cZ 86 ≤ (-15604823767311 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_cos

theorem sCB_86 : (496088439301133 / 500000000000000 : ℝ) ≤ sCG cZ 86 ∧ sCG cZ 86 ≤ (992177208033017 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_86_sin

theorem thL_87_r_bounds : (59719457892683814403 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 ≤ (59719491107316185597 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_87
  have hl : (789136950629964941 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 87 ∧ 17670246 / 100000 * Real.log 87 ≤ (789136950961489821 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_87_eq : (17670246 / 100000 * Real.log 87) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 + π) + ((125 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_87_cos_r : (103364520675947 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) ≤ (826916497558197 / 1000000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (119438949 / 200000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) (119438949 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 - (119438949 / 200000000 : ℝ)| ≤ (16607316185597 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 - (119438949 / 200000000 : ℝ))]

theorem thL_87_sin_r : (140581202946237 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) ≤ (56232514393147 / 100000000000000 : ℝ) := by
  have hr := thL_87_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (119438949 / 200000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502) (119438949 / 200000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 - (119438949 / 200000000 : ℝ)| ≤ (16607316185597 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 87) 502 - (119438949 / 200000000 : ℝ))]

theorem thL_87_cos : (-826916497558197 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 87) ∧ Real.cos (17670246 / 100000 * Real.log 87) ≤ (-103364520675947 / 125000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_87_sin : (-56232514393147 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 87) ∧ Real.sin (17670246 / 100000 * Real.log 87) ≤ (-140581202946237 / 250000000000000 : ℝ) := by
  have hc := thL_87_cos_r
  have hs := thL_87_sin_r
  rw [thL_87_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_87 : (-826916497558197 / 1000000000000000 : ℝ) ≤ cCG cZ 87 ∧ cCG cZ 87 ≤ (-103364520675947 / 125000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_cos

theorem sCB_87 : (-56232514393147 / 100000000000000 : ℝ) ≤ sCG cZ 87 ∧ sCG cZ 87 ≤ (-140581202946237 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_87_sin

theorem thL_88_r_bounds : (-6561492615130048851 / 12500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 ≤ (-6561488434869951149 / 12500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_88
  have hl : (4944727683101001 / 6250000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 88 ∧ 17670246 / 100000 * Real.log 88 ≤ (7911564296298383 / 10000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_88_eq : (17670246 / 100000 * Real.log 88) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_88_cos_r : (432682124274827 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) ≤ (54085286435711 / 62500000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(262459621 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) (-(262459621 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 - (-(262459621 / 500000000 : ℝ))| ≤ (2090130048851 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 - (-(262459621 / 500000000 : ℝ)))]

theorem thL_88_sin_r : (-250571644209491 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) ≤ (-62642869249767 / 125000000000000 : ℝ) := by
  have hr := thL_88_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (262459621 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((380936113225431007670606186002676391881646962535252186792408776961337225250291283976487079780762848799474485284262917846261 / 760134375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(262459621 / 500000000 : ℝ)) ∧ Real.sin (-(262459621 / 500000000 : ℝ)) ≤ -((9767592646805204242201558480552109886106016662621337106093192672827368636951547673643977633765511682179 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504) (-(262459621 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 - (-(262459621 / 500000000 : ℝ))| ≤ (2090130048851 / 12500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 88) 504 - (-(262459621 / 500000000 : ℝ)))]

theorem thL_88_cos : (432682124274827 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 88) ∧ Real.cos (17670246 / 100000 * Real.log 88) ≤ (54085286435711 / 62500000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_88_sin : (-250571644209491 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 88) ∧ Real.sin (17670246 / 100000 * Real.log 88) ≤ (-62642869249767 / 125000000000000 : ℝ) := by
  have hc := thL_88_cos_r
  have hs := thL_88_sin_r
  rw [thL_88_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_88 : (432682124274827 / 500000000000000 : ℝ) ≤ cCG cZ 88 ∧ cCG cZ 88 ≤ (54085286435711 / 62500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_cos

theorem sCB_88 : (-250571644209491 / 500000000000000 : ℝ) ≤ sCG cZ 88 ∧ sCG cZ 88 ≤ (-62642869249767 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_88_sin

theorem thL_89_r_bounds : (-1981130526378425777 / 20000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 ≤ (-1981123793621574223 / 20000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_89
  have hl : (793153088506029249 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 89 ∧ 17670246 / 100000 * Real.log 89 ≤ (396576544420870857 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_89_eq : (17670246 / 100000 * Real.log 89) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 + π / 2) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_89_cos_r : (995097760944291 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) ≤ (199019619516427 / 200000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(49528179 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) (-(49528179 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 - (-(49528179 / 500000000 : ℝ))| ≤ (3366378425777 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 - (-(49528179 / 500000000 : ℝ)))]

theorem thL_89_sin_r : (-3955784517429 / 40000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) ≤ (-98894276297881 / 1000000000000000 : ℝ) := by
  have hr := thL_89_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (49528179 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((309354184566937424059729461245536621239837775388708359906043338297623737050677194415057735348324127255496956225499373873 / 3128125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(49528179 / 500000000 : ℝ)) ∧ Real.sin (-(49528179 / 500000000 : ℝ)) ≤ -((23796475735918263389206542453522724128046835462198862451568840387890742546327742207185125690034472741 / 240625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505) (-(49528179 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 - (-(49528179 / 500000000 : ℝ))| ≤ (3366378425777 / 20000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 89) 505 - (-(49528179 / 500000000 : ℝ)))]

theorem thL_89_cos : (98894276297881 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 89) ∧ Real.cos (17670246 / 100000 * Real.log 89) ≤ (3955784517429 / 40000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_89_sin : (995097760944291 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 89) ∧ Real.sin (17670246 / 100000 * Real.log 89) ≤ (199019619516427 / 200000000000000 : ℝ) := by
  have hc := thL_89_cos_r
  have hs := thL_89_sin_r
  rw [thL_89_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_89 : (98894276297881 / 1000000000000000 : ℝ) ≤ cCG cZ 89 ∧ cCG cZ 89 ≤ (3955784517429 / 40000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_cos

theorem sCB_89 : (995097760944291 / 1000000000000000 : ℝ) ≤ sCG cZ 89 ∧ sCG cZ 89 ≤ (199019619516427 / 200000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_89_sin

theorem thL_91_r_bounds : (137246751808593009571 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 ≤ (137246819791406990429 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_91
  have hl : (797079971444055551 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 91 ∧ 17670246 / 100000 * Real.log 91 ≤ (797079971783510453 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_91_eq : (17670246 / 100000 * Real.log 91) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 + π + π / 2) + ((126 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_91_cos_r : (77363761417617 / 100000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) ≤ (77363795411301 / 100000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (686233929 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) (686233929 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 - (686233929 / 1000000000 : ℝ)| ≤ (33991406990429 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 - (686233929 / 1000000000 : ℝ))]

theorem thL_91_sin_r : (316813968894099 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) ≤ (633628277703471 / 1000000000000000 : ℝ) := by
  have hr := thL_91_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (686233929 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507) (686233929 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 - (686233929 / 1000000000 : ℝ)| ≤ (33991406990429 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 91) 507 - (686233929 / 1000000000 : ℝ))]

theorem thL_91_cos : (316813968894099 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 91) ∧ Real.cos (17670246 / 100000 * Real.log 91) ≤ (633628277703471 / 1000000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_91_sin : (-77363795411301 / 100000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 91) ∧ Real.sin (17670246 / 100000 * Real.log 91) ≤ (-77363761417617 / 100000000000000 : ℝ) := by
  have hc := thL_91_cos_r
  have hs := thL_91_sin_r
  rw [thL_91_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_91 : (316813968894099 / 500000000000000 : ℝ) ≤ cCG cZ 91 ∧ cCG cZ 91 ≤ (633628277703471 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_cos

theorem sCB_91 : (-77363795411301 / 100000000000000 : ℝ) ≤ sCG cZ 91 ∧ sCG cZ 91 ≤ (-77363761417617 / 100000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_91_sin

theorem thL_92_r_bounds : (-52416524683719681193 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 ≤ (-52416490516280318807 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_92
  have hl : (399505582546131343 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 92 ∧ 17670246 / 100000 * Real.log 92 ≤ (99876395679179947 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_92_eq : (17670246 / 100000 * Real.log 92) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 + π / 2) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_92_cos_r : (108217742986891 / 125000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) ≤ (43287114278521 / 50000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(131041269 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) (-(131041269 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 - (-(131041269 / 250000000 : ℝ))| ≤ (17083719681193 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 - (-(131041269 / 250000000 : ℝ)))]

theorem thL_92_sin_r : (-500490521170997 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) ≤ (-250245089748283 / 500000000000000 : ℝ) := by
  have hr := thL_92_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (131041269 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((191112839006093238534790064650728549358259625124381474410692719438900827695599991657225445880809436013870717039721063 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(131041269 / 250000000 : ℝ)) ∧ Real.sin (-(131041269 / 250000000 : ℝ)) ≤ -((58803950463409049987728361701244871156177441406686411005288701068721985742899327474580218173604451 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509) (-(131041269 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 - (-(131041269 / 250000000 : ℝ))| ≤ (17083719681193 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 92) 509 - (-(131041269 / 250000000 : ℝ)))]

theorem thL_92_cos : (250245089748283 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 92) ∧ Real.cos (17670246 / 100000 * Real.log 92) ≤ (500490521170997 / 1000000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_92_sin : (108217742986891 / 125000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 92) ∧ Real.sin (17670246 / 100000 * Real.log 92) ≤ (43287114278521 / 50000000000000 : ℝ) := by
  have hc := thL_92_cos_r
  have hs := thL_92_sin_r
  rw [thL_92_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_92 : (250245089748283 / 500000000000000 : ℝ) ≤ cCG cZ 92 ∧ cCG cZ 92 ≤ (500490521170997 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_cos

theorem sCB_92 : (108217742986891 / 125000000000000 : ℝ) ≤ sCG cZ 92 ∧ sCG cZ 92 ≤ (43287114278521 / 50000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_92_sin

theorem thL_93_r_bounds : (-1846461038155391927 / 10000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 ≤ (-1846457601844608073 / 10000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_93
  have hl : (800921480562405027 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 93 ∧ 17670246 / 100000 * Real.log 93 ≤ (160184296181042563 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_93_eq : (17670246 / 100000 * Real.log 93) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 + π) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_93_cos_r : (491500573391041 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) ≤ (983001490413161 / 1000000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(46161483 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) (-(46161483 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 - (-(46161483 / 250000000 : ℝ))| ≤ (1718155391927 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 - (-(46161483 / 250000000 : ℝ)))]

theorem thL_93_sin_r : (-91799333774157 / 500000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) ≤ (-36719664783447 / 200000000000000 : ℝ) := by
  have hr := thL_93_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (46161483 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((70107305232432305932823420684343796878008797698329579497846531048663654011089593925870359074408098837339154432785241 / 381851196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(46161483 / 250000000 : ℝ)) ∧ Real.sin (-(46161483 / 250000000 : ℝ)) ≤ -((21571478533056094127704423760207882239000138234399604332391684038631392911158581008646350518313693 / 117492675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510) (-(46161483 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 - (-(46161483 / 250000000 : ℝ))| ≤ (1718155391927 / 10000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 93) 510 - (-(46161483 / 250000000 : ℝ)))]

theorem thL_93_cos : (-983001490413161 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 93) ∧ Real.cos (17670246 / 100000 * Real.log 93) ≤ (-491500573391041 / 500000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_93_sin : (36719664783447 / 200000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 93) ∧ Real.sin (17670246 / 100000 * Real.log 93) ≤ (91799333774157 / 500000000000000 : ℝ) := by
  have hc := thL_93_cos_r
  have hs := thL_93_sin_r
  rw [thL_93_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_93 : (-983001490413161 / 1000000000000000 : ℝ) ≤ cCG cZ 93 ∧ cCG cZ 93 ≤ (-491500573391041 / 500000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_cos

theorem sCB_93 : (36719664783447 / 200000000000000 : ℝ) ≤ sCG cZ 93 ∧ sCG cZ 93 ≤ (91799333774157 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_93_sin

theorem thL_94_r_bounds : (13444146640234142653 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 ≤ (13444181159765857347 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_94
  have hl : (200702841114859129 / 250000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 94 ∧ 17670246 / 100000 * Real.log 94 ≤ (802811364803789831 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_94_eq : (17670246 / 100000 * Real.log 94) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 + π + π / 2) + ((127 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_94_cos_r : (495488077059231 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) ≤ (49548824965689 / 50000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (134441639 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) (134441639 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 - (134441639 / 1000000000 : ℝ)| ≤ (17259765857347 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 - (134441639 / 1000000000 : ℝ))]

theorem thL_94_sin_r : (134036836799837 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) ≤ (26807436399031 / 200000000000000 : ℝ) := by
  have hr := thL_94_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (134441639 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511) (134441639 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 - (134441639 / 1000000000 : ℝ)| ≤ (17259765857347 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 94) 511 - (134441639 / 1000000000 : ℝ))]

theorem thL_94_cos : (134036836799837 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 94) ∧ Real.cos (17670246 / 100000 * Real.log 94) ≤ (26807436399031 / 200000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_94_sin : (-49548824965689 / 50000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 94) ∧ Real.sin (17670246 / 100000 * Real.log 94) ≤ (-495488077059231 / 500000000000000 : ℝ) := by
  have hc := thL_94_cos_r
  have hs := thL_94_sin_r
  rw [thL_94_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_94 : (134036836799837 / 1000000000000000 : ℝ) ≤ cCG cZ 94 ∧ cCG cZ 94 ≤ (26807436399031 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_cos

theorem sCB_94 : (-49548824965689 / 50000000000000 : ℝ) ≤ sCG cZ 94 ∧ sCG cZ 94 ≤ (-495488077059231 / 500000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_94_sin

theorem thL_96_r_bounds : (71303800906389266499 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 ≤ (71303835693610733501 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_96
  have hl : (806531553655508963 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 96 ∧ 17670246 / 100000 * Real.log 96 ≤ (806531554002718073 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_96_eq : (17670246 / 100000 * Real.log 96) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 + π / 2) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_96_cos_r : (756377814735013 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) ≤ (94547270330411 / 125000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (713038183 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) (713038183 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 - (713038183 / 1000000000 : ℝ)| ≤ (17393610733501 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 - (713038183 / 1000000000 : ℝ))]

theorem thL_96_sin_r : (163533656826653 / 250000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) ≤ (130826995036161 / 200000000000000 : ℝ) := by
  have hr := thL_96_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (713038183 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513) (713038183 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 - (713038183 / 1000000000 : ℝ)| ≤ (17393610733501 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 96) 513 - (713038183 / 1000000000 : ℝ))]

theorem thL_96_cos : (-130826995036161 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 96) ∧ Real.cos (17670246 / 100000 * Real.log 96) ≤ (-163533656826653 / 250000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_96_sin : (756377814735013 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 96) ∧ Real.sin (17670246 / 100000 * Real.log 96) ≤ (94547270330411 / 125000000000000 : ℝ) := by
  have hc := thL_96_cos_r
  have hs := thL_96_sin_r
  rw [thL_96_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_96 : (-130826995036161 / 200000000000000 : ℝ) ≤ cCG cZ 96 ∧ cCG cZ 96 ≤ (-163533656826653 / 250000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_cos

theorem sCB_96 : (756377814735013 / 1000000000000000 : ℝ) ≤ sCG cZ 96 ∧ sCG cZ 96 ≤ (94547270330411 / 125000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_96_sin

theorem thL_97_r_bounds : (-23896987299582356241 / 40000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 ≤ (-23896973340417643759 / 40000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_97
  have hl : (4041813418084411 / 5000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 97 ∧ 17670246 / 100000 * Real.log 97 ≤ (808362683965411079 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_97_eq : (17670246 / 100000 * Real.log 97) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 + π + π / 2) + ((128 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_97_cos_r : (206696733422881 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) ≤ (413393641337479 / 500000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(149356127 / 250000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) (-(149356127 / 250000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 - (-(149356127 / 250000000 : ℝ))| ≤ (6979582356241 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 - (-(149356127 / 250000000 : ℝ)))]

theorem thL_97_sin_r : (-70314391535051 / 125000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) ≤ (-562514783301091 / 1000000000000000 : ℝ) := by
  have hr := thL_97_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (149356127 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((52195673323791245025257541109826993696319483378142145440768047699926457294312895142170914137642273893832142838685561567 / 92789840698242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(149356127 / 250000000 : ℝ)) ∧ Real.sin (-(149356127 / 250000000 : ℝ)) ≤ -((5353402392181829903777663257863741038570188577821117591212738264311116259297456749637664940612996577 / 9516906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515) (-(149356127 / 250000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 - (-(149356127 / 250000000 : ℝ))| ≤ (6979582356241 / 40000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 97) 515 - (-(149356127 / 250000000 : ℝ)))]

theorem thL_97_cos : (-70314391535051 / 125000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 97) ∧ Real.cos (17670246 / 100000 * Real.log 97) ≤ (-562514783301091 / 1000000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_97_sin : (-413393641337479 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 97) ∧ Real.sin (17670246 / 100000 * Real.log 97) ≤ (-206696733422881 / 250000000000000 : ℝ) := by
  have hc := thL_97_cos_r
  have hs := thL_97_sin_r
  rw [thL_97_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_97 : (-70314391535051 / 125000000000000 : ℝ) ≤ cCG cZ 97 ∧ cCG cZ 97 ≤ (-562514783301091 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_cos

theorem sCB_97 : (-413393641337479 / 500000000000000 : ℝ) ≤ sCG cZ 97 ∧ sCG cZ 97 ≤ (-206696733422881 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_97_sin

theorem thL_98_r_bounds : (-17793609950121076263 / 50000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 ≤ (-17793592449878923737 / 50000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_98
  have hl : (405087516213582117 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 98 ∧ 17670246 / 100000 * Real.log 98 ≤ (32407001311077863 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_98_eq : (17670246 / 100000 * Real.log 98) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_98_cos_r : (187468570041877 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) ≤ (937343200214237 / 1000000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(44484003 / 125000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) (-(44484003 / 125000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 - (-(44484003 / 125000000 : ℝ))| ≤ (8750121076263 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 - (-(44484003 / 125000000 : ℝ)))]

theorem thL_98_sin_r : (-348408058218003 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) ≤ (-348407708213159 / 1000000000000000 : ℝ) := by
  have hr := thL_98_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (44484003 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((2320032906710547890150008932257734048922963544968728405821925465123066282724569246763790091554626992003628087223 / 6658956408500671386718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(44484003 / 125000000 : ℝ)) ∧ Real.sin (-(44484003 / 125000000 : ℝ)) ≤ -((19987975811660091372160107331361211546122591235181474421741515509939086000217018979771842801813 / 57369470596313476562500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516) (-(44484003 / 125000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 - (-(44484003 / 125000000 : ℝ))| ≤ (8750121076263 / 50000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 98) 516 - (-(44484003 / 125000000 : ℝ)))]

theorem thL_98_cos : (187468570041877 / 200000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 98) ∧ Real.cos (17670246 / 100000 * Real.log 98) ≤ (937343200214237 / 1000000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_98_sin : (-348408058218003 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 98) ∧ Real.sin (17670246 / 100000 * Real.log 98) ≤ (-348407708213159 / 1000000000000000 : ℝ) := by
  have hc := thL_98_cos_r
  have hs := thL_98_sin_r
  rw [thL_98_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_98 : (187468570041877 / 200000000000000 : ℝ) ≤ cCG cZ 98 ∧ cCG cZ 98 ≤ (937343200214237 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_cos

theorem sCB_98 : (-348408058218003 / 1000000000000000 : ℝ) ≤ sCG cZ 98 ∧ sCG cZ 98 ≤ (-348407708213159 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_98_sin

theorem thL_99_r_bounds : (-26543902701951028899 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 ≤ (-26543832498048971101 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_99
  have hl : (811968981439451797 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 99 ∧ 17670246 / 100000 * Real.log 99 ≤ (3247875927161701 / 4000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_99_eq : (17670246 / 100000 * Real.log 99) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 + π / 2) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_99_cos_r : (247801383347777 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) ≤ (991205884410619 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (-(66359669 / 500000000 : ℝ))) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) (-(66359669 / 500000000 : ℝ)))
  rw [Real.cos_neg] at hlip
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 - (-(66359669 / 500000000 : ℝ))| ≤ (35101951028899 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 - (-(66359669 / 500000000 : ℝ)))]

theorem thL_99_sin_r : (-132330227434241 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) ≤ (-132329876414729 / 1000000000000000 : ℝ) := by
  have hr := thL_99_r_bounds
  have hs0 := PsiOmega.Num.sin_bounds (x := (66359669 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0
  norm_num at hs0
  have hs : -((14369803044762265119262513013463926996148580973374733144810749554940539869471968921806424970831653312424600729724740392787 / 108590625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ Real.sin (-(66359669 / 500000000 : ℝ)) ∧ Real.sin (-(66359669 / 500000000 : ℝ)) ≤ -((2579195418290662970111633130055705820865491970671020196741072084839419170840468620614872089396931538131 / 19490625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by
    rw [Real.sin_neg]
    constructor <;> linarith [hs0.1, hs0.2]
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517) (-(66359669 / 500000000 : ℝ)))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 - (-(66359669 / 500000000 : ℝ))| ≤ (35101951028899 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 99) 517 - (-(66359669 / 500000000 : ℝ)))]

theorem thL_99_cos : (132329876414729 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 99) ∧ Real.cos (17670246 / 100000 * Real.log 99) ≤ (132330227434241 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_99_sin : (247801383347777 / 250000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 99) ∧ Real.sin (17670246 / 100000 * Real.log 99) ≤ (991205884410619 / 1000000000000000 : ℝ) := by
  have hc := thL_99_cos_r
  have hs := thL_99_sin_r
  rw [thL_99_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_99 : (132329876414729 / 1000000000000000 : ℝ) ≤ cCG cZ 99 ∧ cCG cZ 99 ≤ (132330227434241 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_cos

theorem sCB_99 : (247801383347777 / 250000000000000 : ℝ) ≤ sCG cZ 99 ∧ sCG cZ 99 ≤ (991205884410619 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_99_sin

theorem thL_101_r_bounds : (51970968233425123407 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 ≤ (51971038966574876593 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_101
  have hl : (815503148447718471 / 1000000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 101 ∧ 17670246 / 100000 * Real.log 101 ≤ (203875787200225397 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_101_eq : (17670246 / 100000 * Real.log 101) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 + π + π / 2) + ((129 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_101_cos_r : (966427063197429 / 1000000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) ≤ (966427416863179 / 1000000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (129927509 / 500000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) (129927509 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 - (129927509 / 500000000 : ℝ)| ≤ (35366574876593 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 - (129927509 / 500000000 : ℝ))]

theorem thL_101_sin_r : (256940263206073 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) ≤ (256940616871823 / 1000000000000000 : ℝ) := by
  have hr := thL_101_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (129927509 / 500000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519) (129927509 / 500000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 - (129927509 / 500000000 : ℝ)| ≤ (35366574876593 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 101) 519 - (129927509 / 500000000 : ℝ))]

theorem thL_101_cos : (256940263206073 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 101) ∧ Real.cos (17670246 / 100000 * Real.log 101) ≤ (256940616871823 / 1000000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_101_sin : (-966427416863179 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 101) ∧ Real.sin (17670246 / 100000 * Real.log 101) ≤ (-966427063197429 / 1000000000000000 : ℝ) := by
  have hc := thL_101_cos_r
  have hs := thL_101_sin_r
  rw [thL_101_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_101 : (256940263206073 / 1000000000000000 : ℝ) ≤ cCG cZ 101 ∧ cCG cZ 101 ≤ (256940616871823 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_cos

theorem sCB_101 : (-966427416863179 / 1000000000000000 : ℝ) ≤ sCG cZ 101 ∧ sCG cZ 101 ≤ (-966427063197429 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_101_sin

theorem thL_102_r_bounds : (1074958828737747499 / 2500000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 ≤ (1074959716262252501 / 2500000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_102
  have hl : (20431101836641071 / 25000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 102 ∧ 17670246 / 100000 * Real.log 102 ≤ (817244073819851143 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_102_eq : (17670246 / 100000 * Real.log 102) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_102_cos_r : (227243090822881 / 250000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) ≤ (908972718301411 / 1000000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (429983709 / 1000000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) (429983709 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 - (429983709 / 1000000000 : ℝ)| ≤ (443762252501 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 - (429983709 / 1000000000 : ℝ))]

theorem thL_102_sin_r : (416855816907961 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) ≤ (416856171917767 / 1000000000000000 : ℝ) := by
  have hr := thL_102_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (429983709 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520) (429983709 / 1000000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 - (429983709 / 1000000000 : ℝ)| ≤ (443762252501 / 2500000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 102) 520 - (429983709 / 1000000000 : ℝ))]

theorem thL_102_cos : (227243090822881 / 250000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 102) ∧ Real.cos (17670246 / 100000 * Real.log 102) ≤ (908972718301411 / 1000000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.cos_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_102_sin : (416855816907961 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 102) ∧ Real.sin (17670246 / 100000 * Real.log 102) ≤ (416856171917767 / 1000000000000000 : ℝ) := by
  have hc := thL_102_cos_r
  have hs := thL_102_sin_r
  rw [thL_102_eq]
  rw [Real.sin_add_int_mul_two_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_102 : (227243090822881 / 250000000000000 : ℝ) ≤ cCG cZ 102 ∧ cCG cZ 102 ≤ (908972718301411 / 1000000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_cos

theorem sCB_102 : (416855816907961 / 1000000000000000 : ℝ) ≤ sCG cZ 102 ∧ sCG cZ 102 ≤ (416856171917767 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_102_sin

theorem thL_103_r_bounds : (116625463668555875713 / 200000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 ≤ (116625534731444124287 / 200000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_103
  have hl : (409484006789241959 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 103 ∧ 17670246 / 100000 * Real.log 103 ≤ (163793602786733673 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_103_eq : (17670246 / 100000 * Real.log 103) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 + π / 2) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_103_cos_r : (417372220782319 / 500000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) ≤ (208686199220577 / 250000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (72890937 / 125000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) (72890937 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 - (72890937 / 125000000 : ℝ)| ≤ (35531444124287 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 - (72890937 / 125000000 : ℝ))]

theorem thL_103_sin_r : (6882963853617 / 12500000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) ≤ (550637463603947 / 1000000000000000 : ℝ) := by
  have hr := thL_103_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (72890937 / 125000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521) (72890937 / 125000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 - (72890937 / 125000000 : ℝ)| ≤ (35531444124287 / 200000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 103) 521 - (72890937 / 125000000 : ℝ))]

theorem thL_103_cos : (-550637463603947 / 1000000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 103) ∧ Real.cos (17670246 / 100000 * Real.log 103) ≤ (-6882963853617 / 12500000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_103_sin : (417372220782319 / 500000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 103) ∧ Real.sin (17670246 / 100000 * Real.log 103) ≤ (208686199220577 / 250000000000000 : ℝ) := by
  have hc := thL_103_cos_r
  have hs := thL_103_sin_r
  rw [thL_103_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_103 : (-550637463603947 / 1000000000000000 : ℝ) ≤ cCG cZ 103 ∧ cCG cZ 103 ≤ (-6882963853617 / 12500000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_cos

theorem sCB_103 : (417372220782319 / 500000000000000 : ℝ) ≤ sCG cZ 103 ∧ sCG cZ 103 ≤ (208686199220577 / 250000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_103_sin

theorem thL_104_r_bounds : (71961441776665875933 / 100000000000000000000 : ℝ) ≤ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 ∧ PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 ≤ (71961477423334124067 / 100000000000000000000 : ℝ) := by
  have hl0 := PsiOmega.Num.log_bound_104
  have hl : (410337648502351347 / 500000000000000 : ℝ) ≤ 17670246 / 100000 * Real.log 104 ∧ 17670246 / 100000 * Real.log 104 ≤ (82067529736081703 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl0.1, hl0.2]
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  unfold PsiOmega.Num.redAngle
  push_cast
  constructor <;> linarith [hl.1, hl.2]

theorem thL_104_eq : (17670246 / 100000 * Real.log 104) = (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 + π) + ((130 : ℤ) : ℝ) * (2 * π) := by
  unfold PsiOmega.Num.redAngle
  push_cast
  ring

theorem thL_104_cos_r : (150411924903207 / 200000000000000 : ℝ) ≤ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) ∧ Real.cos (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) ≤ (376029990511489 / 500000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hc := PsiOmega.Num.cos_bounds (x := (179903649 / 250000000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num at hc
  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) (179903649 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 - (179903649 / 250000000 : ℝ)| ≤ (17823334124067 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 - (179903649 / 250000000 : ℝ))]

theorem thL_104_sin_r : (659094695836587 / 1000000000000000 : ℝ) ≤ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) ∧ Real.sin (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) ≤ (659095052305499 / 1000000000000000 : ℝ) := by
  have hr := thL_104_r_bounds
  have hs := PsiOmega.Num.sin_bounds (x := (179903649 / 250000000 : ℝ)) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522) (179903649 / 250000000 : ℝ))
  have hd : |PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 - (179903649 / 250000000 : ℝ)| ≤ (17823334124067 / 100000000000000000000 : ℝ) := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (PsiOmega.Num.redAngle (17670246 / 100000 * Real.log 104) 522 - (179903649 / 250000000 : ℝ))]

theorem thL_104_cos : (-376029990511489 / 500000000000000 : ℝ) ≤ Real.cos (17670246 / 100000 * Real.log 104) ∧ Real.cos (17670246 / 100000 * Real.log 104) ≤ (-150411924903207 / 200000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem thL_104_sin : (-659095052305499 / 1000000000000000 : ℝ) ≤ Real.sin (17670246 / 100000 * Real.log 104) ∧ Real.sin (17670246 / 100000 * Real.log 104) ≤ (-659094695836587 / 1000000000000000 : ℝ) := by
  have hc := thL_104_cos_r
  have hs := thL_104_sin_r
  rw [thL_104_eq]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

theorem cCB_104 : (-376029990511489 / 500000000000000 : ℝ) ≤ cCG cZ 104 ∧ cCG cZ 104 ≤ (-150411924903207 / 200000000000000 : ℝ) := by
  unfold cCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_cos

theorem sCB_104 : (-659095052305499 / 1000000000000000 : ℝ) ≤ sCG cZ 104 ∧ sCG cZ 104 ≤ (-659094695836587 / 1000000000000000 : ℝ) := by
  unfold sCG
  rw [cZ_im]
  simp only [Nat.cast_ofNat]
  exact thL_104_sin

end PsiOmega.Locate.Z4

#print axioms PsiOmega.Locate.Z4.cCB_104
#print axioms PsiOmega.Locate.Z4.sCB_104
