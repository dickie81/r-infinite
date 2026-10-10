import DHLocate2Base

/-! # Generated (`gen_locate_zero.py 2`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 65083 / 100000`, `n ∈ NS`

`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` with `exp(-(y/8))` from `Real.exp_bound`
(`exp_neg_ge_of`, `exp_neg_le_of`, `DHLocateExp`). -/

open Real Finset

namespace PsiOmega.Locate.Z2

theorem exB_2 : (636913783950001 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 2 ∧ ex (65083 / 100000) 2 ≤ (636913784032907 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_2
  have hlo := exp_neg_ge_of (q := (225560489793737 / 500000000000000 : ℝ)) (a := (23629258294791720553 / 25000000000000000000 : ℝ)) (lo := (636913783950001 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (451120979457307 / 1000000000000000 : ℝ)) (b := (18903406636140951409 / 20000000000000000000 : ℝ)) (hi := (636913784032907 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_3 : (489187300156227 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 3 ∧ ex (65083 / 100000) 3 ≤ (489187300241639 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_3
  have hlo := exp_neg_ge_of (q := (715009835938993 / 1000000000000000 : ℝ)) (a := (2286253616070388451 / 2500000000000000000 : ℝ)) (lo := (489187300156227 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (178752458941099 / 250000000000000 : ℝ)) (b := (45725072322405701577 / 50000000000000000000 : ℝ)) (hi := (489187300241639 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_4 : (202829584094681 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 4 ∧ ex (65083 / 100000) 4 ≤ (202829584132877 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_4
  have hlo := exp_neg_ge_of (q := (112780244895681 / 125000000000000 : ℝ)) (a := (89334695610023417641 / 100000000000000000000 : ℝ)) (lo := (202829584094681 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (56390122436071 / 62500000000000 : ℝ)) (b := (22333673903031566761 / 25000000000000000000 : ℝ)) (hi := (202829584132877 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_6 : (311570134405471 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 6 ∧ ex (65083 / 100000) 6 ≤ (311570134478663 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_6
  have hlo := exp_neg_ge_of (q := (583065407758927 / 500000000000000 : ℝ)) (a := (86435963554539126233 / 100000000000000000000 : ℝ)) (lo := (311570134405471 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (233226163056589 / 200000000000000 : ℝ)) (b := (10804495444634649937 / 12500000000000000000 : ℝ)) (hi := (311570134478663 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_7 : (140914228384289 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 7 ∧ ex (65083 / 100000) 7 ≤ (281828456834989 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_7
  have hlo := exp_neg_ge_of (q := (1266456702470493 / 1000000000000000 : ℝ)) (a := (2133969038415066879 / 2500000000000000000 : ℝ)) (lo := (140914228384289 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1266456702234853 / 1000000000000000 : ℝ)) (b := (42679380769558458797 / 50000000000000000000 : ℝ)) (hi := (281828456834989 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_8 : (25836991580301 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 8 ∧ ex (65083 / 100000) 8 ≤ (258369915872681 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_8
  have hlo := exp_neg_ge_of (q := (270672587752509 / 200000000000000 : ℝ)) (a := (42218251945066003511 / 50000000000000000000 : ℝ)) (lo := (25836991580301 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (270672587698579 / 200000000000000 : ℝ)) (b := (84436503892978045181 / 100000000000000000000 : ℝ)) (hi := (258369915872681 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_9 : (239304214636389 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 9 ∧ ex (65083 / 100000) 9 ≤ (47860842940711 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_9
  have hlo := exp_neg_ge_of (q := (1430019671868581 / 1000000000000000 : ℝ)) (a := (83631289552017153091 / 100000000000000000000 : ℝ)) (lo := (239304214636389 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (357504917896979 / 250000000000000 : ℝ)) (b := (41815644777475600279 / 50000000000000000000 : ℝ)) (hi := (47860842940711 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_11 : (210005369277953 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 11 ∧ ex (65083 / 100000) 11 ≤ (21000536933809 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_11
  have hlo := exp_neg_ge_of (q := (390155545150317 / 250000000000000 : ℝ)) (a := (41138533328707755589 / 50000000000000000000 : ℝ)) (lo := (210005369277953 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (390155545078729 / 250000000000000 : ℝ)) (b := (82277066660360537877 / 100000000000000000000 : ℝ)) (hi := (21000536933809 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_12 : (198443313273423 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 12 ∧ ex (65083 / 100000) 12 ≤ (198443313330393 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_12
  have hlo := exp_neg_ge_of (q := (1617251795088073 / 1000000000000000 : ℝ)) (a := (20424177087938136891 / 25000000000000000000 : ℝ)) (lo := (198443313273423 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (404312948700249 / 250000000000000 : ℝ)) (b := (16339341670936841083 / 20000000000000000000 : ℝ)) (hi := (198443313330393 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_13 : (7534808850867 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 13 ∧ ex (65083 / 100000) 13 ≤ (188370221325817 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_13
  have hlo := exp_neg_ge_of (q := (208668248815443 / 125000000000000 : ℝ)) (a := (40583223081476534253 / 50000000000000000000 : ℝ)) (lo := (7534808850867 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (834672995118063 / 500000000000000 : ℝ)) (b := (81166446165869158793 / 100000000000000000000 : ℝ)) (hi := (188370221325817 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_14 : (179500428828399 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 14 ∧ ex (65083 / 100000) 14 ≤ (179500428880023 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_14
  have hlo := exp_neg_ge_of (q := (1717577682040503 / 1000000000000000 : ℝ)) (a := (40339284481526403289 / 50000000000000000000 : ℝ)) (lo := (179500428828399 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (858788840876457 / 500000000000000 : ℝ)) (b := (80678568965953094539 / 100000000000000000000 : ℝ)) (hi := (179500428880023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_16 : (82279680367047 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 16 ∧ ex (65083 / 100000) 16 ≤ (164559360789229 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_16
  have hlo := exp_neg_ge_of (q := (1804483918342997 / 1000000000000000 : ℝ)) (a := (498792989982716547 / 625000000000000000 : ℝ)) (lo := (82279680367047 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (902241959003979 / 500000000000000 : ℝ)) (b := (79806878400576957457 / 100000000000000000000 : ℝ)) (hi := (164559360789229 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_17 : (1977410980219 / 12500000000000 : ℝ) ≤ ex (65083 / 100000) 17 ∧ ex (65083 / 100000) 17 ≤ (79096439237679 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_17
  have hlo := exp_neg_ge_of (q := (230492530123249 / 125000000000000 : ℝ)) (a := (39707118356284043787 / 50000000000000000000 : ℝ)) (lo := (1977410980219 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (921970120310191 / 500000000000000 : ℝ)) (b := (79414236716197427631 / 100000000000000000000 : ℝ)) (hi := (79096439237679 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_18 : (152416152855169 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 18 ∧ ex (65083 / 100000) 18 ≤ (152416152913981 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_18
  have hlo := exp_neg_ge_of (q := (1881140651482801 / 1000000000000000 : ℝ)) (a := (79045813693780896993 / 100000000000000000000 : ℝ)) (lo := (152416152855169 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (117571290693559 / 62500000000000 : ℝ)) (b := (39522906848796728743 / 50000000000000000000 : ℝ)) (hi := (152416152913981 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_19 : (147146112817569 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 19 ∧ ex (65083 / 100000) 19 ≤ (147146112876367 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_19
  have hlo := exp_neg_ge_of (q := (239541152639237 / 125000000000000 : ℝ)) (a := (78698888600584235879 / 100000000000000000000 : ℝ)) (lo := (147146112817569 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1916329220714317 / 1000000000000000 : ℝ)) (b := (3147955544180602197 / 4000000000000000000 : ℝ)) (hi := (147146112876367 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_21 : (34466725466699 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 21 ∧ ex (65083 / 100000) 21 ≤ (137866901924117 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_21
  have hlo := exp_neg_ge_of (q := (396293307692081 / 200000000000000 : ℝ)) (a := (78060710890042271833 / 100000000000000000000 : ℝ)) (lo := (34466725466699 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1981466538044647 / 1000000000000000 : ℝ)) (b := (3122428435763963663 / 4000000000000000000 : ℝ)) (hi := (137866901924117 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_22 : (133755314389759 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 22 ∧ ex (65083 / 100000) 22 ≤ (133755314446011 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_22
  have hlo := exp_neg_ge_of (q := (201174316024017 / 100000000000000 : ℝ)) (a := (38882921195467363359 / 50000000000000000000 : ℝ)) (lo := (133755314389759 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (100587157990981 / 50000000000000 : ℝ)) (b := (77765842395022808769 / 100000000000000000000 : ℝ)) (hi := (133755314446011 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_23 : (3248528498087 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 23 ∧ ex (65083 / 100000) 23 ≤ (64970569989291 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_23
  have hlo := exp_neg_ge_of (q := (2040673700877133 / 1000000000000000 : ℝ)) (a := (77485124296821813481 / 100000000000000000000 : ℝ)) (lo := (3248528498087 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1020336850226549 / 500000000000000 : ℝ)) (b := (19371281075232224599 / 25000000000000000000 : ℝ)) (hi := (64970569989291 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_24 : (31597820387369 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 24 ∧ ex (65083 / 100000) 24 ≤ (126391281603397 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_24
  have hlo := exp_neg_ge_of (q := (2068372774731521 / 1000000000000000 : ℝ)) (a := (19304326234643212491 / 25000000000000000000 : ℝ)) (lo := (31597820387369 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (517093193576229 / 250000000000000 : ℝ)) (b := (77217304942690551369 / 100000000000000000000 : ℝ)) (hi := (126391281603397 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_26 : (23995118081323 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 26 ∧ ex (65083 / 100000) 26 ≤ (119975590458203 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_26
  have hlo := exp_neg_ge_of (q := (1060233485084789 / 500000000000000 : ℝ)) (a := (19179029212406841383 / 25000000000000000000 : ℝ)) (lo := (23995118081323 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1060233484869801 / 500000000000000 : ℝ)) (b := (3835805842687534053 / 5000000000000000000 : ℝ)) (hi := (119975590458203 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_27 : (1829134104237 / 15625000000000 : ℝ) ≤ ex (65083 / 100000) 27 ∧ ex (65083 / 100000) 27 ≤ (58532291360817 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_27
  have hlo := exp_neg_ge_of (q := (429005901566321 / 200000000000000 : ℝ)) (a := (76480935261741767091 / 100000000000000000000 : ℝ)) (lo := (1829134104237 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (53625737685013 / 25000000000000 : ℝ)) (b := (15296187053172610509 / 20000000000000000000 : ℝ)) (hi := (58532291360817 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_28 : (114326297338873 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 28 ∧ ex (65083 / 100000) 28 ≤ (114326297388257 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_28
  have hlo := exp_neg_ge_of (q := (542174665422017 / 250000000000000 : ℝ)) (a := (1906374744867820297 / 2500000000000000000 : ℝ)) (lo := (114326297338873 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (33885916582127 / 15625000000000 : ℝ)) (b := (9531873724853760083 / 12500000000000000000 : ℝ)) (hi := (114326297388257 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_29 : (5587242422897 / 50000000000000 : ℝ) ≤ ex (65083 / 100000) 29 ∧ ex (65083 / 100000) 29 ≤ (27936212126571 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_29
  have hlo := exp_neg_ge_of (q := (2140172993517 / 976562500000 : ℝ)) (a := (76037606693696658171 / 100000000000000000000 : ℝ)) (lo := (5587242422897 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1095768572464401 / 500000000000000 : ℝ)) (b := (19009401674452132393 / 25000000000000000000 : ℝ)) (hi := (27936212126571 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_31 : (53499173532661 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 31 ∧ ex (65083 / 100000) 31 ≤ (106998347111713 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_31
  have hlo := exp_neg_ge_of (q := (1117470946313591 / 500000000000000 : ℝ)) (a := (15125234939337296337 / 20000000000000000000 : ℝ)) (lo := (53499173532661 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2234941892193639 / 1000000000000000 : ℝ)) (b := (37813087350392491873 / 50000000000000000000 : ℝ)) (hi := (106998347111713 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_32 : (20962025025467 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 32 ∧ ex (65083 / 100000) 32 ≤ (26202531293203 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_32
  have hlo := exp_neg_ge_of (q := (281950612243943 / 125000000000000 : ℝ)) (a := (75431093733772842187 / 100000000000000000000 : ℝ)) (lo := (20962025025467 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (225560489751767 / 100000000000000 : ℝ)) (b := (18857773434465976287 / 25000000000000000000 : ℝ)) (hi := (26202531293203 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_33 : (51365979806587 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 33 ∧ ex (65083 / 100000) 33 ≤ (6420747478611 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_33
  have hlo := exp_neg_ge_of (q := (455126403312371 / 200000000000000 : ℝ)) (a := (75242496465869022457 / 100000000000000000000 : ℝ)) (lo := (51365979806587 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (568908004031929 / 250000000000000 : ℝ)) (b := (7524249646995236217 / 10000000000000000000 : ℝ)) (hi := (6420747478611 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_34 : (100755224787319 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 34 ∧ ex (65083 / 100000) 34 ≤ (20151044966217 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_34
  have hlo := exp_neg_ge_of (q := (1147530610284373 / 500000000000000 : ℝ)) (a := (75059980462644267219 / 100000000000000000000 : ℝ)) (lo := (100755224787319 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (286882652516799 / 125000000000000 : ℝ)) (b := (75059980466719733139 / 100000000000000000000 : ℝ)) (hi := (20151044966217 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_36 : (48537974326101 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 36 ∧ ex (65083 / 100000) 36 ≤ (97075948694401 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_36
  have hlo := exp_neg_ge_of (q := (291532703881059 / 125000000000000 : ℝ)) (a := (74711757955896796271 / 100000000000000000000 : ℝ)) (lo := (48537974326101 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (11661308153069 / 5000000000000 : ℝ)) (b := (3735587897997817771 / 5000000000000000000 : ℝ)) (hi := (97075948694401 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_37 : (95360226026893 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 37 ∧ ex (65083 / 100000) 37 ≤ (47680113034179 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_37
  have hlo := exp_neg_ge_of (q := (73440428294357 / 31250000000000 : ℝ)) (a := (74545410217067801673 / 100000000000000000000 : ℝ)) (lo := (95360226026893 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1175046852492317 / 500000000000000 : ℝ)) (b := (37272705110559719173 / 50000000000000000000 : ℝ)) (hi := (47680113034179 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_38 : (46859693755649 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 38 ∧ ex (65083 / 100000) 38 ≤ (46859693776029 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_38
  have hlo := exp_neg_ge_of (q := (2367450200667991 / 1000000000000000 : ℝ)) (a := (74383854650559963233 / 100000000000000000000 : ℝ)) (lo := (46859693755649 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2367450200233103 / 1000000000000000 : ℝ)) (b := (74383854654603748011 / 100000000000000000000 : ℝ)) (hi := (46859693776029 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_39 : (92148319971751 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 39 ∧ ex (65083 / 100000) 39 ≤ (23037080002959 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_39
  have hlo := exp_neg_ge_of (q := (1192177913241947 / 500000000000000 : ℝ)) (a := (37113416208627608451 / 50000000000000000000 : ℝ)) (lo := (92148319971751 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1192177913024463 / 500000000000000 : ℝ)) (b := (74226832421291226251 / 100000000000000000000 : ℝ)) (hi := (23037080002959 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_41 : (1393708370549 / 15625000000000 : ℝ) ≤ ex (65083 / 100000) 41 ∧ ex (65083 / 100000) 41 ≤ (89197335753949 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_41
  have hlo := exp_neg_ge_of (q := (151056506781663 / 62500000000000 : ℝ)) (a := (73925451438157288203 / 100000000000000000000 : ℝ)) (lo := (1393708370549 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (483380821614303 / 200000000000000 : ℝ)) (b := (73925451442178105519 / 100000000000000000000 : ℝ)) (hi := (89197335753949 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_42 : (21952332538393 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 42 ∧ ex (65083 / 100000) 42 ≤ (17561866038357 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_42
  have hlo := exp_neg_ge_of (q := (2432587518000849 / 1000000000000000 : ℝ)) (a := (36890334006134140387 / 50000000000000000000 : ℝ)) (lo := (21952332538393 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (608146879391427 / 250000000000000 : ℝ)) (b := (73780668016281687599 / 100000000000000000000 : ℝ)) (hi := (17561866038357 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_43 : (86474831592567 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 43 ∧ ex (65083 / 100000) 43 ≤ (86474831630203 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_43
  have hlo := exp_neg_ge_of (q := (61197546790759 / 25000000000000 : ℝ)) (a := (36819782603189664259 / 50000000000000000000 : ℝ)) (lo := (86474831592567 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2447901871195179 / 1000000000000000 : ℝ)) (b := (36819782605192725347 / 50000000000000000000 : ℝ)) (hi := (86474831630203 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_44 : (10648825426969 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 44 ∧ ex (65083 / 100000) 44 ≤ (2662206357901 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_44
  have hlo := exp_neg_ge_of (q := (2462864139776571 / 1000000000000000 : ℝ)) (a := (36750983527583679983 / 50000000000000000000 : ℝ)) (lo := (10648825426969 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1231432069670677 / 500000000000000 : ℝ)) (b := (14700393411833270201 / 20000000000000000000 : ℝ)) (hi := (2662206357901 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_46 : (20690325780977 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 46 ∧ ex (65083 / 100000) 46 ≤ (646572680937 / 7812500000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_46
  have hlo := exp_neg_ge_of (q := (2491794680410593 / 1000000000000000 : ℝ)) (a := (73236640641039920607 / 100000000000000000000 : ℝ)) (lo := (20690325780977 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1245897339987661 / 500000000000000 : ℝ)) (b := (73236640645025020991 / 100000000000000000000 : ℝ)) (hi := (646572680937 / 7812500000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_47 : (81610972107089 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 47 ∧ ex (65083 / 100000) 47 ≤ (40805486071309 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_47
  have hlo := exp_neg_ge_of (q := (626447890988643 / 250000000000000 : ℝ)) (a := (73108617078103751003 / 100000000000000000000 : ℝ)) (lo := (81610972107089 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2505791563519279 / 1000000000000000 : ℝ)) (b := (73108617082082113041 / 100000000000000000000 : ℝ)) (hi := (40805486071309 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_48 : (40250174697243 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 48 ∧ ex (65083 / 100000) 48 ≤ (40250174714767 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_48
  have hlo := exp_neg_ge_of (q := (2519493754262813 / 1000000000000000 : ℝ)) (a := (36491752864680769989 / 50000000000000000000 : ℝ)) (lo := (40250174697243 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2519493753827501 / 1000000000000000 : ℝ)) (b := (912293821666666189 / 1250000000000000000 : ℝ)) (hi := (40250174714767 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_49 : (79427279043601 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 49 ∧ ex (65083 / 100000) 49 ≤ (79427279078183 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_49
  have hlo := exp_neg_ge_of (q := (2532913404952983 / 1000000000000000 : ℝ)) (a := (18215295427629075581 / 25000000000000000000 : ℝ)) (lo := (79427279043601 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (316614175564707 / 125000000000000 : ℝ)) (b := (72861181714481566289 / 100000000000000000000 : ℝ)) (hi := (79427279078183 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_51 : (38692973550257 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 51 ∧ ex (65083 / 100000) 51 ≤ (77385947134209 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_51
  have hlo := exp_neg_ge_of (q := (2558950076879639 / 1000000000000000 : ℝ)) (a := (283689196644697673 / 390625000000000000 : ℝ)) (lo := (38692973550257 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1279475038222143 / 500000000000000 : ℝ)) (b := (72624434344995281399 / 100000000000000000000 : ℝ)) (hi := (77385947134209 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_52 : (76414107272019 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 52 ∧ ex (65083 / 100000) 52 ≤ (19103526826323 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_52
  have hlo := exp_neg_ge_of (q := (1285793974849013 / 500000000000000 : ℝ)) (a := (36254898808532626659 / 50000000000000000000 : ℝ)) (lo := (76414107272019 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1285793974631331 / 500000000000000 : ℝ)) (b := (9063724702626477913 / 12500000000000000000 : ℝ)) (hi := (19103526826323 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_53 : (75472638949363 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 53 ∧ ex (65083 / 100000) 53 ≤ (75472638982227 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_53
  have hlo := exp_neg_ge_of (q := (2583985086430811 / 1000000000000000 : ℝ)) (a := (36198760199921938141 / 50000000000000000000 : ℝ)) (lo := (75472638949363 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2583985085995437 / 1000000000000000 : ℝ)) (b := (7239752040378445929 / 10000000000000000000 : ℝ)) (hi := (75472638982227 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_54 : (74560046320087 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 54 ∧ ex (65083 / 100000) 54 ≤ (14912009270511 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_54
  have hlo := exp_neg_ge_of (q := (2596150487359117 / 1000000000000000 : ℝ)) (a := (1807187773940472309 / 2500000000000000000 : ℝ)) (lo := (74560046320087 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (519230097384747 / 200000000000000 : ℝ)) (b := (72287510961553594567 / 100000000000000000000 : ℝ)) (hi := (14912009270511 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_56 : (18203998661877 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 56 ∧ ex (65083 / 100000) 56 ≤ (36407997339609 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_56
  have hlo := exp_neg_ge_of (q := (2619819641214859 / 1000000000000000 : ℝ)) (a := (72073954005585146701 / 100000000000000000000 : ℝ)) (lo := (18203998661877 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (327477455097433 / 125000000000000 : ℝ)) (b := (4504622125594275917 / 6250000000000000000 : ℝ)) (hi := (36407997339609 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_57 : (35991004831531 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 57 ∧ ex (65083 / 100000) 57 ≤ (71982009694409 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_57
  have hlo := exp_neg_ge_of (q := (2631339056978467 / 1000000000000000 : ℝ)) (a := (35985123729095699469 / 50000000000000000000 : ℝ)) (lo := (35991004831531 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1315669528271533 / 500000000000000 : ℝ)) (b := (71970247462109113919 / 100000000000000000000 : ℝ)) (hi := (71982009694409 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_58 : (14234366853787 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 58 ∧ ex (65083 / 100000) 58 ≤ (71171834304537 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_58
  have hlo := exp_neg_ge_of (q := (2642658124939409 / 1000000000000000 : ℝ)) (a := (8983561243426267129 / 12500000000000000000 : ℝ)) (lo := (14234366853787 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (330332265554911 / 125000000000000 : ℝ)) (b := (17967122487975942067 / 25000000000000000000 : ℝ)) (hi := (71171834304537 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_59 : (1759609887793 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 59 ∧ ex (65083 / 100000) 59 ≤ (70384395551107 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_59
  have hlo := exp_neg_ge_of (q := (1326891847525071 / 500000000000000 : ℝ)) (a := (35884306086436754121 / 50000000000000000000 : ℝ)) (lo := (1759609887793 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2653783694490647 / 1000000000000000 : ℝ)) (b := (71768612177893583787 / 100000000000000000000 : ℝ)) (hi := (70384395551107 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_61 : (6887375846853 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 61 ∧ ex (65083 / 100000) 61 ≤ (34436879257143 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_61
  have hlo := exp_neg_ge_of (q := (267548003753669 / 100000000000000 : ℝ)) (a := (4473389770071390383 / 6250000000000000000 : ℝ)) (lo := (6887375846853 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2675480036872457 / 1000000000000000 : ℝ)) (b := (35787118163542938929 / 50000000000000000000 : ℝ)) (hi := (34436879257143 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_62 : (17037180523749 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 62 ∧ ex (65083 / 100000) 62 ≤ (34074361071711 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_62
  have hlo := exp_neg_ge_of (q := (2686062872372661 / 1000000000000000 : ℝ)) (a := (1429592332575786281 / 2000000000000000000 : ℝ)) (lo := (17037180523749 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (268606287166219 / 100000000000000 : ℝ)) (b := (71479616635138266863 / 100000000000000000000 : ℝ)) (hi := (34074361071711 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_63 : (33721368746963 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 63 ∧ ex (65083 / 100000) 63 ≤ (8430342193091 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_63
  have hlo := exp_neg_ge_of (q := (269647637456529 / 100000000000000 : ℝ)) (a := (2855465320666900249 / 4000000000000000000 : ℝ)) (lo := (33721368746963 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2696476373812163 / 1000000000000000 : ℝ)) (b := (71386633023393878923 / 100000000000000000000 : ℝ)) (hi := (8430342193091 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_64 : (66755013376207 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 64 ∧ ex (65083 / 100000) 64 ≤ (104304708483 / 1562500000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_64
  have hlo := exp_neg_ge_of (q := (541345175552477 / 200000000000000 : ℝ)) (a := (71295231889767058879 / 100000000000000000000 : ℝ)) (lo := (66755013376207 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2706725876969857 / 1000000000000000 : ℝ)) (b := (35647615948415505113 / 50000000000000000000 : ℝ)) (hi := (104304708483 / 1562500000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_66 : (8178925138943 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 66 ∧ ex (65083 / 100000) 66 ≤ (65431401168001 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_66
  have hlo := exp_neg_ge_of (q := (1363376498214307 / 500000000000000 : ℝ)) (a := (35558487673497606343 / 50000000000000000000 : ℝ)) (lo := (8178925138943 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (545350599113181 / 200000000000000 : ℝ)) (b := (2844679014186619263 / 4000000000000000000 : ℝ)) (hi := (65431401168001 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_67 : (8099267610417 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 67 ∧ ex (65083 / 100000) 67 ≤ (64794140941271 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_67
  have hlo := exp_neg_ge_of (q := (1368270049089401 / 500000000000000 : ℝ)) (a := (71030024910652045363 / 100000000000000000000 : ℝ)) (lo := (8099267610417 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2736540097284813 / 1000000000000000 : ℝ)) (b := (2219688278705959809 / 3125000000000000000 : ℝ)) (hi := (64794140941271 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_68 : (6417239145101 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 68 ∧ ex (65083 / 100000) 68 ≤ (16043097877563 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_68
  have hlo := exp_neg_ge_of (q := (2746182200483569 / 1000000000000000 : ℝ)) (a := (14188893327049937587 / 20000000000000000000 : ℝ)) (lo := (6417239145101 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (54923643991211 / 20000000000000 : ℝ)) (b := (70944466643436285221 / 100000000000000000000 : ℝ)) (hi := (16043097877563 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_69 : (15891388849569 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 69 ∧ ex (65083 / 100000) 69 ≤ (63565555458673 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_69
  have hlo := exp_neg_ge_of (q := (21528777633847 / 7812500000000 : ℝ)) (a := (70860258243306236937 / 100000000000000000000 : ℝ)) (lo := (15891388849569 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (344460442022803 / 125000000000000 : ℝ)) (b := (35430129125861041971 / 50000000000000000000 : ℝ)) (hi := (63565555458673 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_71 : (62394387899519 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 71 ∧ ex (65083 / 100000) 71 ≤ (31197193980913 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_71
  have hlo := exp_neg_ge_of (q := (346784993144867 / 125000000000000 : ℝ)) (a := (35347865629340361733 / 50000000000000000000 : ℝ)) (lo := (62394387899519 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (5548559888321 / 2000000000000 : ℝ)) (b := (70695731267505237151 / 100000000000000000000 : ℝ)) (hi := (31197193980913 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_72 : (15457252440393 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 72 ∧ ex (65083 / 100000) 72 ≤ (61829009824661 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_72
  have hlo := exp_neg_ge_of (q := (2783382611040771 / 1000000000000000 : ℝ)) (a := (70615337052339273077 / 100000000000000000000 : ℝ)) (lo := (15457252440393 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2783382610020567 / 1000000000000000 : ℝ)) (b := (8826917132668244049 / 12500000000000000000 : ℝ)) (hi := (61829009824661 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_73 : (61276447986253 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 73 ∧ ex (65083 / 100000) 73 ≤ (61276448050023 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_73
  have hlo := exp_neg_ge_of (q := (1396179859450203 / 500000000000000 : ℝ)) (a := (70536141307787844849 / 100000000000000000000 : ℝ)) (lo := (61276447986253 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2792359717859893 / 1000000000000000 : ℝ)) (b := (70536141316963545567 / 100000000000000000000 : ℝ)) (hi := (61276448050023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_74 : (60736242370617 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 74 ∧ ex (65083 / 100000) 74 ≤ (60736242434977 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_74
  have hlo := exp_neg_ge_of (q := (17507591784019 / 6250000000000 : ℝ)) (a := (70458110104569524629 / 100000000000000000000 : ℝ)) (lo := (60736242370617 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2801214684383563 / 1000000000000000 : ℝ)) (b := (70458110113902154519 / 100000000000000000000 : ℝ)) (hi := (60736242434977 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_76 : (59691169701621 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 76 ∧ ex (65083 / 100000) 76 ≤ (29845584883461 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_76
  have hlo := exp_neg_ge_of (q := (2818571180718969 / 1000000000000000 : ℝ)) (a := (70305412575938285967 / 100000000000000000000 : ℝ)) (lo := (59691169701621 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (88080349363287 / 31250000000000 : ℝ)) (b := (17576353146388079099 / 25000000000000000000 : ℝ)) (hi := (29845584883461 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_77 : (11837097821351 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 77 ∧ ex (65083 / 100000) 77 ≤ (59185489172423 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_77
  have hlo := exp_neg_ge_of (q := (282707888357787 / 100000000000000 : ℝ)) (a := (14046137024594052099 / 20000000000000000000 : ℝ)) (lo := (11837097821351 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (35338486030857 / 12500000000000 : ℝ)) (b := (35115342566355213159 / 50000000000000000000 : ℝ)) (hi := (59185489172423 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_78 : (29345267564611 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 78 ∧ ex (65083 / 100000) 78 ≤ (11738107039039 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_78
  have hlo := exp_neg_ge_of (q := (177217300409929 / 62500000000000 : ℝ)) (a := (70156999819385067537 / 100000000000000000000 : ℝ)) (lo := (29345267564611 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (708869201358751 / 250000000000000 : ℝ)) (b := (70156999829242676089 / 100000000000000000000 : ℝ)) (hi := (11738107039039 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_79 : (58205947035953 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 79 ∧ ex (65083 / 100000) 79 ≤ (1818935846943 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_79
  have hlo := exp_neg_ge_of (q := (568753549343301 / 200000000000000 : ℝ)) (a := (35042164523405391819 / 50000000000000000000 : ℝ)) (lo := (58205947035953 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2843767745578999 / 1000000000000000 : ℝ)) (b := (17521082264194448239 / 25000000000000000000 : ℝ)) (hi := (1818935846943 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_81 : (14316626778329 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 81 ∧ ex (65083 / 100000) 81 ≤ (28633253589947 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_81
  have hlo := exp_neg_ge_of (q := (2860039344250731 / 1000000000000000 : ℝ)) (a := (34970962958420731501 / 50000000000000000000 : ℝ)) (lo := (14316626778329 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1430019671544191 / 500000000000000 : ℝ)) (b := (69941925927005550653 / 100000000000000000000 : ℝ)) (hi := (28633253589947 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_82 : (28405506289311 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 82 ∧ ex (65083 / 100000) 82 ≤ (28405506322657 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_82
  have hlo := exp_neg_ge_of (q := (11203223002427 / 3906250000000 : ℝ)) (a := (34936071729522744457 / 50000000000000000000 : ℝ)) (lo := (28405506289311 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (57360501748953 / 20000000000000 : ℝ)) (b := (17468035867324578163 / 25000000000000000000 : ℝ)) (hi := (28405506322657 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_83 : (28182298405107 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 83 ∧ ex (65083 / 100000) 83 ≤ (28182298438491 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_83
  have hlo := exp_neg_ge_of (q := (2875914033705093 / 1000000000000000 : ℝ)) (a := (34901637616450140217 / 50000000000000000000 : ℝ)) (lo := (28182298405107 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2875914032520787 / 1000000000000000 : ℝ)) (b := (279213100972943769 / 400000000000000000 : ℝ)) (hi := (28182298438491 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_84 : (27963486351903 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 84 ∧ ex (65083 / 100000) 84 ≤ (6990871596327 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_84
  have hlo := exp_neg_ge_of (q := (720927124533011 / 250000000000000 : ℝ)) (a := (8716912307528149687 / 12500000000000000000 : ℝ)) (lo := (27963486351903 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2883708496937717 / 1000000000000000 : ℝ)) (b := (69735298470638217889 / 100000000000000000000 : ℝ)) (hi := (6990871596327 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_86 : (11015402435059 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 86 ∧ ex (65083 / 100000) 86 ≤ (55077012242101 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_86
  have hlo := exp_neg_ge_of (q := (2899022851776197 / 1000000000000000 : ℝ)) (a := (34800966137123980401 / 50000000000000000000 : ℝ)) (lo := (11015402435059 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (115960914022541 / 40000000000000 : ℝ)) (b := (69601932284800819609 / 100000000000000000000 : ℝ)) (hi := (55077012242101 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_87 : (218656642779 / 4000000000000 : ℝ) ≤ ex (65083 / 100000) 87 ∧ ex (65083 / 100000) 87 ≤ (10932832152303 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_87
  have hlo := exp_neg_ge_of (q := (2906546981826209 / 1000000000000000 : ℝ)) (a := (34768250649874113491 / 50000000000000000000 : ℝ)) (lo := (218656642779 / 4000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2906546980605137 / 1000000000000000 : ℝ)) (b := (69536501310364254107 / 100000000000000000000 : ℝ)) (hi := (10932832152303 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_88 : (27129534773747 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 88 ∧ ex (65083 / 100000) 88 ≤ (10851813922839 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_88
  have hlo := exp_neg_ge_of (q := (2913985119935443 / 1000000000000000 : ℝ)) (a := (69471878583908786319 / 100000000000000000000 : ℝ)) (lo := (27129534773747 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2913985118706439 / 1000000000000000 : ℝ)) (b := (4341992412161494107 / 6250000000000000000 : ℝ)) (hi := (10851813922839 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_89 : (53861507137587 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 89 ∧ ex (65083 / 100000) 89 ≤ (53861507204203 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_89
  have hlo := exp_neg_ge_of (q := (1460669604743677 / 500000000000000 : ℝ)) (a := (17352011281539617569 / 25000000000000000000 : ℝ)) (lo := (53861507137587 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1460669604125429 / 500000000000000 : ℝ)) (b := (69408045136888859623 / 100000000000000000000 : ℝ)) (hi := (53861507204203 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_91 : (53088088729331 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 91 ∧ ex (65083 / 100000) 91 ≤ (53088088795723 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_91
  have hlo := exp_neg_ge_of (q := (117432107744479 / 40000000000000 : ℝ)) (a := (8660334152826999307 / 12500000000000000000 : ℝ)) (lo := (53088088729331 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1467901346180847 / 500000000000000 : ℝ)) (b := (69282673233446544049 / 100000000000000000000 : ℝ)) (hi := (53088088795723 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_92 : (10542362941197 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 92 ∧ ex (65083 / 100000) 92 ≤ (26355907386121 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_92
  have hlo := exp_neg_ge_of (q := (1471457830295757 / 500000000000000 : ℝ)) (a := (4326318745553858779 / 6250000000000000000 : ℝ)) (lo := (10542362941197 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2942915659334891 / 1000000000000000 : ℝ)) (b := (86526374924672027 / 125000000000000000 : ℝ)) (hi := (26355907386121 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_93 : (13085558123207 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 93 ∧ ex (65083 / 100000) 93 ≤ (10468446511787 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_93
  have hlo := exp_neg_ge_of (q := (1474975864562213 / 500000000000000 : ℝ)) (a := (69160246143119432219 / 100000000000000000000 : ℝ)) (lo := (13085558123207 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (737487931965449 / 250000000000000 : ℝ)) (b := (8645030769254720753 / 12500000000000000000 : ℝ)) (hi := (10468446511787 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_94 : (51979153025217 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 94 ∧ ex (65083 / 100000) 94 ≤ (25989576545581 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_94
  have hlo := exp_neg_ge_of (q := (2956912544144833 / 1000000000000000 : ℝ)) (a := (69100095855332380561 / 100000000000000000000 : ℝ)) (lo := (51979153025217 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2956912542876511 / 1000000000000000 : ℝ)) (b := (34550047933145233821 / 50000000000000000000 : ℝ)) (hi := (25989576545581 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_96 : (51271782110787 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 96 ∧ ex (65083 / 100000) 96 ≤ (410174257411 / 8000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_96
  have hlo := exp_neg_ge_of (q := (2970614734461473 / 1000000000000000 : ℝ)) (a := (68981844320267155037 / 100000000000000000000 : ℝ)) (lo := (51271782110787 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2970614733182633 / 1000000000000000 : ℝ)) (b := (68981844331297356123 / 100000000000000000000 : ℝ)) (hi := (410174257411 / 8000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_97 : (50927147538129 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 97 ∧ ex (65083 / 100000) 97 ≤ (12731786900881 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_97
  have hlo := exp_neg_ge_of (q := (2977359147151707 / 1000000000000000 : ℝ)) (a := (68923713574040278527 / 100000000000000000000 : ℝ)) (lo := (50927147538129 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (595471829173601 / 200000000000000 : ℝ)) (b := (3446185679255158063 / 5000000000000000000 : ℝ)) (hi := (12731786900881 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_98 : (10117665762639 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 98 ∧ ex (65083 / 100000) 98 ≤ (50588328878389 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_98
  have hlo := exp_neg_ge_of (q := (746008596289803 / 250000000000000 : ℝ)) (a := (34433113643366325017 / 50000000000000000000 : ℝ)) (lo := (10117665762639 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1492017191935447 / 500000000000000 : ℝ)) (b := (34433113648913065587 / 50000000000000000000 : ℝ)) (hi := (50588328878389 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_99 : (5025516993367 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 99 ∧ ex (65083 / 100000) 99 ≤ (785237031229 / 15625000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_99
  have hlo := exp_neg_ge_of (q := (373830231635331 / 125000000000000 : ℝ)) (a := (13761874369179068613 / 20000000000000000000 : ℝ)) (lo := (5025516993367 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2990641851789943 / 1000000000000000 : ℝ)) (b := (17202342964254372453 / 25000000000000000000 : ℝ)) (hi := (785237031229 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_101 : (9921047193099 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 101 ∧ ex (65083 / 100000) 101 ≤ (9921047206009 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_101
  have hlo := exp_neg_ge_of (q := (3003658887001861 / 1000000000000000 : ℝ)) (a := (34348750571856343229 / 50000000000000000000 : ℝ)) (lo := (9921047193099 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3003658885701017 / 1000000000000000 : ℝ)) (b := (68697501154886827609 / 100000000000000000000 : ℝ)) (hi := (9921047206009 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_102 : (24644088180593 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 102 ∧ ex (65083 / 100000) 102 ≤ (49288176425511 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_102
  have hlo := exp_neg_ge_of (q := (3010071057098887 / 1000000000000000 : ℝ)) (a := (34321230348440851151 / 50000000000000000000 : ℝ)) (lo := (24644088180593 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3010071055794267 / 1000000000000000 : ℝ)) (b := (34321230354039692411 / 50000000000000000000 : ℝ)) (hi := (49288176425511 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_103 : (48976207087481 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 103 ∧ ex (65083 / 100000) 103 ≤ (24488103575787 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_103
  have hlo := exp_neg_ge_of (q := (603284133688291 / 200000000000000 : ℝ)) (a := (1714700017346339007 / 2500000000000000000 : ℝ)) (lo := (48976207087481 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (75410516678331 / 25000000000000 : ℝ)) (b := (68588000705073276591 / 100000000000000000000 : ℝ)) (hi := (24488103575787 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_104 : (6083649772343 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 104 ∧ ex (65083 / 100000) 104 ≤ (48669198242603 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_104
  have hlo := exp_neg_ge_of (q := (3022708929922881 / 1000000000000000 : ℝ)) (a := (68534109466404892831 / 100000000000000000000 : ℝ)) (lo := (6083649772343 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (75567723215281 / 25000000000000 : ℝ)) (b := (34267054738822620361 / 50000000000000000000 : ℝ)) (hi := (48669198242603 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_106 : (48069564027029 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 106 ∧ ex (65083 / 100000) 106 ≤ (48069564090409 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_106
  have hlo := exp_neg_ge_of (q := (3035106066660759 / 1000000000000000 : ℝ)) (a := (68427988371715857319 / 100000000000000000000 : ℝ)) (lo := (48069564027029 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1517553032671371 / 500000000000000 : ℝ)) (b := (68427988382993535997 / 100000000000000000000 : ℝ)) (hi := (48069564090409 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_107 : (11944175174973 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 107 ∧ ex (65083 / 100000) 107 ≤ (11944175190757 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_107
  have hlo := exp_neg_ge_of (q := (152060859568751 / 50000000000000 : ℝ)) (a := (17093934208781115497 / 25000000000000000000 : ℝ)) (lo := (11944175174973 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1520608595027017 / 500000000000000 : ℝ)) (b := (34187868423209503163 / 50000000000000000000 : ℝ)) (hi := (11944175190757 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_108 : (9497664240493 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 108 ∧ ex (65083 / 100000) 108 ≤ (9497664253071 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_108
  have hlo := exp_neg_ge_of (q := (30472714675937 / 10000000000000 : ℝ)) (a := (34162005355338230483 / 50000000000000000000 : ℝ)) (lo := (9497664240493 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3047271466269881 / 1000000000000000 : ℝ)) (b := (68324010721986758877 / 100000000000000000000 : ℝ)) (hi := (9497664253071 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_109 : (5900539539267 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 109 ∧ ex (65083 / 100000) 109 ≤ (23602158188389 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_109
  have hlo := exp_neg_ge_of (q := (1526634971618901 / 500000000000000 : ℝ)) (a := (34136399961486325603 / 50000000000000000000 : ℝ)) (lo := (5900539539267 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1526634970955639 / 500000000000000 : ℝ)) (b := (68272799934297660399 / 100000000000000000000 : ℝ)) (hi := (23602158188389 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_111 : (9329802296759 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 111 ∧ ex (65083 / 100000) 111 ≤ (23324505772969 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_111
  have hlo := exp_neg_ge_of (q := (1532551770985379 / 500000000000000 : ℝ)) (a := (68171885462866512409 / 100000000000000000000 : ℝ)) (lo := (9329802296759 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (153255177031959 / 50000000000000 : ℝ)) (b := (681718854742180613 / 1000000000000000000 : ℝ)) (hi := (23324505772969 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_112 : (2318875532631 / 50000000000000 : ℝ) ≤ ex (65083 / 100000) 112 ∧ ex (65083 / 100000) 112 ≤ (46377510714511 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_112
  have hlo := exp_neg_ge_of (q := (1535470310728763 / 500000000000000 : ℝ)) (a := (68122163015413472597 / 100000000000000000000 : ℝ)) (lo := (2318875532631 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (767735155030897 / 250000000000000 : ℝ)) (b := (34061081513388472941 / 50000000000000000000 : ℝ)) (hi := (46377510714511 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_113 : (23054991185063 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 113 ∧ ex (65083 / 100000) 113 ≤ (11527495607941 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_113
  have hlo := exp_neg_ge_of (q := (1538362907553449 / 500000000000000 : ℝ)) (a := (8509114791884731817 / 12500000000000000000 : ℝ)) (lo := (23054991185063 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1538362906885351 / 500000000000000 : ℝ)) (b := (17018229586613109001 / 25000000000000000000 : ℝ)) (hi := (11527495607941 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_114 : (9169266824121 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 114 ∧ ex (65083 / 100000) 114 ≤ (45846334181991 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_114
  have hlo := exp_neg_ge_of (q := (1541230018612331 / 500000000000000 : ℝ)) (a := (68024142663582216553 / 100000000000000000000 : ℝ)) (lo := (9169266824121 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3082460035886307 / 1000000000000000 : ℝ)) (b := (2720965706998684653 / 4000000000000000000 : ℝ)) (hi := (45846334181991 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_116 : (5666290280901 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 116 ∧ ex (65083 / 100000) 116 ≤ (45330322308087 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_116
  have hlo := exp_neg_ge_of (q := (618755821027413 / 200000000000000 : ℝ)) (a := (84909955604718361 / 125000000000000000 : ℝ)) (lo := (5666290280901 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (386722387974333 / 125000000000000 : ℝ)) (b := (67927964495178070857 / 100000000000000000000 : ℝ)) (hi := (45330322308087 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_117 : (45077787832833 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 117 ∧ ex (65083 / 100000) 117 ≤ (2253889394673 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_117
  have hlo := exp_neg_ge_of (q := (12397462652181 / 4000000000000 : ℝ)) (a := (13576109120814937189 / 20000000000000000000 : ℝ)) (lo := (45077787832833 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3099365661700953 / 1000000000000000 : ℝ)) (b := (67880545615486309561 / 100000000000000000000 : ℝ)) (hi := (2253889394673 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_118 : (44828791651023 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 118 ∧ ex (65083 / 100000) 118 ≤ (11207197927849 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_118
  have hlo := exp_neg_ge_of (q := (776226168800817 / 250000000000000 : ℝ)) (a := (67833562974861893143 / 100000000000000000000 : ℝ)) (lo := (44828791651023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (620980934771431 / 200000000000000 : ℝ)) (b := (16958390746570283041 / 25000000000000000000 : ℝ)) (hi := (11207197927849 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_119 : (44583254768121 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 119 ∧ ex (65083 / 100000) 119 ≤ (22291627414121 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_119
  have hlo := exp_neg_ge_of (q := (388799618010681 / 125000000000000 : ℝ)) (a := (67787008936259620701 / 100000000000000000000 : ℝ)) (lo := (44583254768121 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (622079388547519 / 200000000000000 : ℝ)) (b := (847337611846073541 / 1250000000000000000 : ℝ)) (hi := (22291627414121 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_121 : (44102255096677 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 121 ∧ ex (65083 / 100000) 121 ≤ (8820451031259 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_121
  have hlo := exp_neg_ge_of (q := (624248872371403 / 200000000000000 : ℝ)) (a := (8461894621493060883 / 12500000000000000000 : ℝ)) (lo := (44102255096677 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3121244360505891 / 1000000000000000 : ℝ)) (b := (8461894622922897923 / 12500000000000000000 : ℝ)) (hi := (8820451031259 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_122 : (171354086327 / 3906250000000 : ℝ) ≤ ex (65083 / 100000) 122 ∧ ex (65083 / 100000) 122 ≤ (10966661539753 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_122
  have hlo := exp_neg_ge_of (q := (3126601017610033 / 1000000000000000 : ℝ)) (a := (33824922343638029637 / 50000000000000000000 : ℝ)) (lo := (171354086327 / 3906250000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (312660101625891 / 100000000000000 : ℝ)) (b := (67649844698707211317 / 100000000000000000000 : ℝ)) (hi := (10966661539753 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_123 : (21817101906099 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 123 ∧ ex (65083 / 100000) 123 ≤ (8726840774237 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_123
  have hlo := exp_neg_ge_of (q := (3131913945073319 / 1000000000000000 : ℝ)) (a := (2112654133210602027 / 3125000000000000000 : ℝ)) (lo := (21817101906099 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (626382788744439 / 200000000000000 : ℝ)) (b := (67604932274162958317 / 100000000000000000000 : ℝ)) (hi := (8726840774237 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_124 : (10851215110343 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 124 ∧ ex (65083 / 100000) 124 ≤ (43404860500049 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_124
  have hlo := exp_neg_ge_of (q := (1568591926204507 / 500000000000000 : ℝ)) (a := (67560412961578440239 / 100000000000000000000 : ℝ)) (lo := (10851215110343 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (313718385105789 / 100000000000000 : ℝ)) (b := (16890103243248683571 / 25000000000000000000 : ℝ)) (hi := (43404860500049 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_126 : (21477604559681 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 126 ∧ ex (65083 / 100000) 126 ≤ (5369401147179 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_126
  have hlo := exp_neg_ge_of (q := (1573798677283759 / 500000000000000 : ℝ)) (a := (2698901104414214507 / 4000000000000000000 : ℝ)) (lo := (21477604559681 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (629519470643279 / 200000000000000 : ℝ)) (b := (67472527621757047967 / 100000000000000000000 : ℝ)) (hi := (5369401147179 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_127 : (42734775206683 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 127 ∧ ex (65083 / 100000) 127 ≤ (42734775264457 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_127
  have hlo := exp_neg_ge_of (q := (3152742282546133 / 1000000000000000 : ℝ)) (a := (67429148898735749419 / 100000000000000000000 : ℝ)) (lo := (42734775206683 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3152742281195009 / 1000000000000000 : ℝ)) (b := (33714574455065120047 / 50000000000000000000 : ℝ)) (hi := (42734775264457 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_128 : (1328662129711 / 31250000000000 : ℝ) ≤ ex (65083 / 100000) 128 ∧ ex (65083 / 100000) 128 ≤ (5314648526029 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_128
  have hlo := exp_neg_ge_of (q := (789461714433273 / 250000000000000 : ℝ)) (a := (16846534494295450837 / 25000000000000000000 : ℝ)) (lo := (1328662129711 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3157846856381969 / 1000000000000000 : ℝ)) (b := (67386137988569145903 / 100000000000000000000 : ℝ)) (hi := (5314648526029 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_129 : (42302389371651 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 129 ∧ ex (65083 / 100000) 129 ≤ (42302389428841 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_129
  have hlo := exp_neg_ge_of (q := (632582341639399 / 200000000000000 : ℝ)) (a := (67343488890284920861 / 100000000000000000000 : ℝ)) (lo := (42302389371651 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3162911706845871 / 1000000000000000 : ℝ)) (b := (16835872225416298623 / 25000000000000000000 : ℝ)) (hi := (42302389428841 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_131 : (41880930502427 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 131 ∧ ex (65083 / 100000) 131 ≤ (5235116319881 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_131
  have hlo := exp_neg_ge_of (q := (1586462337462647 / 500000000000000 : ℝ)) (a := (16814813275677932441 / 25000000000000000000 : ℝ)) (lo := (41880930502427 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (317292467357417 / 100000000000000 : ℝ)) (b := (67259253114078031837 / 100000000000000000000 : ℝ)) (hi := (5235116319881 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_132 : (8334832251489 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 132 ∧ ex (65083 / 100000) 132 ≤ (41674161313787 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_132
  have hlo := exp_neg_ge_of (q := (397234247042897 / 125000000000000 : ℝ)) (a := (2100551724437047377 / 3125000000000000000 : ℝ)) (lo := (8334832251489 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (794468493748013 / 250000000000000 : ℝ)) (b := (6721765519334492203 / 10000000000000000000 : ℝ)) (hi := (41674161313787 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_133 : (41469961869853 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 133 ∧ ex (65083 / 100000) 133 ≤ (259187262037 / 6250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_133
  have hlo := exp_neg_ge_of (q := (795696481046713 / 250000000000000 : ℝ)) (a := (33588198323731821841 / 50000000000000000000 : ℝ)) (lo := (41469961869853 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (198924120177233 / 62500000000000 : ℝ)) (b := (67176396658816212093 / 100000000000000000000 : ℝ)) (hi := (259187262037 / 6250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_134 : (41268281435301 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 134 ∧ ex (65083 / 100000) 134 ≤ (5158535186387 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_134
  have hlo := exp_neg_ge_of (q := (159383053903417 / 50000000000000 : ℝ)) (a := (33567736104715384723 / 50000000000000000000 : ℝ)) (lo := (41268281435301 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (99614408647413 / 31250000000000 : ℝ)) (b := (1678386805519413949 / 2500000000000000000 : ℝ)) (hi := (5158535186387 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_136 : (40872280652757 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 136 ∧ ex (65083 / 100000) 136 ≤ (20436140354009 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_136
  have hlo := exp_neg_ge_of (q := (3197303180349883 / 1000000000000000 : ℝ)) (a := (33527302533039352471 / 50000000000000000000 : ℝ)) (lo := (40872280652757 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3197303178998759 / 1000000000000000 : ℝ)) (b := (33527302538705551581 / 50000000000000000000 : ℝ)) (hi := (20436140354009 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_137 : (40677865201261 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 137 ∧ ex (65083 / 100000) 137 ≤ (2033893262813 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_137
  have hlo := exp_neg_ge_of (q := (3202071187023007 / 1000000000000000 : ℝ)) (a := (33507326186314097639 / 50000000000000000000 : ℝ)) (lo := (40677865201261 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3202071185671883 / 1000000000000000 : ℝ)) (b := (67014652383953981413 / 100000000000000000000 : ℝ)) (hi := (2033893262813 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_138 : (20242889203577 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 138 ∧ ex (65083 / 100000) 138 ≤ (20242889230947 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_138
  have hlo := exp_neg_ge_of (q := (6263290072221 / 1953125000000 : ℝ)) (a := (66975013792509081151 / 100000000000000000000 : ℝ)) (lo := (20242889203577 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (801701128906507 / 250000000000000 : ℝ)) (b := (66975013803828309479 / 100000000000000000000 : ℝ)) (hi := (20242889230947 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_139 : (20147987902583 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 139 ∧ ex (65083 / 100000) 139 ≤ (805919517193 / 20000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_139
  have hlo := exp_neg_ge_of (q := (401437958870717 / 125000000000000 : ℝ)) (a := (16733921151652186851 / 25000000000000000000 : ℝ)) (lo := (20147987902583 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (802875917403653 / 250000000000000 : ℝ)) (b := (13387136923584294281 / 20000000000000000000 : ℝ)) (hi := (805919517193 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_141 : (39923051083103 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 141 ∧ ex (65083 / 100000) 141 ≤ (9980762784271 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_141
  have hlo := exp_neg_ge_of (q := (3220801400521111 / 1000000000000000 : ℝ)) (a := (66857936059036046889 / 100000000000000000000 : ℝ)) (lo := (39923051083103 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3220801399169987 / 1000000000000000 : ℝ)) (b := (66857936070335919573 / 100000000000000000000 : ℝ)) (hi := (9980762784271 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_142 : (39739845685611 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 142 ∧ ex (65083 / 100000) 142 ≤ (7947969147869 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_142
  have hlo := exp_neg_ge_of (q := (3225400924964917 / 1000000000000000 : ℝ)) (a := (66819507768190166943 / 100000000000000000000 : ℝ)) (lo := (39739845685611 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3225400923613793 / 1000000000000000 : ℝ)) (b := (66819507779483691127 / 100000000000000000000 : ℝ)) (hi := (7947969147869 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_143 : (9889689463309 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 143 ∧ ex (65083 / 100000) 143 ≤ (39558757906727 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_143
  have hlo := exp_neg_ge_of (q := (403746021472293 / 125000000000000 : ℝ)) (a := (66781371007484661447 / 100000000000000000000 : ℝ)) (lo := (9889689463309 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (161498408521361 / 50000000000000 : ℝ)) (b := (6678137101877188759 / 10000000000000000000 : ℝ)) (hi := (39558757906727 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_144 : (39379748557173 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 144 ∧ ex (65083 / 100000) 144 ≤ (39379748610421 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_144
  have hlo := exp_neg_ge_of (q := (3234503590829337 / 1000000000000000 : ℝ)) (a := (66743521549655435667 / 100000000000000000000 : ℝ)) (lo := (39379748557173 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3234503589478213 / 1000000000000000 : ℝ)) (b := (66743521560936413511 / 100000000000000000000 : ℝ)) (hi := (39379748610421 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

end PsiOmega.Locate.Z2

#print axioms PsiOmega.Locate.Z2.exB_144
