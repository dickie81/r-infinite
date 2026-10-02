import DHLocate4Base

/-! # Generated (`gen_locate_zero.py 4`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 72426 / 100000`, `n ∈ NS`

`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` with `exp(-(y/8))` from `Real.exp_bound`
(`exp_neg_ge_of`, `exp_neg_le_of`, `DHLocateExp`). -/

open Real Finset

namespace PsiOmega.Locate.Z4

theorem exB_2 : (151326861160847 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 2 ∧ ex (72426 / 100000) 2 ≤ (60530744473107 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_2
  have hlo := exp_neg_ge_of (q := (502018777063171 / 1000000000000000 : ℝ)) (a := (46958801726421564413 / 50000000000000000000 : ℝ)) (lo := (151326861160847 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (251009388459159 / 500000000000000 : ℝ)) (b := (46958801727271829827 / 50000000000000000000 : ℝ)) (hi := (60530744473107 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_3 : (45127384153337 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 3 ∧ ex (72426 / 100000) 3 ≤ (112818460405263 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_3
  have hlo := exp_neg_ge_of (q := (795680936307753 / 1000000000000000 : ℝ)) (a := (45266302811638120963 / 50000000000000000000 : ℝ)) (lo := (45127384153337 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (795680936113457 / 1000000000000000 : ℝ)) (b := (2263315140636875183 / 2500000000000000000 : ℝ)) (hi := (112818460405263 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_4 : (183198551272291 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 4 ∧ ex (72426 / 100000) 4 ≤ (91599275655341 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_4
  have hlo := exp_neg_ge_of (q := (1004037554115771 / 1000000000000000 : ℝ)) (a := (88205162383371468029 / 100000000000000000000 : ℝ)) (lo := (183198551272291 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1004037553906213 / 1000000000000000 : ℝ)) (b := (44102581192840990107 / 50000000000000000000 : ℝ)) (hi := (91599275655341 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_6 : (68289853963897 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 6 ∧ ex (72426 / 100000) 6 ≤ (68289853981749 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_6
  have hlo := exp_neg_ge_of (q := (64884985668067 / 50000000000000 : ℝ)) (a := (85026053544896801467 / 100000000000000000000 : ℝ)) (lo := (68289853963897 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1297699713099927 / 1000000000000000 : ℝ)) (b := (42513026773837583043 / 50000000000000000000 : ℝ)) (hi := (68289853981749 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_7 : (244303277547041 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 7 ∧ ex (72426 / 100000) 7 ≤ (48860655522221 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_7
  have hlo := exp_neg_ge_of (q := (1409344884733769 / 1000000000000000 : ℝ)) (a := (83847701462116634447 / 100000000000000000000 : ℝ)) (lo := (244303277547041 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1409344884471543 / 1000000000000000 : ℝ)) (b := (83847701464865015773 / 100000000000000000000 : ℝ)) (hi := (48860655522221 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_8 : (221782893863627 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 8 ∧ ex (72426 / 100000) 8 ≤ (221782893930179 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_8
  have hlo := exp_neg_ge_of (q := (376514082797413 / 250000000000000 : ℝ)) (a := (82840174632040267349 / 100000000000000000000 : ℝ)) (lo := (221782893863627 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (753028165444789 / 500000000000000 : ℝ)) (b := (41420087317573770533 / 50000000000000000000 : ℝ)) (hi := (221782893930179 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_9 : (203648080054417 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 9 ∧ ex (72426 / 100000) 9 ≤ (203648080118023 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_9
  have hlo := exp_neg_ge_of (q := (19892023407563 / 12500000000000 : ℝ)) (a := (512259542559399467 / 625000000000000000 : ℝ)) (lo := (203648080054417 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1591361872292709 / 1000000000000000 : ℝ)) (b := (81961526812703807161 / 100000000000000000000 : ℝ)) (hi := (203648080118023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_11 : (22012579970983 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 11 ∧ ex (72426 / 100000) 11 ≤ (176100639823981 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_11
  have hlo := exp_neg_ge_of (q := (434174907626521 / 250000000000000 : ℝ)) (a := (80485957818780871309 / 100000000000000000000 : ℝ)) (lo := (22012579970983 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (54271863443357 / 31250000000000 : ℝ)) (b := (4024297891099341659 / 5000000000000000000 : ℝ)) (hi := (176100639823981 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_12 : (165345427995001 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 12 ∧ ex (72426 / 100000) 12 ≤ (10334089252989 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_12
  have hlo := exp_neg_ge_of (q := (1799718490405309 / 1000000000000000 : ℝ)) (a := (79854431800089909439 / 100000000000000000000 : ℝ)) (lo := (165345427995001 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (449929622521461 / 250000000000000 : ℝ)) (b := (79854431803278754047 / 100000000000000000000 : ℝ)) (hi := (10334089252989 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_13 : (78016307594141 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 13 ∧ ex (72426 / 100000) 13 ≤ (15603261523819 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_13
  have hlo := exp_neg_ge_of (q := (1857690221865283 / 1000000000000000 : ℝ)) (a := (79277860914386246331 / 100000000000000000000 : ℝ)) (lo := (78016307594141 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1857690221545437 / 1000000000000000 : ℝ)) (b := (19819465229388961447 / 25000000000000000000 : ℝ)) (hi := (15603261523819 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_14 : (147878592652877 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 14 ∧ ex (72426 / 100000) 14 ≤ (29575718540041 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_14
  have hlo := exp_neg_ge_of (q := (1911363661777507 / 1000000000000000 : ℝ)) (a := (39373875881852862233 / 50000000000000000000 : ℝ)) (lo := (147878592652877 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1911363661457471 / 1000000000000000 : ℝ)) (b := (78747751766856004551 / 100000000000000000000 : ℝ)) (hi := (29575718540041 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_16 : (16780854593907 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 16 ∧ ex (72426 / 100000) 16 ≤ (13424683680131 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_16
  have hlo := exp_neg_ge_of (q := (2008075108245009 / 1000000000000000 : ℝ)) (a := (77801506710638294283 / 100000000000000000000 : ℝ)) (lo := (16780854593907 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2008075107872169 / 1000000000000000 : ℝ)) (b := (77801506714264261801 / 100000000000000000000 : ℝ)) (hi := (13424683680131 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_17 : (64239931386111 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 17 ∧ ex (72426 / 100000) 17 ≤ (128479862824497 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_17
  have hlo := exp_neg_ge_of (q := (2051983096870941 / 1000000000000000 : ℝ)) (a := (15475132588425316423 / 20000000000000000000 : ℝ)) (lo := (64239931386111 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2051983096464081 / 1000000000000000 : ℝ)) (b := (77375662946061751577 / 100000000000000000000 : ℝ)) (hi := (128479862824497 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_18 : (123269698940601 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 18 ∧ ex (72426 / 100000) 18 ≤ (61634849496767 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_18
  have hlo := exp_neg_ge_of (q := (261672581212247 / 125000000000000 : ℝ)) (a := (38488150866279576269 / 50000000000000000000 : ℝ)) (lo := (123269698940601 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (261672581158573 / 125000000000000 : ℝ)) (b := (76976301736690825177 / 100000000000000000000 : ℝ)) (hi := (61634849496767 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_19 : (118535904185899 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 19 ∧ ex (72426 / 100000) 19 ≤ (118535904238609 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_19
  have hlo := exp_neg_ge_of (q := (1066269687694137 / 500000000000000 : ℝ)) (a := (4787527228112403997 / 6250000000000000000 : ℝ)) (lo := (118535904185899 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2132539374943613 / 1000000000000000 : ℝ)) (b := (4787527228378510967 / 6250000000000000000 : ℝ)) (hi := (118535904238609 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_21 : (55123839275799 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 21 ∧ ex (72426 / 100000) 21 ≤ (6890479912663 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_21
  have hlo := exp_neg_ge_of (q := (2205025821098187 / 1000000000000000 : ℝ)) (a := (75909508888342320943 / 100000000000000000000 : ℝ)) (lo := (55123839275799 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2205025820635521 / 1000000000000000 : ℝ)) (b := (75909508892732501513 / 100000000000000000000 : ℝ)) (hi := (6890479912663 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_22 : (2131900565037 / 20000000000000 : ℝ) ≤ ex (72426 / 100000) 22 ∧ ex (72426 / 100000) 22 ≤ (53297514150869 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_22
  have hlo := exp_neg_ge_of (q := (447743681525297 / 200000000000000 : ℝ)) (a := (3779524134946217877 / 5000000000000000000 : ℝ)) (lo := (2131900565037 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2238718407158487 / 1000000000000000 : ℝ)) (b := (37795241351673243101 / 50000000000000000000 : ℝ)) (hi := (53297514150869 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_23 : (103217894857017 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 23 ∧ ex (72426 / 100000) 23 ≤ (51608947452863 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_23
  have hlo := exp_neg_ge_of (q := (2270913041189361 / 1000000000000000 : ℝ)) (a := (15057378598937604639 / 20000000000000000000 : ℝ)) (lo := (103217894857017 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (454182608143497 / 200000000000000 : ℝ)) (b := (37643446499564453377 / 50000000000000000000 : ℝ)) (hi := (51608947452863 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_24 : (50042409248443 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 24 ∧ ex (72426 / 100000) 24 ≤ (50042409272201 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_24
  have hlo := exp_neg_ge_of (q := (230173726753077 / 100000000000000 : ℝ)) (a := (74997368596945422301 / 100000000000000000000 : ℝ)) (lo := (50042409248443 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1150868633528017 / 500000000000000 : ℝ)) (b := (7499736860139606171 / 10000000000000000000 : ℝ)) (hi := (50042409272201 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_26 : (11805962946811 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 26 ∧ ex (72426 / 100000) 26 ≤ (94447703619683 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_26
  have hlo := exp_neg_ge_of (q := (2359708998993621 / 1000000000000000 : ℝ)) (a := (14891173407772621137 / 20000000000000000000 : ℝ)) (lo := (11805962946811 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2359708998515133 / 1000000000000000 : ℝ)) (b := (3722793352165829087 / 5000000000000000000 : ℝ)) (hi := (94447703619683 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_27 : (5743815712787 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 27 ∧ ex (72426 / 100000) 27 ≤ (45950525724341 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_27
  have hlo := exp_neg_ge_of (q := (477408561787907 / 200000000000000 : ℝ)) (a := (7420190582901575451 / 10000000000000000000 : ℝ)) (lo := (5743815712787 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1193521404229907 / 500000000000000 : ℝ)) (b := (74201905833465506337 / 100000000000000000000 : ℝ)) (hi := (45950525724341 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_28 : (17902402606037 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 28 ∧ ex (72426 / 100000) 28 ≤ (17902402614643 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_28
  have hlo := exp_neg_ge_of (q := (2413382438907549 / 1000000000000000 : ℝ)) (a := (14791600245769597457 / 20000000000000000000 : ℝ)) (lo := (17902402606037 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (603345609606719 / 250000000000000 : ℝ)) (b := (73958001233291946051 / 100000000000000000000 : ℝ)) (hi := (17902402614643 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_29 : (10908213734801 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 29 ∧ ex (72426 / 100000) 29 ≤ (87265709920423 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_29
  have hlo := exp_neg_ge_of (q := (487759535638939 / 200000000000000 : ℝ)) (a := (73723416515507972649 / 100000000000000000000 : ℝ)) (lo := (10908213734801 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3810621371427 / 1562500000000 : ℝ)) (b := (73723416519944708867 / 100000000000000000000 : ℝ)) (hi := (87265709920423 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_31 : (83150789949803 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 31 ∧ ex (72426 / 100000) 31 ≤ (20787697497481 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_31
  have hlo := exp_neg_ge_of (q := (2487099573089997 / 1000000000000000 : ℝ)) (a := (1144994296753130629 / 1562500000000000000 : ℝ)) (lo := (83150789949803 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (124354978630377 / 50000000000000 : ℝ)) (b := (36639817498310006541 / 50000000000000000000 : ℝ)) (hi := (20787697497481 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_32 : (20315152425863 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 32 ∧ ex (72426 / 100000) 32 ≤ (81260609742691 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_32
  have hlo := exp_neg_ge_of (q := (2510093885331631 / 1000000000000000 : ℝ)) (a := (73069310552619849577 / 100000000000000000000 : ℝ)) (lo := (20315152425863 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (502018776969761 / 200000000000000 : ℝ)) (b := (18267327639257557929 / 25000000000000000000 : ℝ)) (hi := (81260609742691 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_33 : (15893922440523 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 33 ∧ ex (72426 / 100000) 33 ≤ (79469612241013 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_33
  have hlo := exp_neg_ge_of (q := (2532380566837867 / 1000000000000000 : ℝ)) (a := (1138531793343344577 / 1562500000000000000 : ℝ)) (lo := (15893922440523 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1266190283177373 / 500000000000000 : ℝ)) (b := (72866034778374899727 / 100000000000000000000 : ℝ)) (hi := (79469612241013 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_34 : (77769817423191 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 34 ∧ ex (72426 / 100000) 34 ≤ (77769817460787 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_34
  have hlo := exp_neg_ge_of (q := (127700093696443 / 50000000000000 : ℝ)) (a := (36334684145521097259 / 50000000000000000000 : ℝ)) (lo := (77769817423191 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (5108003746891 / 2000000000000 : ℝ)) (b := (72669368295433384777 / 100000000000000000000 : ℝ)) (hi := (77769817460787 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_36 : (74616066469501 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 36 ∧ ex (72426 / 100000) 36 ≤ (23317520783 / 312500000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_36
  have hlo := exp_neg_ge_of (q := (519079885347377 / 200000000000000 : ℝ)) (a := (18073574453516906929 / 25000000000000000000 : ℝ)) (lo := (74616066469501 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2595399426253171 / 1000000000000000 : ℝ)) (b := (9036787227304932893 / 12500000000000000000 : ℝ)) (hi := (23317520783 / 312500000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_37 : (9143747656763 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 37 ∧ ex (72426 / 100000) 37 ≤ (2285936915297 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_37
  have hlo := exp_neg_ge_of (q := (2615243407782481 / 1000000000000000 : ℝ)) (a := (72115194204499686687 / 100000000000000000000 : ℝ)) (lo := (9143747656763 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (653810851824659 / 250000000000000 : ℝ)) (b := (7211519420886193249 / 10000000000000000000 : ℝ)) (hi := (2285936915297 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_38 : (896883315799 / 12500000000000 : ℝ) ≤ ex (72426 / 100000) 38 ∧ ex (72426 / 100000) 38 ≤ (71750665298651 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_38
  have hlo := exp_neg_ge_of (q := (26345581524143 / 10000000000000 : ℝ)) (a := (71941293397061386389 / 100000000000000000000 : ℝ)) (lo := (896883315799 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1317279075965173 / 500000000000000 : ℝ)) (b := (71941293401414156963 / 100000000000000000000 : ℝ)) (hi := (71750665298651 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_39 : (14082687531767 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 39 ∧ ex (72426 / 100000) 39 ≤ (2816537507717 / 40000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_39
  have hlo := exp_neg_ge_of (q := (2653371158196803 / 1000000000000000 : ℝ)) (a := (71772313167976782241 / 100000000000000000000 : ℝ)) (lo := (14082687531767 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2653371157712759 / 1000000000000000 : ℝ)) (b := (2870892526892808141 / 4000000000000000000 : ℝ)) (hi := (2816537507717 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_41 : (67908660451383 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 41 ∧ ex (72426 / 100000) 41 ≤ (67908660484271 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_41
  have hlo := exp_neg_ge_of (q := (1344795852701163 / 500000000000000 : ℝ)) (a := (14289618725549989461 / 20000000000000000000 : ℝ)) (lo := (67908660451383 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2689591704918143 / 1000000000000000 : ℝ)) (b := (71448093632075134563 / 100000000000000000000 : ℝ)) (hi := (67908660484271 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_42 : (66733740585419 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 42 ∧ ex (72426 / 100000) 42 ≤ (66733740617743 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_42
  have hlo := exp_neg_ge_of (q := (1353522299054511 / 500000000000000 : ℝ)) (a := (35646195770609776893 / 50000000000000000000 : ℝ)) (lo := (66733740585419 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1353522298812393 / 500000000000000 : ℝ)) (b := (71292391545535865943 / 100000000000000000000 : ℝ)) (hi := (66733740617743 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_43 : (65606087100977 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 43 ∧ ex (72426 / 100000) 43 ≤ (32803043566379 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_43
  have hlo := exp_neg_ge_of (q := (340510849520421 / 125000000000000 : ℝ)) (a := (71140680809311883367 / 100000000000000000000 : ℝ)) (lo := (65606087100977 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2724086795679087 / 1000000000000000 : ℝ)) (b := (35570340406809746223 / 50000000000000000000 : ℝ)) (hi := (32803043566379 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_44 : (64522764166477 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 44 ∧ ex (72426 / 100000) 44 ≤ (8065345524717 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_44
  have hlo := exp_neg_ge_of (q := (2740737184632821 / 1000000000000000 : ℝ)) (a := (7099276978976909991 / 10000000000000000000 : ℝ)) (lo := (64522764166477 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1370368592074251 / 500000000000000 : ℝ)) (b := (70992769794068175773 / 100000000000000000000 : ℝ)) (hi := (8065345524717 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_46 : (31239280090559 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 46 ∧ ex (72426 / 100000) 46 ≤ (976227503303 / 15625000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_46
  have hlo := exp_neg_ge_of (q := (1386465909096213 / 500000000000000 : ℝ)) (a := (8838455701905936719 / 12500000000000000000 : ℝ)) (lo := (31239280090559 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (554586363541609 / 200000000000000 : ℝ)) (b := (35353822809765017049 / 50000000000000000000 : ℝ)) (hi := (976227503303 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_47 : (15378232192119 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 47 ∧ ex (72426 / 100000) 47 ≤ (15378232199571 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_47
  have hlo := exp_neg_ge_of (q := (2788507902385781 / 1000000000000000 : ℝ)) (a := (70570111019195999819 / 100000000000000000000 : ℝ)) (lo := (15378232192119 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2788507901901377 / 1000000000000000 : ℝ)) (b := (70570111023470510243 / 100000000000000000000 : ℝ)) (hi := (15378232199571 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_48 : (2423283429429 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 48 ∧ ex (72426 / 100000) 48 ≤ (15145521441271 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_48
  have hlo := exp_neg_ge_of (q := (2803756044531421 / 1000000000000000 : ℝ)) (a := (4402233202468463309 / 6250000000000000000 : ℝ)) (lo := (2423283429429 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (700939011011749 / 250000000000000 : ℝ)) (b := (70435731243762069893 / 100000000000000000000 : ℝ)) (hi := (15145521441271 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_49 : (59684091419419 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 49 ∧ ex (72426 / 100000) 49 ≤ (7460511431043 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_49
  have hlo := exp_neg_ge_of (q := (281868976948089 / 100000000000000 : ℝ)) (a := (35152185202341725479 / 50000000000000000000 : ℝ)) (lo := (59684091419419 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2818689768996447 / 1000000000000000 : ℝ)) (b := (8788046301117801753 / 12500000000000000000 : ℝ)) (hi := (7460511431043 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_51 : (11595920247163 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 51 ∧ ex (72426 / 100000) 51 ≤ (28989800631959 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_51
  have hlo := exp_neg_ge_of (q := (355958004141029 / 125000000000000 : ℝ)) (a := (17512550945057768871 / 25000000000000000000 : ℝ)) (lo := (11595920247163 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (35595800408047 / 12500000000000 : ℝ)) (b := (35025101892237558747 / 50000000000000000000 : ℝ)) (hi := (28989800631959 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_52 : (57169898106853 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 52 ∧ ex (72426 / 100000) 52 ≤ (11433979626913 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_52
  have hlo := exp_neg_ge_of (q := (2861727775991107 / 1000000000000000 : ℝ)) (a := (34963582976754010739 / 50000000000000000000 : ℝ)) (lo := (57169898106853 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2861727775506623 / 1000000000000000 : ℝ)) (b := (69927165957744831319 / 100000000000000000000 : ℝ)) (hi := (11433979626913 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_53 : (28193303261357 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 53 ∧ ex (72426 / 100000) 53 ≤ (56386606550047 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_53
  have hlo := exp_neg_ge_of (q := (2875523621680591 / 1000000000000000 : ℝ)) (a := (17451670455193245077 / 25000000000000000000 : ℝ)) (lo := (28193303261357 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2875523621196097 / 1000000000000000 : ℝ)) (b := (69806681825002698797 / 100000000000000000000 : ℝ)) (hi := (56386606550047 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_54 : (27814195294727 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 54 ∧ ex (72426 / 100000) 54 ≤ (55628390616421 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_54
  have hlo := exp_neg_ge_of (q := (144453079296799 / 50000000000000 : ℝ)) (a := (34844325835763225879 / 50000000000000000000 : ℝ)) (lo := (27814195294727 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2889061585451477 / 1000000000000000 : ℝ)) (b := (69688651675749222509 / 100000000000000000000 : ℝ)) (hi := (55628390616421 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_56 : (54182287875833 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 56 ∧ ex (72426 / 100000) 56 ≤ (54182287902101 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_56
  have hlo := exp_neg_ge_of (q := (2915401215903191 / 1000000000000000 : ℝ)) (a := (69459582316342492513 / 100000000000000000000 : ℝ)) (lo := (54182287875833 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2915401215418673 / 1000000000000000 : ℝ)) (b := (34729791160275888243 / 50000000000000000000 : ℝ)) (hi := (54182287902101 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_57 : (53492152846017 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 57 ∧ ex (72426 / 100000) 57 ≤ (3343259554497 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_57
  have hlo := exp_neg_ge_of (q := (366027538951651 / 125000000000000 : ℝ)) (a := (3467418515662951583 / 5000000000000000000 : ℝ)) (lo := (53492152846017 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (732055077782171 / 250000000000000 : ℝ)) (b := (69348370317461766279 / 100000000000000000000 : ℝ)) (hi := (3343259554497 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_58 : (52822583852033 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 58 ∧ ex (72426 / 100000) 58 ≤ (52822583881449 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_58
  have hlo := exp_neg_ge_of (q := (117632658209893 / 40000000000000 : ℝ)) (a := (34619632987505757817 / 50000000000000000000 : ℝ)) (lo := (52822583852033 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1470408227345389 / 500000000000000 : ℝ)) (b := (69239265979831133023 / 100000000000000000000 : ℝ)) (hi := (52822583881449 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_59 : (208690516139 / 4000000000000 : ℝ) ≤ ex (72426 / 100000) 59 ∧ ex (72426 / 100000) 59 ≤ (13043157266813 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_59
  have hlo := exp_neg_ge_of (q := (2953197269604991 / 1000000000000000 : ℝ)) (a := (69132194036456711849 / 100000000000000000000 : ℝ)) (lo := (208690516139 / 4000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (295319726898237 / 100000000000000 : ℝ)) (b := (34566097020920001449 / 50000000000000000000 : ℝ)) (hi := (13043157266813 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_61 : (10185609197609 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 61 ∧ ex (72426 / 100000) 61 ≤ (5092804602571 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_61
  have hlo := exp_neg_ge_of (q := (2977341505441241 / 1000000000000000 : ℝ)) (a := (34461932782866377559 / 50000000000000000000 : ℝ)) (lo := (10185609197609 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1488670752351033 / 500000000000000 : ℝ)) (b := (13784773114420859759 / 20000000000000000000 : ℝ)) (hi := (5092804602571 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_62 : (50331792175727 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 62 ∧ ex (72426 / 100000) 62 ≤ (25165896107771 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_62
  have hlo := exp_neg_ge_of (q := (2989118350329001 / 1000000000000000 : ℝ)) (a := (1376449540043002037 / 2000000000000000000 : ℝ)) (lo := (50331792175727 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2989118349538371 / 1000000000000000 : ℝ)) (b := (17205619252238772513 / 25000000000000000000 : ℝ)) (hi := (25165896107771 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_63 : (1554746669091 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 63 ∧ ex (72426 / 100000) 63 ≤ (4975189345263 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_63
  have hlo := exp_neg_ge_of (q := (3000706757590549 / 1000000000000000 : ℝ)) (a := (34361428155429834443 / 50000000000000000000 : ℝ)) (lo := (1554746669091 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3000706756752451 / 1000000000000000 : ℝ)) (b := (8590357039757842241 / 12500000000000000000 : ℝ)) (hi := (4975189345263 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_64 : (12296912999379 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 64 ∧ ex (72426 / 100000) 64 ≤ (49187652040919 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_64
  have hlo := exp_neg_ge_of (q := (3012112662643371 / 1000000000000000 : ℝ)) (a := (68624945328400599539 / 100000000000000000000 : ℝ)) (lo := (12296912999379 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1506056330880713 / 500000000000000 : ℝ)) (b := (1372498906719393987 / 2000000000000000000 : ℝ)) (hi := (49187652040919 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_66 : (12025886968549 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 66 ∧ ex (72426 / 100000) 66 ≤ (48103547920401 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_66
  have hlo := exp_neg_ge_of (q := (1517199672105917 / 500000000000000 : ℝ)) (a := (68434033588169706719 / 100000000000000000000 : ℝ)) (lo := (12025886968549 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3034399343251789 / 1000000000000000 : ℝ)) (b := (68434033596386186651 / 100000000000000000000 : ℝ)) (hi := (48103547920401 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_67 : (11895619707663 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 67 ∧ ex (72426 / 100000) 67 ≤ (23791239439007 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_67
  have hlo := exp_neg_ge_of (q := (3045290677299723 / 1000000000000000 : ℝ)) (a := (68340929747314190953 / 100000000000000000000 : ℝ)) (lo := (11895619707663 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (304529067630487 / 100000000000000 : ℝ)) (b := (13668185951163405099 / 20000000000000000000 : ℝ)) (hi := (23791239439007 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_68 : (23537324718823 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 68 ∧ ex (72426 / 100000) 68 ≤ (5884331185753 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_68
  have hlo := exp_neg_ge_of (q := (1528010325678157 / 500000000000000 : ℝ)) (a := (13649865828031137129 / 20000000000000000000 : ℝ)) (lo := (23537324718823 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (611204130065831 / 200000000000000 : ℝ)) (b := (68249329148922917409 / 100000000000000000000 : ℝ)) (hi := (5884331185753 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_69 : (5822441988837 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 69 ∧ ex (72426 / 100000) 69 ≤ (11644883989991 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_69
  have hlo := exp_neg_ge_of (q := (306659397784909 / 100000000000000 : ℝ)) (a := (68159185917895886207 / 100000000000000000000 : ℝ)) (lo := (5822441988837 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (766648494197979 / 250000000000000 : ℝ)) (b := (34079592963453726809 / 50000000000000000000 : ℝ)) (hi := (11644883989991 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_71 : (1425796845937 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 71 ∧ ex (72426 / 100000) 71 ≤ (9125099824141 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_71
  have hlo := exp_neg_ge_of (q := (61745770572371 / 20000000000000 : ℝ)) (a := (8497887287849510069 / 12500000000000000000 : ℝ)) (lo := (1425796845937 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1543644263753733 / 500000000000000 : ℝ)) (b := (849788728903036029 / 1250000000000000000 : ℝ)) (hi := (9125099824141 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_72 : (5645707562953 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 72 ∧ ex (72426 / 100000) 72 ≤ (4516566055493 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_72
  have hlo := exp_neg_ge_of (q := (774354551062639 / 250000000000000 : ℝ)) (a := (67897071936205700939 / 100000000000000000000 : ℝ)) (lo := (5645707562953 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1548709101557623 / 500000000000000 : ℝ)) (b := (67897071945846362059 / 100000000000000000000 : ℝ)) (hi := (4516566055493 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_73 : (22358352003037 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 73 ∧ ex (72426 / 100000) 73 ≤ (44716704057881 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_73
  have hlo := exp_neg_ge_of (q := (3107408155756201 / 1000000000000000 : ℝ)) (a := (135624677590424289 / 200000000000000000 : ℝ)) (lo := (22358352003037 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (776852038649573 / 250000000000000 : ℝ)) (b := (67812338805032544429 / 100000000000000000000 : ℝ)) (hi := (44716704057881 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_74 : (22139114103559 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 74 ∧ ex (72426 / 100000) 74 ≤ (44278228259353 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_74
  have hlo := exp_neg_ge_of (q := (1558631092665501 / 500000000000000 : ℝ)) (a := (13545772423623209487 / 20000000000000000000 : ℝ)) (lo := (22139114103559 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3117262184151989 / 1000000000000000 : ℝ)) (b := (8466107766012905051 / 12500000000000000000 : ℝ)) (hi := (44278228259353 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_76 : (43431211819939 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 76 ∧ ex (72426 / 100000) 76 ≤ (21715605936417 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_76
  have hlo := exp_neg_ge_of (q := (3136576929993271 / 1000000000000000 : ℝ)) (a := (67565538647137241219 / 100000000000000000000 : ℝ)) (lo := (43431211819939 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (39207211609701 / 12500000000000 : ℝ)) (b := (844569233217790377 / 1250000000000000000 : ℝ)) (hi := (21715605936417 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_77 : (43021963449159 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 77 ∧ ex (72426 / 100000) 77 ≤ (43021963502301 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_77
  have hlo := exp_neg_ge_of (q := (393255564475383 / 125000000000000 : ℝ)) (a := (33742812813029781859 / 50000000000000000000 : ℝ)) (lo := (43021963449159 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (629208902913719 / 200000000000000 : ℝ)) (b := (13497125127295873173 / 20000000000000000000 : ℝ)) (hi := (43021963502301 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_78 : (10655444498669 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 78 ∧ ex (72426 / 100000) 78 ≤ (8524355609603 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_78
  have hlo := exp_neg_ge_of (q := (3155389935802471 / 1000000000000000 : ℝ)) (a := (3370341823272839107 / 5000000000000000000 : ℝ)) (lo := (10655444498669 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (788847483637953 / 250000000000000 : ℝ)) (b := (67406836476001065247 / 100000000000000000000 : ℝ)) (hi := (8524355609603 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_79 : (42230342377369 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 79 ∧ ex (72426 / 100000) 79 ≤ (2111517121543 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_79
  have hlo := exp_neg_ge_of (q := (1582308151312091 / 500000000000000 : ℝ)) (a := (67329141251911973889 / 100000000000000000000 : ℝ)) (lo := (42230342377369 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (12361782427181 / 3906250000000 : ℝ)) (b := (16832285315643038831 / 25000000000000000000 : ℝ)) (hi := (2111517121543 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_81 : (20736270243057 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 81 ∧ ex (72426 / 100000) 81 ≤ (8294508107959 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_81
  have hlo := exp_neg_ge_of (q := (1591361872890797 / 500000000000000 : ℝ)) (a := (67176918764644483307 / 100000000000000000000 : ℝ)) (lo := (20736270243057 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1591361872244051 / 500000000000000 : ℝ)) (b := (16794229693878298927 / 25000000000000000000 : ℝ)) (hi := (8294508107959 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_82 : (8221123540567 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 82 ∧ ex (72426 / 100000) 82 ≤ (41105617756559 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_82
  have hlo := exp_neg_ge_of (q := (3191610483052213 / 1000000000000000 : ℝ)) (a := (16775584310749724049 / 25000000000000000000 : ℝ)) (lo := (8221123540567 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (797902620436533 / 250000000000000 : ℝ)) (b := (3355116862698069283 / 5000000000000000000 : ℝ)) (hi := (41105617756559 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_83 : (5093291275767 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 83 ∧ ex (72426 / 100000) 83 ≤ (325970642079 / 8000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_83
  have hlo := exp_neg_ge_of (q := (800097374910211 / 250000000000000 : ℝ)) (a := (67028741065289290819 / 100000000000000000000 : ℝ)) (lo := (5093291275767 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3200389498322919 / 1000000000000000 : ℝ)) (b := (33514370538169623721 / 50000000000000000000 : ℝ)) (hi := (325970642079 / 8000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_84 : (20197214980391 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 84 ∧ ex (72426 / 100000) 84 ≤ (10098607503627 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_84
  have hlo := exp_neg_ge_of (q := (160453168788863 / 50000000000000 : ℝ)) (a := (66956105574660211229 / 100000000000000000000 : ℝ)) (lo := (20197214980391 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3209063374448183 / 1000000000000000 : ℝ)) (b := (33478052792895894769 / 50000000000000000000 : ℝ)) (hi := (10098607503627 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_86 : (9927963227859 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 86 ∧ ex (72426 / 100000) 86 ≤ (39711852965067 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_86
  have hlo := exp_neg_ge_of (q := (32261055738479 / 10000000000000 : ℝ)) (a := (66813622490946036607 / 100000000000000000000 : ℝ)) (lo := (9927963227859 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3226105572498407 / 1000000000000000 : ℝ)) (b := (66813622502224967097 / 100000000000000000000 : ℝ)) (hi := (39711852965067 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_87 : (7876146421577 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 87 ∧ ex (72426 / 100000) 87 ≤ (39380732161439 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_87
  have hlo := exp_neg_ge_of (q := (3234478615087581 / 1000000000000000 : ℝ)) (a := (1668593248027511613 / 2500000000000000000 : ℝ)) (lo := (7876146421577 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3234478613728741 / 1000000000000000 : ℝ)) (b := (16685932483111462771 / 25000000000000000000 : ℝ)) (hi := (39380732161439 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_88 : (39056109474069 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 88 ∧ ex (72426 / 100000) 88 ≤ (39056109527527 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_88
  have hlo := exp_neg_ge_of (q := (3242755962331859 / 1000000000000000 : ℝ)) (a := (66674708006038249263 / 100000000000000000000 : ℝ)) (lo := (39056109474069 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3242755960964193 / 1000000000000000 : ℝ)) (b := (66674708017445739773 / 100000000000000000000 : ℝ)) (hi := (39056109527527 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_89 : (19368892896201 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 89 ∧ ex (72426 / 100000) 89 ≤ (38737785845749 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_89
  have hlo := exp_neg_ge_of (q := (3250939778226743 / 1000000000000000 : ℝ)) (a := (66606536189187104491 / 100000000000000000000 : ℝ)) (lo := (19368892896201 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3250939776850739 / 1000000000000000 : ℝ)) (b := (8325817025081579301 / 12500000000000000000 : ℝ)) (hi := (38737785845749 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_91 : (19059639634239 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 91 ∧ ex (72426 / 100000) 91 ≤ (38119279321561 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_91
  have hlo := exp_neg_ge_of (q := (3267035107286709 / 1000000000000000 : ℝ)) (a := (531781313114588941 / 800000000000000000 : ℝ)) (lo := (19059639634239 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (653407021179073 / 200000000000000 : ℝ)) (b := (1329453283017882857 / 2000000000000000000 : ℝ)) (hi := (38119279321561 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_92 : (37818737583217 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 92 ∧ ex (72426 / 100000) 92 ≤ (756374752723 / 20000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_92
  have hlo := exp_neg_ge_of (q := (3274950595915999 / 1000000000000000 : ℝ)) (a := (8300865776784946971 / 12500000000000000000 : ℝ)) (lo := (37818737583217 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1637475297258799 / 500000000000000 : ℝ)) (b := (16601731556474383489 / 25000000000000000000 : ℝ)) (hi := (756374752723 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_93 : (9380944095957 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 93 ∧ ex (72426 / 100000) 93 ≤ (37523776436599 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_93
  have hlo := exp_neg_ge_of (q := (1641390255009493 / 500000000000000 : ℝ)) (a := (66341962944503885473 / 100000000000000000000 : ℝ)) (lo := (9380944095957 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (32827805086139 / 10000000000000 : ℝ)) (b := (3317098147808310817 / 5000000000000000000 : ℝ)) (hi := (37523776436599 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_94 : (37234233700361 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 94 ∧ ex (72426 / 100000) 94 ≤ (37234233752963 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_94
  have hlo := exp_neg_ge_of (q := (13162106720479 / 4000000000000 : ℝ)) (a := (66277757017673527843 / 100000000000000000000 : ℝ)) (lo := (37234233700361 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3290526678708329 / 1000000000000000 : ℝ)) (b := (66277757029377361317 / 100000000000000000000 : ℝ)) (hi := (37234233752963 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_96 : (9167696870719 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 96 ∧ ex (72426 / 100000) 96 ≤ (18335393767557 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_96
  have hlo := exp_neg_ge_of (q := (206610926392171 / 62500000000000 : ℝ)) (a := (66151550748986342453 / 100000000000000000000 : ℝ)) (lo := (9167696870719 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (330577482085161 / 100000000000000 : ℝ)) (b := (33075775380382651347 / 50000000000000000000 : ℝ)) (hi := (18335393767557 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_97 : (9099147642199 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 97 ∧ ex (72426 / 100000) 97 ≤ (18198295310421 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_97
  have hlo := exp_neg_ge_of (q := (3313280174417429 / 1000000000000000 : ℝ)) (a := (13217903703300133867 / 20000000000000000000 : ℝ)) (lo := (9099147642199 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3313280172988893 / 1000000000000000 : ℝ)) (b := (3304475926415679847 / 5000000000000000000 : ℝ)) (hi := (18198295310421 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_98 : (2257951552377 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 98 ∧ ex (72426 / 100000) 98 ≤ (36127224889879 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_98
  have hlo := exp_neg_ge_of (q := (3320708547232627 / 1000000000000000 : ℝ)) (a := (66028179800995778831 / 100000000000000000000 : ℝ)) (lo := (2257951552377 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1660354272899477 / 500000000000000 : ℝ)) (b := (6602817981284046551 / 10000000000000000000 : ℝ)) (hi := (36127224889879 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_99 : (17931278580287 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 99 ∧ ex (72426 / 100000) 99 ≤ (17931278606109 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_99
  have hlo := exp_neg_ge_of (q := (3328061503793063 / 1000000000000000 : ℝ)) (a := (65967519889891362251 / 100000000000000000000 : ℝ)) (lo := (17931278580287 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (832015375588627 / 250000000000000 : ℝ)) (b := (8245939987720719139 / 12500000000000000000 : ℝ)) (hi := (17931278606109 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_101 : (276146937797 / 7812500000000 : ℝ) ≤ ex (72426 / 100000) 101 ∧ ex (72426 / 100000) 101 ≤ (883670202231 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_101
  have hlo := exp_neg_ge_of (q := (3342547186669281 / 1000000000000000 : ℝ)) (a := (16462044973980465627 / 25000000000000000000 : ℝ)) (lo := (276146937797 / 7812500000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3342547185221669 / 1000000000000000 : ℝ)) (b := (65848179907849992261 / 100000000000000000000 : ℝ)) (hi := (883670202231 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_102 : (35095484240773 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 102 ∧ ex (72426 / 100000) 102 ≤ (35095484291783 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_102
  have hlo := exp_neg_ge_of (q := (1674841405447229 / 500000000000000 : ℝ)) (a := (65789472598433474967 / 100000000000000000000 : ℝ)) (lo := (35095484240773 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (837420702360661 / 250000000000000 : ℝ)) (b := (65789472610385869321 / 100000000000000000000 : ℝ)) (hi := (35095484291783 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_103 : (34848373365787 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 103 ∧ ex (72426 / 100000) 103 ≤ (17424186708289 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_103
  have hlo := exp_neg_ge_of (q := (839187204540897 / 250000000000000 : ℝ)) (a := (65731389641669751603 / 100000000000000000000 : ℝ)) (lo := (34848373365787 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3356748816707773 / 1000000000000000 : ℝ)) (b := (65731389653644815531 / 100000000000000000000 : ℝ)) (hi := (17424186708289 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_104 : (34605364908989 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 104 ∧ ex (72426 / 100000) 104 ≤ (34605364959559 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_104
  have hlo := exp_neg_ge_of (q := (840936638440893 / 250000000000000 : ℝ)) (a := (16418479605048279853 / 25000000000000000000 : ℝ)) (lo := (34605364908989 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1681873276151973 / 500000000000000 : ℝ)) (b := (16418479608047337801 / 25000000000000000000 : ℝ)) (hi := (34605364959559 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_106 : (8532808170481 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 106 ∧ ex (72426 / 100000) 106 ≤ (17065616366023 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_106
  have hlo := exp_neg_ge_of (q := (844385599864681 / 250000000000000 : ℝ)) (a := (16390190652537614117 / 25000000000000000000 : ℝ)) (lo := (8532808170481 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1688771198996001 / 500000000000000 : ℝ)) (b := (16390190655546222581 / 25000000000000000000 : ℝ)) (hi := (17065616366023 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_107 : (16949953417851 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 107 ∧ ex (72426 / 100000) 107 ≤ (33899906885599 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_107
  have hlo := exp_neg_ge_of (q := (1692171506403571 / 500000000000000 : ℝ)) (a := (1310101092337401761 / 2000000000000000000 : ℝ)) (lo := (16949953417851 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (676868602267423 / 200000000000000 : ℝ)) (b := (65505054628921724593 / 100000000000000000000 : ℝ)) (hi := (33899906885599 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_108 : (33672278933027 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 108 ∧ ex (72426 / 100000) 108 ≤ (4209034872837 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_108
  have hlo := exp_neg_ge_of (q := (3391080363719271 / 1000000000000000 : ℝ)) (a := (65449911522593444743 / 100000000000000000000 : ℝ)) (lo := (33672278933027 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (847770090561523 / 250000000000000 : ℝ)) (b := (16362477883665273691 / 25000000000000000000 : ℝ)) (hi := (4209034872837 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_109 : (33448256432687 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 109 ∧ ex (72426 / 100000) 109 ≤ (33448256482127 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_109
  have hlo := exp_neg_ge_of (q := (849438904586993 / 250000000000000 : ℝ)) (a := (6539532244740396743 / 10000000000000000000 : ℝ)) (lo := (33448256432687 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1698877808435891 / 500000000000000 : ℝ)) (b := (16348830614871635409 / 25000000000000000000 : ℝ)) (hi := (33448256482127 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_111 : (33010673026079 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 111 ∧ ex (72426 / 100000) 111 ≤ (33010673075061 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_111
  have hlo := exp_neg_ge_of (q := (1705462172385831 / 500000000000000 : ℝ)) (a := (65287764358043474789 / 100000000000000000000 : ℝ)) (lo := (33010673026079 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3410924343289849 / 1000000000000000 : ℝ)) (b := (32643882185076415777 / 50000000000000000000 : ℝ)) (hi := (33010673075061 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_112 : (6559388439017 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 112 ∧ ex (72426 / 100000) 112 ≤ (16398471121919 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_112
  have hlo := exp_neg_ge_of (q := (3417419993695477 / 1000000000000000 : ℝ)) (a := (13046955014780926767 / 20000000000000000000 : ℝ)) (lo := (6559388439017 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1708709996105519 / 500000000000000 : ℝ)) (b := (521878200688207727 / 800000000000000000 : ℝ)) (hi := (16398471121919 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_113 : (32586476669717 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 113 ∧ ex (72426 / 100000) 113 ≤ (32586476718241 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_113
  have hlo := exp_neg_ge_of (q := (1711928951376951 / 500000000000000 : ℝ)) (a := (65182299247726941863 / 100000000000000000000 : ℝ)) (lo := (32586476669717 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (68477158025339 / 20000000000000 : ℝ)) (b := (65182299259859393641 / 100000000000000000000 : ℝ)) (hi := (32586476718241 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_114 : (505924973811 / 15625000000000 : ℝ) ≤ ex (72426 / 100000) 114 ∧ ex (72426 / 100000) 114 ≤ (32379198372199 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_114
  have hlo := exp_neg_ge_of (q := (1715119544704711 / 500000000000000 : ℝ)) (a := (16282581856458419847 / 25000000000000000000 : ℝ)) (lo := (505924973811 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3430239087920067 / 1000000000000000 : ℝ)) (b := (65130327437976420739 / 100000000000000000000 : ℝ)) (hi := (32379198372199 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_116 : (15986951614583 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 116 ∧ ex (72426 / 100000) 116 ≤ (31973903277003 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_116
  have hlo := exp_neg_ge_of (q := (1721417616494761 / 500000000000000 : ℝ)) (a := (65027859246536374411 / 100000000000000000000 : ℝ)) (lo := (15986951614583 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (688567046299133 / 200000000000000 : ℝ)) (b := (127007537614643397 / 195312500000000000 : ℝ)) (hi := (31973903277003 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_117 : (31775742485799 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 117 ∧ ex (72426 / 100000) 117 ≤ (992991954169 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_117
  have hlo := exp_neg_ge_of (q := (3449052095197137 / 1000000000000000 : ℝ)) (a := (3248867261071247677 / 5000000000000000000 : ℝ)) (lo := (31775742485799 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (344905209370117 / 100000000000000 : ℝ)) (b := (64977345233594103083 / 100000000000000000000 : ℝ)) (hi := (992991954169 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_118 : (31580480741413 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 118 ∧ ex (72426 / 100000) 118 ≤ (6316096157759 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_118
  have hlo := exp_neg_ge_of (q := (3455216047297633 / 1000000000000000 : ℝ)) (a := (32463649924142644167 / 50000000000000000000 : ℝ)) (lo := (31580480741413 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (691043209159929 / 200000000000000 : ℝ)) (b := (32463649930230942931 / 50000000000000000000 : ℝ)) (hi := (6316096157759 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_119 : (31388051552007 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 119 ∧ ex (72426 / 100000) 119 ≤ (31388051599163 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_119
  have hlo := exp_neg_ge_of (q := (3461327982304637 / 1000000000000000 : ℝ)) (a := (64877714862353302873 / 100000000000000000000 : ℝ)) (lo := (31388051552007 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (432665997600589 / 125000000000000 : ℝ)) (b := (2027428589829272897 / 3125000000000000000 : ℝ)) (hi := (31388051599163 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_121 : (31011435303991 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 121 ∧ ex (72426 / 100000) 121 ≤ (31011435350697 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_121
  have hlo := exp_neg_ge_of (q := (434174907717561 / 125000000000000 : ℝ)) (a := (12955978810829793973 / 20000000000000000000 : ℝ)) (lo := (31011435303991 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3473399260236923 / 1000000000000000 : ℝ)) (b := (3238994703317218227 / 5000000000000000000 : ℝ)) (hi := (31011435350697 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_122 : (30827125360973 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 122 ∧ ex (72426 / 100000) 122 ≤ (30827125407403 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_122
  have hlo := exp_neg_ge_of (q := (3479360283045101 / 1000000000000000 : ℝ)) (a := (64731642742003855253 / 100000000000000000000 : ℝ)) (lo := (30827125360973 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (108730008798173 / 31250000000000 : ℝ)) (b := (2589265710167624131 / 4000000000000000000 : ℝ)) (hi := (30827125407403 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_123 : (30645402053801 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 123 ∧ ex (72426 / 100000) 123 ≤ (30645402099959 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_123
  have hlo := exp_neg_ge_of (q := (3485272642408619 / 1000000000000000 : ℝ)) (a := (64683820823692789703 / 100000000000000000000 : ℝ)) (lo := (30645402053801 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (697054528181011 / 200000000000000 : ℝ)) (b := (2587352833434838727 / 4000000000000000000 : ℝ)) (hi := (30645402099959 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_124 : (30466208490927 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 124 ∧ ex (72426 / 100000) 124 ≤ (30466208536817 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_124
  have hlo := exp_neg_ge_of (q := (218196070493231 / 62500000000000 : ℝ)) (a := (32318210516625061531 / 50000000000000000000 : ℝ)) (lo := (30466208490927 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (872784281597033 / 250000000000000 : ℝ)) (b := (32318210522709911947 / 50000000000000000000 : ℝ)) (hi := (30466208536817 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_126 : (15057595726381 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 126 ∧ ex (72426 / 100000) 126 ≤ (30115191498127 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_126
  have hlo := exp_neg_ge_of (q := (350272553511527 / 100000000000000 : ℝ)) (a := (6454285966775851827 / 10000000000000000000 : ℝ)) (lo := (15057595726381 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (700545106722341 / 200000000000000 : ℝ)) (b := (64542859679911518039 / 100000000000000000000 : ℝ)) (hi := (30115191498127 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_127 : (5988652485409 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 127 ∧ ex (72426 / 100000) 127 ≤ (29943262472153 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_127
  have hlo := exp_neg_ge_of (q := (3508450940425091 / 1000000000000000 : ℝ)) (a := (32248342219520545731 / 50000000000000000000 : ℝ)) (lo := (5988652485409 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3508450938921527 / 1000000000000000 : ℝ)) (b := (64496684451185849099 / 100000000000000000000 : ℝ)) (hi := (29943262472153 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_128 : (29773651925857 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 128 ∧ ex (72426 / 100000) 128 ≤ (29773651970711 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_128
  have hlo := exp_neg_ge_of (q := (1757065720066507 / 500000000000000 : ℝ)) (a := (64450904019803034227 / 100000000000000000000 : ℝ)) (lo := (29773651925857 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (70282628772589 / 20000000000000 : ℝ)) (b := (64450904031939636473 / 100000000000000000000 : ℝ)) (hi := (29773651970711 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_129 : (29606310933273 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 129 ∧ ex (72426 / 100000) 129 ≤ (7401577744469 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_129
  have hlo := exp_neg_ge_of (q := (3519767733169577 / 1000000000000000 : ℝ)) (a := (64405511989163462927 / 100000000000000000000 : ℝ)) (lo := (29606310933273 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (879941932916503 / 250000000000000 : ℝ)) (b := (16101378000322998823 / 25000000000000000000 : ℝ)) (hi := (7401577744469 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_131 : (7319562097011 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 131 ∧ ex (72426 / 100000) 131 ≤ (29278248432157 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_131
  have hlo := exp_neg_ge_of (q := (1765455207244129 / 500000000000000 : ℝ)) (a := (12863173634255623051 / 20000000000000000000 : ℝ)) (lo := (7319562097011 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1765455206492347 / 500000000000000 : ℝ)) (b := (2009870880730959731 / 3125000000000000000 : ℝ)) (hi := (29278248432157 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_132 : (14558717815669 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 132 ∧ ex (72426 / 100000) 132 ≤ (29117435675211 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_132
  have hlo := exp_neg_ge_of (q := (3536418121638997 / 1000000000000000 : ℝ)) (a := (64271604289178144981 / 100000000000000000000 : ℝ)) (lo := (14558717815669 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3536418120135433 / 1000000000000000 : ℝ)) (b := (64271604301282888591 / 100000000000000000000 : ℝ)) (hi := (29117435675211 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_133 : (14479354940057 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 133 ∧ ex (72426 / 100000) 133 ≤ (28958709923749 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_133
  have hlo := exp_neg_ge_of (q := (3541884260792479 / 1000000000000000 : ℝ)) (a := (64227704596916976197 / 100000000000000000000 : ℝ)) (lo := (14479354940057 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (708376851857783 / 200000000000000 : ℝ)) (b := (64227704609013940179 / 100000000000000000000 : ℝ)) (hi := (28958709923749 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_134 : (28802028661023 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 134 ∧ ex (72426 / 100000) 134 ≤ (28802028704423 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_134
  have hlo := exp_neg_ge_of (q := (3547309454699039 / 1000000000000000 : ℝ)) (a := (12836832678670150629 / 20000000000000000000 : ℝ)) (lo := (28802028661023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (141892378127819 / 40000000000000 : ℝ)) (b := (1604604085136000233 / 2500000000000000000 : ℝ)) (hi := (28802028704423 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_136 : (5698927149933 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 136 ∧ ex (72426 / 100000) 136 ≤ (14247317896303 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_136
  have hlo := exp_neg_ge_of (q := (711607885745957 / 200000000000000 : ℝ)) (a := (64098134298569172471 / 100000000000000000000 : ℝ)) (lo := (5698927149933 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3558039427226221 / 1000000000000000 : ℝ)) (b := (64098134310643224323 / 100000000000000000000 : ℝ)) (hi := (14247317896303 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_137 : (14171922406937 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 137 ∧ ex (72426 / 100000) 137 ≤ (28343844856589 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_137
  have hlo := exp_neg_ge_of (q := (356334538652687 / 100000000000000 : ℝ)) (a := (12811127128839649271 / 20000000000000000000 : ℝ)) (lo := (14171922406937 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (712669077004661 / 200000000000000 : ℝ)) (b := (12811127131252961533 / 20000000000000000000 : ℝ)) (hi := (28343844856589 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_138 : (28194939846627 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 138 ∧ ex (72426 / 100000) 138 ≤ (176218374307 / 6250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_138
  have hlo := exp_neg_ge_of (q := (3568612755198549 / 1000000000000000 : ℝ)) (a := (4000842121546390969 / 6250000000000000000 : ℝ)) (lo := (28194939846627 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (713722550738997 / 200000000000000 : ℝ)) (b := (2000421061150043063 / 3125000000000000000 : ℝ)) (hi := (176218374307 / 6250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_139 : (3505985480997 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 139 ∧ ex (72426 / 100000) 139 ≤ (28047883890249 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_139
  have hlo := exp_neg_ge_of (q := (3573842091995827 / 1000000000000000 : ℝ)) (a := (31985822057885038943 / 50000000000000000000 : ℝ)) (lo := (3505985480997 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1786921045246131 / 500000000000000 : ℝ)) (b := (15992911031955461101 / 25000000000000000000 : ℝ)) (hi := (28047883890249 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_141 : (346989695623 / 12500000000000 : ℝ) ≤ ex (72426 / 100000) 141 ∧ ex (72426 / 100000) 141 ≤ (13879587845841 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_141
  have hlo := exp_neg_ge_of (q := (896047209847971 / 250000000000000 : ℝ)) (a := (6388896029131307747 / 10000000000000000000 : ℝ)) (lo := (346989695623 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (11200590118401 / 3125000000000 : ℝ)) (b := (1996530009479697021 / 3125000000000000000 : ℝ)) (hi := (13879587845841 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_142 : (3452181780729 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 142 ∧ ex (72426 / 100000) 142 ≤ (13808727143731 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_142
  have hlo := exp_neg_ge_of (q := (3589307305924881 / 1000000000000000 : ℝ)) (a := (31924048338505904341 / 50000000000000000000 : ℝ)) (lo := (3452181780729 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3589307304421317 / 1000000000000000 : ℝ)) (b := (63848096689041866739 / 100000000000000000000 : ℝ)) (hi := (13808727143731 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_143 : (13738721669613 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 143 ∧ ex (72426 / 100000) 143 ≤ (27477443380647 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_143
  have hlo := exp_neg_ge_of (q := (3594389853098633 / 1000000000000000 : ℝ)) (a := (7975943211169387597 / 12500000000000000000 : ℝ)) (lo := (13738721669613 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (898597462898767 / 250000000000000 : ℝ)) (b := (63807545701378060827 / 100000000000000000000 : ℝ)) (hi := (27477443380647 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_144 : (6834777634719 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 144 ∧ ex (72426 / 100000) 144 ≤ (2733911058009 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_144
  have hlo := exp_neg_ge_of (q := (1799718490768753 / 500000000000000 : ℝ)) (a := (6376730277532870473 / 10000000000000000000 : ℝ)) (lo := (6834777634719 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1799718490016971 / 500000000000000 : ℝ)) (b := (63767302787344613129 / 100000000000000000000 : ℝ)) (hi := (2733911058009 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_146 : (1691709614321 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 146 ∧ ex (72426 / 100000) 146 ≤ (3383419233743 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_146
  have hlo := exp_neg_ge_of (q := (225589183314067 / 62500000000000 : ℝ)) (a := (12737544688024515091 / 20000000000000000000 : ℝ)) (lo := (1691709614321 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3609426931521507 / 1000000000000000 : ℝ)) (b := (7960965431515573503 / 12500000000000000000 : ℝ)) (hi := (3383419233743 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_147 : (26933869194361 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 147 ∧ ex (72426 / 100000) 147 ≤ (2693386923497 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_147
  have hlo := exp_neg_ge_of (q := (45179633831087 / 12500000000000 : ℝ)) (a := (63648378388814037831 / 100000000000000000000 : ℝ)) (lo := (26933869194361 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (722874140996679 / 200000000000000 : ℝ)) (b := (7956047300101148581 / 12500000000000000000 : ℝ)) (hi := (2693386923497 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_148 : (26801941164237 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 148 ∧ ex (72426 / 100000) 148 ≤ (26801941204649 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_148
  have hlo := exp_neg_ge_of (q := (361928096258299 / 100000000000000 : ℝ)) (a := (15902331036421820153 / 25000000000000000000 : ℝ)) (lo := (26801941164237 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1809640480539713 / 500000000000000 : ℝ)) (b := (63609324157675620767 / 100000000000000000000 : ℝ)) (hi := (26801941204649 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_149 : (333394265649 / 12500000000000 : ℝ) ≤ ex (72426 / 100000) 149 ∧ ex (72426 / 100000) 149 ≤ (26671541292137 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_149
  have hlo := exp_neg_ge_of (q := (72483163054613 / 20000000000000 : ℝ)) (a := (63570556618047390697 / 100000000000000000000 : ℝ)) (lo := (333394265649 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1812079075613543 / 500000000000000 : ℝ)) (b := (15892639157507246603 / 25000000000000000000 : ℝ)) (hi := (26671541292137 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_151 : (26415215350843 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 151 ∧ ex (72426 / 100000) 151 ≤ (26415215390677 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_151
  have hlo := exp_neg_ge_of (q := (3633815095798169 / 1000000000000000 : ℝ)) (a := (3968366609941158519 / 6250000000000000000 : ℝ)) (lo := (26415215350843 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (726763018858921 / 200000000000000 : ℝ)) (b := (63493865771026814921 / 100000000000000000000 : ℝ)) (hi := (26415215390677 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_152 : (13144617920119 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 152 ∧ ex (72426 / 100000) 152 ≤ (6572308969971 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_152
  have hlo := exp_neg_ge_of (q := (909648926803679 / 250000000000000 : ℝ)) (a := (63455934656112180541 / 100000000000000000000 : ℝ)) (lo := (13144617920119 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (227412231606947 / 62500000000000 : ℝ)) (b := (15863983667018471257 / 25000000000000000000 : ℝ)) (hi := (6572308969971 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_153 : (26164677361881 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 153 ∧ ex (72426 / 100000) 153 ≤ (26164677401341 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_153
  have hlo := exp_neg_ge_of (q := (3643344970134277 / 1000000000000000 : ℝ)) (a := (15854568680272484197 / 25000000000000000000 : ℝ)) (lo := (26164677361881 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3643344968630713 / 1000000000000000 : ℝ)) (b := (63418274733045122469 / 100000000000000000000 : ℝ)) (hi := (26164677401341 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_154 : (13020757377547 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 154 ∧ ex (72426 / 100000) 154 ≤ (26041514794371 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_154
  have hlo := exp_neg_ge_of (q := (3648063293010687 / 1000000000000000 : ℝ)) (a := (63380882261979386491 / 100000000000000000000 : ℝ)) (lo := (13020757377547 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3648063291507123 / 1000000000000000 : ℝ)) (b := (63380882273928107991 / 100000000000000000000 : ℝ)) (hi := (26041514794371 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_156 : (41278847233 / 1600000000000 : ℝ) ≤ ex (72426 / 100000) 156 ∧ ex (72426 / 100000) 156 ≤ (1289963977977 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_156
  have hlo := exp_neg_ge_of (q := (1828704356498571 / 500000000000000 : ℝ)) (a := (63306885370663594767 / 100000000000000000000 : ℝ)) (lo := (41278847233 / 1600000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3657408711493577 / 1000000000000000 : ℝ)) (b := (7913360672824944621 / 12500000000000000000 : ℝ)) (hi := (1289963977977 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_157 : (12840079762169 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 157 ∧ ex (72426 / 100000) 157 ≤ (1027206382523 / 40000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_157
  have hlo := exp_neg_ge_of (q := (1831018294084079 / 500000000000000 : ℝ)) (a := (12654054783178302897 / 20000000000000000000 : ℝ)) (lo := (12840079762169 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3662036586664593 / 1000000000000000 : ℝ)) (b := (63270273927821172319 / 100000000000000000000 : ℝ)) (hi := (1027206382523 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_158 : (2556234062771 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 158 ∧ ex (72426 / 100000) 158 ≤ (25562340666271 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_158
  have hlo := exp_neg_ge_of (q := (3666635079806703 / 1000000000000000 : ℝ)) (a := (63233915888201088031 / 100000000000000000000 : ℝ)) (lo := (2556234062771 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3666635078303139 / 1000000000000000 : ℝ)) (b := (63233915900124485557 / 100000000000000000000 : ℝ)) (hi := (25562340666271 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_159 : (25445800518653 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 159 ∧ ex (72426 / 100000) 159 ≤ (318072506963 / 12500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_159
  have hlo := exp_neg_ge_of (q := (3671204558686617 / 1000000000000000 : ℝ)) (a := (3949862996621500149 / 6250000000000000000 : ℝ)) (lo := (25445800518653 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (917801139295763 / 250000000000000 : ℝ)) (b := (31598903978930603371 / 50000000000000000000 : ℝ)) (hi := (318072506963 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_161 : (5043293999727 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 161 ∧ ex (72426 / 100000) 161 ≤ (630411750917 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_161
  have hlo := exp_neg_ge_of (q := (3680257926570239 / 1000000000000000 : ℝ)) (a := (31563164636572340961 / 50000000000000000000 : ℝ)) (lo := (5043293999727 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (147210317002667 / 40000000000000 : ℝ)) (b := (63126329285049627763 / 100000000000000000000 : ℝ)) (hi := (630411750917 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_162 : (12551818750987 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 162 ∧ ex (72426 / 100000) 162 ≤ (25103637539851 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_162
  have hlo := exp_neg_ge_of (q := (3684742522941999 / 1000000000000000 : ℝ)) (a := (6309095217641788231 / 10000000000000000000 : ℝ)) (lo := (12551818750987 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1842371260719217 / 500000000000000 : ℝ)) (b := (63090952188316785281 / 100000000000000000000 : ℝ)) (hi := (25103637539851 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_163 : (12495999796277 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 163 ∧ ex (72426 / 100000) 163 ≤ (3123999953783 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_163
  have hlo := exp_neg_ge_of (q := (1844599760811449 / 500000000000000 : ℝ)) (a := (63055812429610657993 / 100000000000000000000 : ℝ)) (lo := (12495999796277 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3689199520119333 / 1000000000000000 : ℝ)) (b := (63055812441503559119 / 100000000000000000000 : ℝ)) (hi := (3123999953783 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_164 : (6220384102479 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 164 ∧ ex (72426 / 100000) 164 ≤ (12440768223731 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_164
  have hlo := exp_neg_ge_of (q := (1846814630101273 / 500000000000000 : ℝ)) (a := (3151045349937447557 / 5000000000000000000 : ℝ)) (lo := (6220384102479 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1846814629349491 / 500000000000000 : ℝ)) (b := (63020907010635890883 / 100000000000000000000 : ℝ)) (hi := (12440768223731 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_166 : (24664057013647 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 166 ∧ ex (72426 / 100000) 166 ≤ (24664057050869 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_166
  have hlo := exp_neg_ge_of (q := (1851204138390851 / 500000000000000 : ℝ)) (a := (15737946808121391659 / 25000000000000000000 : ℝ)) (lo := (24664057013647 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1851204137639069 / 500000000000000 : ℝ)) (b := (62951787244360742147 / 100000000000000000000 : ℝ)) (hi := (24664057050869 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_167 : (3069625408961 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 167 ∧ ex (72426 / 100000) 167 ≤ (24557003308751 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_167
  have hlo := exp_neg_ge_of (q := (3706758199767551 / 1000000000000000 : ℝ)) (a := (15729391777118552569 / 25000000000000000000 : ℝ)) (lo := (3069625408961 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3706758198263987 / 1000000000000000 : ℝ)) (b := (31458783560171786979 / 50000000000000000000 : ℝ)) (hi := (24557003308751 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_168 : (4890209835119 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 168 ∧ ex (72426 / 100000) 168 ≤ (1956083937 / 80000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_168
  have hlo := exp_neg_ge_of (q := (927770538227299 / 250000000000000 : ℝ)) (a := (62883569720500362609 / 100000000000000000000 : ℝ)) (lo := (4890209835119 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (57985658615713 / 15625000000000 : ℝ)) (b := (15720892433090990151 / 25000000000000000000 : ℝ)) (hi := (1956083937 / 80000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_169 : (608654424617 / 25000000000000 : ℝ) ≤ ex (72426 / 100000) 169 ∧ ex (72426 / 100000) 169 ≤ (24346177021429 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_169
  have hlo := exp_neg_ge_of (q := (3715380444456777 / 1000000000000000 : ℝ)) (a := (62849792305859381407 / 100000000000000000000 : ℝ)) (lo := (608654424617 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3715380442953213 / 1000000000000000 : ℝ)) (b := (62849792317717259331 / 100000000000000000000 : ℝ)) (hi := (24346177021429 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_171 : (24139609289727 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 171 ∧ ex (72426 / 100000) 171 ≤ (3017451165771 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_171
  have hlo := exp_neg_ge_of (q := (3723901248619209 / 1000000000000000 : ℝ)) (a := (7847860824543776209 / 12500000000000000000 : ℝ)) (lo := (24139609289727 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (930975311778911 / 250000000000000 : ℝ)) (b := (627828866081967901 / 1000000000000000000 : ℝ)) (hi := (3017451165771 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_172 : (48075760413 / 2000000000000 : ℝ) ≤ ex (72426 / 100000) 172 ∧ ex (72426 / 100000) 172 ≤ (24037880242789 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_172
  have hlo := exp_neg_ge_of (q := (233007771935219 / 62500000000000 : ℝ)) (a := (62749753023077616329 / 100000000000000000000 : ℝ)) (lo := (48075760413 / 2000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3728124349459939 / 1000000000000000 : ℝ)) (b := (62749753034918610477 / 100000000000000000000 : ℝ)) (hi := (24037880242789 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_173 : (23937165849623 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 173 ∧ ex (72426 / 100000) 173 ≤ (11968582942881 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_173
  have hlo := exp_neg_ge_of (q := (3732322971417553 / 1000000000000000 : ℝ)) (a := (7839603608002442457 / 12500000000000000000 : ℝ)) (lo := (23937165849623 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3732322969913989 / 1000000000000000 : ℝ)) (b := (31358414437927491647 / 50000000000000000000 : ℝ)) (hi := (11968582942881 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_174 : (23837450319221 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 174 ∧ ex (72426 / 100000) 174 ≤ (5959362588803 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_174
  have hlo := exp_neg_ge_of (q := (3736497392195707 / 1000000000000000 : ℝ)) (a := (15671027899136271771 / 25000000000000000000 : ℝ)) (lo := (23837450319221 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1868248695346071 / 500000000000000 : ℝ)) (b := (31342055804187519511 / 50000000000000000000 : ℝ)) (hi := (5959362588803 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_176 : (11820476911223 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 176 ∧ ex (72426 / 100000) 176 ≤ (738779808067 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_176
  have hlo := exp_neg_ge_of (q := (936193684858231 / 250000000000000 : ℝ)) (a := (62619287868116031549 / 100000000000000000000 : ℝ)) (lo := (11820476911223 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3744774737929359 / 1000000000000000 : ℝ)) (b := (782741098499188899 / 1250000000000000000 : ℝ)) (hi := (738779808067 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_177 : (2943017839179 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 177 ∧ ex (72426 / 100000) 177 ≤ (4708828549797 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_177
  have hlo := exp_neg_ge_of (q := (1874439103250257 / 500000000000000 : ℝ)) (a := (31293588290549813837 / 50000000000000000000 : ℝ)) (lo := (2943017839179 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3748878204996949 / 1000000000000000 : ℝ)) (b := (625871765929133351 / 1000000000000000000 : ℝ)) (hi := (4708828549797 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_178 : (732758441509 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 178 ∧ ex (72426 / 100000) 178 ≤ (23448270163699 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_178
  have hlo := exp_neg_ge_of (q := (1876479277660569 / 500000000000000 : ℝ)) (a := (31277631265775311033 / 50000000000000000000 : ℝ)) (lo := (732758441509 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3752958553817573 / 1000000000000000 : ℝ)) (b := (781940781791987473 / 1250000000000000000 : ℝ)) (hi := (23448270163699 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_179 : (23353321772263 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 179 ∧ ex (72426 / 100000) 179 ≤ (23353321807533 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_179
  have hlo := exp_neg_ge_of (q := (3757016044924817 / 1000000000000000 : ℝ)) (a := (62523543410058119313 / 100000000000000000000 : ℝ)) (lo := (23353321772263 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3757016043421253 / 1000000000000000 : ℝ)) (b := (7815442927732649559 / 12500000000000000000 : ℝ)) (hi := (23353321807533 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_181 : (23166142040779 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 181 ∧ ex (72426 / 100000) 181 ≤ (23166142075771 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_181
  have hlo := exp_neg_ge_of (q := (3765063461051179 / 1000000000000000 : ℝ)) (a := (31230340455730499651 / 50000000000000000000 : ℝ)) (lo := (23166142040779 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (753012691909523 / 200000000000000 : ℝ)) (b := (15615170230813403927 / 25000000000000000000 : ℝ)) (hi := (23166142075771 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_182 : (23073883525087 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 182 ∧ ex (72426 / 100000) 182 ≤ (23073883559941 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_182
  have hlo := exp_neg_ge_of (q := (58891466943263 / 15625000000000 : ℝ)) (a := (624295331107198389 / 1000000000000000000 : ℝ)) (lo := (23073883525087 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3769053882865267 / 1000000000000000 : ℝ)) (b := (62429533122507292309 / 100000000000000000000 : ℝ)) (hi := (23073883559941 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_183 : (22982494943303 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 183 ∧ ex (72426 / 100000) 183 ≤ (22982494978021 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_183
  have hlo := exp_neg_ge_of (q := (11790695132011 / 3125000000000 : ℝ)) (a := (15599642847258917337 / 25000000000000000000 : ℝ)) (lo := (22982494943303 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (754604488147991 / 200000000000000 : ℝ)) (b := (62398571400817991119 / 100000000000000000000 : ℝ)) (hi := (22982494978021 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_184 : (22891963405703 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 184 ∧ ex (72426 / 100000) 184 ≤ (22891963440287 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_184
  have hlo := exp_neg_ge_of (q := (944242343248119 / 250000000000000 : ℝ)) (a := (31183896813500981817 / 50000000000000000000 : ℝ)) (lo := (22891963405703 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (236060585718057 / 62500000000000 : ℝ)) (b := (12473558727755836947 / 20000000000000000000 : ℝ)) (hi := (22891963440287 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_186 : (11356710597977 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 186 ∧ ex (72426 / 100000) 186 ≤ (354897206723 / 15625000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_186
  have hlo := exp_neg_ge_of (q := (756959857418023 / 200000000000000 : ℝ)) (a := (31153390840472362411 / 50000000000000000000 : ℝ)) (lo := (11356710597977 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3784799285586551 / 1000000000000000 : ℝ)) (b := (31153390846355937443 / 50000000000000000000 : ℝ)) (hi := (354897206723 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_187 : (452507720331 / 20000000000000 : ℝ) ≤ ex (72426 / 100000) 187 ∧ ex (72426 / 100000) 187 ≤ (22625386050737 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_187
  have hlo := exp_neg_ge_of (q := (757736545605939 / 200000000000000 : ℝ)) (a := (1556913585811672913 / 2500000000000000000 : ℝ)) (lo := (452507720331 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3788682726526131 / 1000000000000000 : ℝ)) (b := (62276543444229087643 / 100000000000000000000 : ℝ)) (hi := (22625386050737 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_188 : (22538158854223 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 188 ∧ ex (72426 / 100000) 188 ≤ (563453972207 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_188
  have hlo := exp_neg_ge_of (q := (3792545457185811 / 1000000000000000 : ℝ)) (a := (62246481013229389483 / 100000000000000000000 : ℝ)) (lo := (22538158854223 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3792545455682247 / 1000000000000000 : ℝ)) (b := (15561620256246654719 / 25000000000000000000 : ℝ)) (hi := (563453972207 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_189 : (11225864026811 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 189 ∧ ex (72426 / 100000) 189 ≤ (22451728087551 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_189
  have hlo := exp_neg_ge_of (q := (3796387694313689 / 1000000000000000 : ℝ)) (a := (62216592473678143823 / 100000000000000000000 : ℝ)) (lo := (11225864026811 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (949096923202531 / 250000000000000 : ℝ)) (b := (62216592485430476103 / 100000000000000000000 : ℝ)) (hi := (22451728087551 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_191 : (2785151256711 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 191 ∧ ex (72426 / 100000) 191 ≤ (5570302521841 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_191
  have hlo := exp_neg_ge_of (q := (951002888545911 / 250000000000000 : ℝ)) (a := (15539332348418687673 / 25000000000000000000 : ℝ)) (lo := (2785151256711 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (47550144408501 / 12500000000000 : ℝ)) (b := (7769666175677171809 / 12500000000000000000 : ℝ)) (hi := (5570302521841 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_192 : (22197100664327 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 192 ∧ ex (72426 / 100000) 192 ≤ (11098550348939 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_192
  have hlo := exp_neg_ge_of (q := (3807793599331433 / 1000000000000000 : ℝ)) (a := (62127951110341716473 / 100000000000000000000 : ℝ)) (lo := (22197100664327 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3807793597827869 / 1000000000000000 : ℝ)) (b := (31063975561039771853 / 50000000000000000000 : ℝ)) (hi := (11098550348939 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_193 : (11056871622911 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 193 ∧ ex (72426 / 100000) 193 ≤ (1382108954953 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_193
  have hlo := exp_neg_ge_of (q := (762311199480569 / 200000000000000 : ℝ)) (a := (12419747843924443961 / 20000000000000000000 : ℝ)) (lo := (11056871622911 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (47644449948741 / 12500000000000 : ℝ)) (b := (62098739231355293663 / 100000000000000000000 : ℝ)) (hi := (1382108954953 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_194 : (5507781807757 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 194 ∧ ex (72426 / 100000) 194 ≤ (5507781816083 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_194
  have hlo := exp_neg_ge_of (q := (1907649475734899 / 500000000000000 : ℝ)) (a := (1939677872632978231 / 3125000000000000000 : ℝ)) (lo := (5507781807757 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1907649474983117 / 500000000000000 : ℝ)) (b := (31034845967991821707 / 50000000000000000000 : ℝ)) (hi := (5507781816083 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_196 : (21868078148951 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 196 ∧ ex (72426 / 100000) 196 ≤ (21868078182013 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_196
  have hlo := exp_neg_ge_of (q := (3822727324280887 / 1000000000000000 : ℝ)) (a := (62012084072695008949 / 100000000000000000000 : ℝ)) (lo := (21868078148951 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1911363661388661 / 500000000000000 : ℝ)) (b := (7751510510551751053 / 12500000000000000000 : ℝ)) (hi := (21868078182013 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_197 : (21787624937851 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 197 ∧ ex (72426 / 100000) 197 ≤ (21787624970793 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_197
  have hlo := exp_neg_ge_of (q := (59787705215037 / 15625000000000 : ℝ)) (a := (6198352006236311231 / 10000000000000000000 : ℝ)) (lo := (21787624937851 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3826413132258803 / 1000000000000000 : ℝ)) (b := (12396704014815497779 / 20000000000000000000 : ℝ)) (hi := (21787624970793 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_198 : (21707872833509 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 198 ∧ ex (72426 / 100000) 198 ≤ (21707872866333 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_198
  have hlo := exp_neg_ge_of (q := (478760035104677 / 125000000000000 : ℝ)) (a := (61955113737958138549 / 100000000000000000000 : ℝ)) (lo := (21707872833509 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (957520069833463 / 250000000000000 : ℝ)) (b := (30977556874833959121 / 50000000000000000000 : ℝ)) (hi := (21707872866333 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_199 : (865152489251 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 199 ∧ ex (72426 / 100000) 199 ≤ (10814406131991 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_199
  have hlo := exp_neg_ge_of (q := (3833728953541553 / 1000000000000000 : ℝ)) (a := (61926863439155809277 / 100000000000000000000 : ℝ)) (lo := (865152489251 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (958432238009497 / 250000000000000 : ℝ)) (b := (61926863450861040991 / 100000000000000000000 : ℝ)) (hi := (10814406131991 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_201 : (10736364002597 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 201 ∧ ex (72426 / 100000) 201 ≤ (21472728037669 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_201
  have hlo := exp_neg_ge_of (q := (1920485806948729 / 500000000000000 : ℝ)) (a := (1546770610127825259 / 2500000000000000000 : ℝ)) (lo := (10736364002597 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1920485806196947 / 500000000000000 : ℝ)) (b := (15467706104202305481 / 25000000000000000000 : ℝ)) (hi := (21472728037669 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_202 : (21395686050201 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 202 ∧ ex (72426 / 100000) 202 ≤ (10697843041281 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_202
  have hlo := exp_neg_ge_of (q := (3844565963706389 / 1000000000000000 : ℝ)) (a := (15460758118928667183 / 25000000000000000000 : ℝ)) (lo := (21395686050201 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (480570745275353 / 125000000000000 : ℝ)) (b := (61843032487406430723 / 100000000000000000000 : ℝ)) (hi := (10697843041281 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_203 : (10659649463481 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 203 ∧ ex (72426 / 100000) 203 ≤ (2131929895921 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_203
  have hlo := exp_neg_ge_of (q := (3848142563567397 / 1000000000000000 : ℝ)) (a := (61815390182593571261 / 100000000000000000000 : ℝ)) (lo := (10659649463481 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (481017820257979 / 125000000000000 : ℝ)) (b := (30907695097140454073 / 50000000000000000000 : ℝ)) (hi := (2131929895921 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_204 : (1062177894239 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 204 ∧ ex (72426 / 100000) 204 ≤ (4248711583383 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_204
  have hlo := exp_neg_ge_of (q := (962925396982051 / 250000000000000 : ℝ)) (a := (61787895988886268141 / 100000000000000000000 : ℝ)) (lo := (1062177894239 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (12036567457577 / 3125000000000 : ℝ)) (b := (30893948000284602051 / 50000000000000000000 : ℝ)) (hi := (4248711583383 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_206 : (21093979832559 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 206 ∧ ex (72426 / 100000) 206 ≤ (2636747483059 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_206
  have hlo := exp_neg_ge_of (q := (1929383797597067 / 500000000000000 : ℝ)) (a := (15433336466975636731 / 25000000000000000000 : ℝ)) (lo := (21093979832559 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (385876759369057 / 100000000000000 : ℝ)) (b := (15433336469894197763 / 25000000000000000000 : ℝ)) (hi := (2636747483059 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_207 : (21020126102037 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 207 ∧ ex (72426 / 100000) 207 ≤ (21020126133841 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_207
  have hlo := exp_neg_ge_of (q := (482784364299621 / 125000000000000 : ℝ)) (a := (30853143490583770097 / 50000000000000000000 : ℝ)) (lo := (21020126102037 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (965568728223351 / 250000000000000 : ℝ)) (b := (61706286992837485117 / 100000000000000000000 : ℝ)) (hi := (21020126133841 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_208 : (5236721251151 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 208 ∧ ex (72426 / 100000) 208 ≤ (20946885036299 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_208
  have hlo := exp_neg_ge_of (q := (3865765330791069 / 1000000000000000 : ℝ)) (a := (61679370274038720591 / 100000000000000000000 : ℝ)) (lo := (5236721251151 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (241610333080469 / 62500000000000 : ℝ)) (b := (61679370285704404789 / 100000000000000000000 : ℝ)) (hi := (20946885036299 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_209 : (20874248549461 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 209 ∧ ex (72426 / 100000) 209 ≤ (20874248581049 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_209
  have hlo := exp_neg_ge_of (q := (1934619503257313 / 500000000000000 : ℝ)) (a := (61652594321249053071 / 100000000000000000000 : ℝ)) (lo := (20874248549461 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1934619502505531 / 500000000000000 : ℝ)) (b := (61652594332910491621 / 100000000000000000000 : ℝ)) (hi := (20874248581049 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

end PsiOmega.Locate.Z4

#print axioms PsiOmega.Locate.Z4.exB_209
