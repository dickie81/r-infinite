import DHLocate3Base

/-! # Generated (`gen_locate_zero.py 3`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 57436 / 100000`, `n ∈ NS`

`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` with `exp(-(y/8))` from `Real.exp_bound`
(`exp_neg_ge_of`, `exp_neg_le_of`, `DHLocateExp`). -/

open Real Finset

namespace PsiOmega.Locate.Z3

theorem exB_2 : (335792054762491 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 2 ∧ ex (57436 / 100000) 2 ≤ (67158410960213 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_2
  have hlo := exp_neg_ge_of (q := (398116014682577 / 1000000000000000 : ℝ)) (a := (11893168295796774377 / 12500000000000000000 : ℝ)) (lo := (335792054762491 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (49764501820963 / 125000000000000 : ℝ)) (b := (95145346367740398939 / 100000000000000000000 : ℝ)) (hi := (67158410960213 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_3 : (133015007958663 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 3 ∧ ex (57436 / 100000) 3 ≤ (266030015958317 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_3
  have hlo := exp_neg_ge_of (q := (63099895421219 / 100000000000000 : ℝ)) (a := (46207777873191216383 / 50000000000000000000 : ℝ)) (lo := (133015007958663 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (157749738514527 / 250000000000000 : ℝ)) (b := (46207777874081189737 / 50000000000000000000 : ℝ)) (hi := (266030015958317 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_4 : (90205043234049 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 4 ∧ ex (57436 / 100000) 4 ≤ (1127563040613 / 2500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_4
  have hlo := exp_neg_ge_of (q := (79623202935677 / 100000000000000 : ℝ)) (a := (90526369351868023983 / 100000000000000000000 : ℝ)) (lo := (90205043234049 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (99529003648823 / 125000000000000 : ℝ)) (b := (90526369353748550887 / 100000000000000000000 : ℝ)) (hi := (1127563040613 / 2500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_6 : (11166345709257 / 31250000000000 : ℝ) ≤ ex (57436 / 100000) 6 ∧ ex (57436 / 100000) 6 ≤ (357323062770301 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_6
  have hlo := exp_neg_ge_of (q := (1029114968887167 / 1000000000000000 : ℝ)) (a := (87929100611388729211 / 100000000000000000000 : ℝ)) (lo := (11166345709257 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (514557484339929 / 500000000000000 : ℝ)) (b := (87929100613667290961 / 100000000000000000000 : ℝ)) (hi := (357323062770301 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_7 : (2616371903211 / 8000000000000 : ℝ) ≤ ex (57436 / 100000) 7 ∧ ex (57436 / 100000) 7 ≤ (163523243984693 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_7
  have hlo := exp_neg_ge_of (q := (1117652953353337 / 1000000000000000 : ℝ)) (a := (21740333146442355521 / 25000000000000000000 : ℝ)) (lo := (2616371903211 / 8000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (139706619143173 / 125000000000000 : ℝ)) (b := (4348066629401495293 / 5000000000000000000 : ℝ)) (hi := (163523243984693 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_8 : (151450684086217 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 8 ∧ ex (57436 / 100000) 8 ≤ (75725342061129 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_8
  have hlo := exp_neg_ge_of (q := (7464675275299 / 6250000000000 : ℝ)) (a := (86131627672646606331 / 100000000000000000000 : ℝ)) (lo := (151450684086217 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (74646752738117 / 62500000000000 : ℝ)) (b := (10766453459401084723 / 12500000000000000000 : ℝ)) (hi := (75725342061129 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_9 : (1769299234239 / 6250000000000 : ℝ) ≤ ex (57436 / 100000) 9 ∧ ex (57436 / 100000) 9 ≤ (141543938774179 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_9
  have hlo := exp_neg_ge_of (q := (1261997908416081 / 1000000000000000 : ℝ)) (a := (42703174719607894603 / 50000000000000000000 : ℝ)) (lo := (1769299234239 / 6250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1261997908168393 / 1000000000000000 : ℝ)) (b := (854063494418600553 / 1000000000000000000 : ℝ)) (hi := (141543938774179 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_11 : (252270052321569 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 11 ∧ ex (57436 / 100000) 11 ≤ (6306751309633 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_11
  have hlo := exp_neg_ge_of (q := (172156891133273 / 125000000000000 : ℝ)) (a := (84184708446387345697 / 100000000000000000000 : ℝ)) (lo := (252270052321569 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1377255128813477 / 1000000000000000 : ℝ)) (b := (16836941689809320829 / 20000000000000000000 : ℝ)) (hi := (6306751309633 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_12 : (239972490877237 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 12 ∧ ex (57436 / 100000) 12 ≤ (47994498187607 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_12
  have hlo := exp_neg_ge_of (q := (356807745888629 / 250000000000000 : ℝ)) (a := (2614388979178209487 / 3125000000000000000 : ℝ)) (lo := (239972490877237 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (142723098330117 / 100000000000000 : ℝ)) (b := (5228777958522005251 / 6250000000000000000 : ℝ)) (hi := (47994498187607 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_13 : (229189911068949 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 13 ∧ ex (57436 / 100000) 13 ≤ (229189911127083 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_13
  have hlo := exp_neg_ge_of (q := (368301078283539 / 250000000000000 : ℝ)) (a := (83181057435096172989 / 100000000000000000000 : ℝ)) (lo := (229189911068949 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1473204312880509 / 1000000000000000 : ℝ)) (b := (83181057437733501887 / 100000000000000000000 : ℝ)) (hi := (229189911127083 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_14 : (219639224353903 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 14 ∧ ex (57436 / 100000) 14 ≤ (13727451525603 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_14
  have hlo := exp_neg_ge_of (q := (757884484010251 / 500000000000000 : ℝ)) (a := (10342457636713042837 / 12500000000000000000 : ℝ)) (lo := (219639224353903 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (94735560485419 / 62500000000000 : ℝ)) (b := (82739661096329238729 / 100000000000000000000 : ℝ)) (hi := (13727451525603 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_16 : (50855936404811 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 16 ∧ ex (57436 / 100000) 16 ≤ (6356992052481 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_16
  have hlo := exp_neg_ge_of (q := (79623202936211 / 50000000000000 : ℝ)) (a := (20487558870049724393 / 25000000000000000000 : ℝ)) (lo := (50855936404811 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (796232029214273 / 500000000000000 : ℝ)) (b := (20487558870806929641 / 25000000000000000000 : ℝ)) (hi := (6356992052481 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_17 : (196462360324221 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 17 ∧ ex (57436 / 100000) 17 ≤ (196462360387611 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_17
  have hlo := exp_neg_ge_of (q := (203410552066729 / 125000000000000 : ℝ)) (a := (20398579637255657731 / 25000000000000000000 : ℝ)) (lo := (196462360324221 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (81364220810559 / 50000000000000 : ℝ)) (b := (40797159276156727227 / 50000000000000000000 : ℝ)) (hi := (196462360387611 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_18 : (95058660054527 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 18 ∧ ex (57436 / 100000) 18 ≤ (95058660086897 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_18
  have hlo := exp_neg_ge_of (q := (830056961561131 / 500000000000000 : ℝ)) (a := (81260166992577986801 / 100000000000000000000 : ℝ)) (lo := (95058660054527 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1660113922781741 / 1000000000000000 : ℝ)) (b := (81260166996036838851 / 100000000000000000000 : ℝ)) (hi := (95058660086897 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_19 : (92152068050273 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 19 ∧ ex (57436 / 100000) 19 ≤ (92152068082769 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_19
  have hlo := exp_neg_ge_of (q := (1691167972341437 / 1000000000000000 : ℝ)) (a := (40472673131685801807 / 50000000000000000000 : ℝ)) (lo := (92152068050273 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1691167971988807 / 1000000000000000 : ℝ)) (b := (809453462669395769 / 1000000000000000000 : ℝ)) (hi := (92152068082769 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_21 : (174008364756397 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 21 ∧ ex (57436 / 100000) 21 ≤ (174008364820243 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_21
  have hlo := exp_neg_ge_of (q := (54645372112827 / 31250000000000 : ℝ)) (a := (80365798793147342311 / 100000000000000000000 : ℝ)) (lo := (174008364756397 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (437162976810889 / 250000000000000 : ℝ)) (b := (40182899398416602253 / 50000000000000000000 : ℝ)) (hi := (174008364820243 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_22 : (2647196225633 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 22 ∧ ex (57436 / 100000) 22 ≤ (5294392453231 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_22
  have hlo := exp_neg_ge_of (q := (887685571897073 / 500000000000000 : ℝ)) (a := (80097832438383101569 / 100000000000000000000 : ℝ)) (lo := (2647196225633 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1775371143423009 / 1000000000000000 : ℝ)) (b := (80097832442099016679 / 100000000000000000000 : ℝ)) (hi := (5294392453231 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_23 : (165149780185227 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 23 ∧ ex (57436 / 100000) 23 ≤ (165149780247029 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_23
  have hlo := exp_neg_ge_of (q := (900451229073483 / 500000000000000 : ℝ)) (a := (39921307270327447293 / 50000000000000000000 : ℝ)) (lo := (165149780185227 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (900451228886377 / 500000000000000 : ℝ)) (b := (79842614544389660307 / 100000000000000000000 : ℝ)) (hi := (165149780247029 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_24 : (1007260697427 / 6250000000000 : ℝ) ≤ ex (57436 / 100000) 24 ∧ ex (57436 / 100000) 24 ≤ (40290427912249 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_24
  have hlo := exp_neg_ge_of (q := (182534699828649 / 100000000000000 : ℝ)) (a := (79599022386818000129 / 100000000000000000000 : ℝ)) (lo := (1007260697427 / 6250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1825346997910009 / 1000000000000000 : ℝ)) (b := (79599022390563949079 / 100000000000000000000 : ℝ)) (hi := (40290427912249 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_26 : (30784060465879 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 26 ∧ ex (57436 / 100000) 26 ≤ (76960151193901 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_26
  have hlo := exp_neg_ge_of (q := (1871320327868413 / 1000000000000000 : ℝ)) (a := (79142905207323634693 / 100000000000000000000 : ℝ)) (lo := (30784060465879 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1871320327488957 / 1000000000000000 : ℝ)) (b := (9892863151384694139 / 12500000000000000000 : ℝ)) (hi := (76960151193901 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_27 : (75309872549941 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 27 ∧ ex (57436 / 100000) 27 ≤ (2353433518081 / 15625000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_27
  have hlo := exp_neg_ge_of (q := (1892996862649479 / 1000000000000000 : ℝ)) (a := (7892875247673939461 / 10000000000000000000 : ℝ)) (lo := (75309872549941 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (378599372453809 / 200000000000000 : ℝ)) (b := (2466523515015400193 / 3125000000000000000 : ℝ)) (hi := (2353433518081 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_28 : (147506212896651 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 28 ∧ ex (57436 / 100000) 28 ≤ (1843827661911 / 12500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_28
  have hlo := exp_neg_ge_of (q := (191388498275611 / 100000000000000 : ℝ)) (a := (39361468564723644791 / 50000000000000000000 : ℝ)) (lo := (147506212896651 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1913884982374921 / 1000000000000000 : ℝ)) (b := (78722937133198345193 / 100000000000000000000 : ℝ)) (hi := (1843827661911 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_29 : (564699132397 / 3906250000000 : ℝ) ≤ ex (57436 / 100000) 29 ∧ ex (57436 / 100000) 29 ≤ (18070372243603 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_29
  have hlo := exp_neg_ge_of (q := (386808006640683 / 200000000000000 : ℝ)) (a := (78524853661963572167 / 100000000000000000000 : ℝ)) (lo := (564699132397 / 3906250000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (967020016410819 / 500000000000000 : ℝ)) (b := (39262426832855481539 / 50000000000000000000 : ℝ)) (hi := (18070372243603 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_31 : (34782557045683 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 31 ∧ ex (57436 / 100000) 31 ≤ (27826045647193 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_31
  have hlo := exp_neg_ge_of (q := (1972344891061181 / 1000000000000000 : ℝ)) (a := (78149766936568934169 / 100000000000000000000 : ℝ)) (lo := (34782557045683 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1972344890678577 / 1000000000000000 : ℝ)) (b := (78149766940306508661 / 100000000000000000000 : ℝ)) (hi := (27826045647193 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_32 : (27323231011079 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 32 ∧ ex (57436 / 100000) 32 ≤ (68308077553853 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_32
  have hlo := exp_neg_ge_of (q := (1990580073425393 / 1000000000000000 : ℝ)) (a := (38985917697756624961 / 50000000000000000000 : ℝ)) (lo := (27323231011079 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (995290036521249 / 500000000000000 : ℝ)) (b := (38985917699622576819 / 50000000000000000000 : ℝ)) (hi := (68308077553853 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_33 : (26844562413317 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 33 ∧ ex (57436 / 100000) 33 ≤ (134222812118011 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_33
  have hlo := exp_neg_ge_of (q := (2008254083297431 / 1000000000000000 : ℝ)) (a := (9724970770501907801 / 12500000000000000000 : ℝ)) (lo := (26844562413317 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2008254082914301 / 1000000000000000 : ℝ)) (b := (19449941541935304697 / 25000000000000000000 : ℝ)) (hi := (134222812118011 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_34 : (131940999314067 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 34 ∧ ex (57436 / 100000) 34 ≤ (32985249841161 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_34
  have hlo := exp_neg_ge_of (q := (506350107803061 / 250000000000000 : ℝ)) (a := (77633196998790679533 / 100000000000000000000 : ℝ)) (lo := (131940999314067 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (81016017233157 / 40000000000000 : ℝ)) (b := (77633197002510495833 / 100000000000000000000 : ℝ)) (hi := (32985249841161 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_36 : (127679771133171 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 36 ∧ ex (57436 / 100000) 36 ≤ (2553595423643 / 20000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_36
  have hlo := exp_neg_ge_of (q := (1029114968892799 / 500000000000000 : ℝ)) (a := (7731526734316832181 / 10000000000000000000 : ℝ)) (lo := (127679771133171 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1029114968700999 / 500000000000000 : ℝ)) (b := (3092610693875025077 / 4000000000000000000 : ℝ)) (hi := (2553595423643 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_37 : (125686217849359 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 37 ∧ ex (57436 / 100000) 37 ≤ (125686217897587 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_37
  have hlo := exp_neg_ge_of (q := (518491703150093 / 250000000000000 : ℝ)) (a := (19290832311539188091 / 25000000000000000000 : ℝ)) (lo := (125686217849359 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (518491703054167 / 250000000000000 : ℝ)) (b := (19290832312464444703 / 25000000000000000000 : ℝ)) (hi := (125686217897587 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_38 : (61887864564251 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 38 ∧ ex (57436 / 100000) 38 ≤ (123775729176007 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_38
  have hlo := exp_neg_ge_of (q := (522320996748639 / 250000000000000 : ℝ)) (a := (38507865035014697687 / 50000000000000000000 : ℝ)) (lo := (61887864564251 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1044641993305383 / 500000000000000 : ℝ)) (b := (7701573007372417429 / 10000000000000000000 : ℝ)) (hi := (123775729176007 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_39 : (121942791377227 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 39 ∧ ex (57436 / 100000) 39 ≤ (121942791424037 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_39
  have hlo := exp_neg_ge_of (q := (1052101633682597 / 500000000000000 : ℝ)) (a := (38436118252090267761 / 50000000000000000000 : ℝ)) (lo := (121942791377227 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2104203266981333 / 1000000000000000 : ℝ)) (b := (38436118253934558407 / 50000000000000000000 : ℝ)) (hi := (121942791424037 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_41 : (14811241966779 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 41 ∧ ex (57436 / 100000) 41 ≤ (11848993577973 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_41
  have hlo := exp_neg_ge_of (q := (2132927252526551 / 1000000000000000 : ℝ)) (a := (76596721795110322471 / 100000000000000000000 : ℝ)) (lo := (14811241966779 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (106646362607129 / 50000000000000 : ℝ)) (b := (76596721798786745811 / 100000000000000000000 : ℝ)) (hi := (11848993577973 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_42 : (116861252699673 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 42 ∧ ex (57436 / 100000) 42 ≤ (116861252744551 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_42
  have hlo := exp_neg_ge_of (q := (2146767922251537 / 1000000000000000 : ℝ)) (a := (76464317622240053241 / 100000000000000000000 : ℝ)) (lo := (116861252699673 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2146767921867523 / 1000000000000000 : ℝ)) (b := (76464317625910537367 / 100000000000000000000 : ℝ)) (hi := (116861252744551 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_43 : (23058500064111 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 43 ∧ ex (57436 / 100000) 43 ≤ (23058500072967 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_43
  have hlo := exp_neg_ge_of (q := (2160282898744087 / 1000000000000000 : ℝ)) (a := (76335249992662194013 / 100000000000000000000 : ℝ)) (lo := (23058500064111 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2160282898360037 / 1000000000000000 : ℝ)) (b := (19083812499081707777 / 25000000000000000000 : ℝ)) (hi := (23058500072967 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_44 : (7111259680039 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 44 ∧ ex (57436 / 100000) 44 ≤ (113780154924327 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_44
  have hlo := exp_neg_ge_of (q := (2173487158431651 / 1000000000000000 : ℝ)) (a := (15241872021177385471 / 20000000000000000000 : ℝ)) (lo := (7111259680039 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (217348715804757 / 100000000000000 : ℝ)) (b := (76209360109545821419 / 100000000000000000000 : ℝ)) (hi := (113780154924327 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_46 : (27727992017307 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 46 ∧ ex (57436 / 100000) 46 ≤ (55455984055917 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_46
  have hlo := exp_neg_ge_of (q := (549754618195469 / 250000000000000 : ℝ)) (a := (3798326607656385517 / 5000000000000000000 : ℝ)) (lo := (27727992017307 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (549754618099437 / 250000000000000 : ℝ)) (b := (9495816519596925439 / 12500000000000000000 : ℝ)) (hi := (55455984055917 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_47 : (54775188214237 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 47 ∧ ex (57436 / 100000) 47 ≤ (109550376470559 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_47
  have hlo := exp_neg_ge_of (q := (442274155362521 / 200000000000000 : ℝ)) (a := (3792466372400395599 / 5000000000000000000 : ℝ)) (lo := (54775188214237 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2211370776428457 / 1000000000000000 : ℝ)) (b := (37924663725825086463 / 50000000000000000000 : ℝ)) (hi := (109550376470559 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_48 : (108233644571929 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 48 ∧ ex (57436 / 100000) 48 ≤ (108233644613511 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_48
  have hlo := exp_neg_ge_of (q := (1111731506459743 / 500000000000000 : ℝ)) (a := (37867382777327507247 / 50000000000000000000 : ℝ)) (lo := (108233644571929 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1111731506267661 / 500000000000000 : ℝ)) (b := (75734765558291931907 / 100000000000000000000 : ℝ)) (hi := (108233644613511 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_49 : (10695940524749 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 49 ∧ ex (57436 / 100000) 49 ≤ (13369925661073 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_49
  have hlo := exp_neg_ge_of (q := (1117652953358631 / 500000000000000 : ℝ)) (a := (75622733650827843079 / 100000000000000000000 : ℝ)) (lo := (10695940524749 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2235305906333083 / 1000000000000000 : ℝ)) (b := (37811366827229764391 / 50000000000000000000 : ℝ)) (hi := (13369925661073 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_51 : (104529769692597 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 51 ∧ ex (57436 / 100000) 51 ≤ (2613244243319 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_51
  have hlo := exp_neg_ge_of (q := (1129141685353003 / 500000000000000 : ℝ)) (a := (75405842944929943047 / 100000000000000000000 : ℝ)) (lo := (104529769692597 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (564570842580451 / 250000000000000 : ℝ)) (b := (75405842948551443309 / 100000000000000000000 : ℝ)) (hi := (2613244243319 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_52 : (51685214591543 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 52 ∧ ex (57436 / 100000) 52 ≤ (20674085844561 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_52
  have hlo := exp_neg_ge_of (q := (2269436342498899 / 1000000000000000 : ℝ)) (a := (37650395642204738609 / 50000000000000000000 : ℝ)) (lo := (51685214591543 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (17729971422771 / 7812500000000 : ℝ)) (b := (75300791288026024113 / 100000000000000000000 : ℝ)) (hi := (20674085844561 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_53 : (102245666767183 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 53 ∧ ex (57436 / 100000) 53 ≤ (10224566680647 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_53
  have hlo := exp_neg_ge_of (q := (1140188431881137 / 500000000000000 : ℝ)) (a := (18799470732216069521 / 25000000000000000000 : ℝ)) (lo := (102245666767183 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (456075372675611 / 200000000000000 : ℝ)) (b := (1879947073311899129 / 2500000000000000000 : ℝ)) (hi := (10224566680647 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_54 : (20230765479027 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 54 ∧ ex (57436 / 100000) 54 ≤ (25288456858501 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_54
  have hlo := exp_neg_ge_of (q := (114555643863957 / 50000000000000 : ℝ)) (a := (7509703492714845899 / 10000000000000000000 : ℝ)) (lo := (20230765479027 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1145556438447457 / 500000000000000 : ℝ)) (b := (75097034930755375859 / 100000000000000000000 : ℝ)) (hi := (25288456858501 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_56 : (99062828642903 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 56 ∧ ex (57436 / 100000) 56 ≤ (9906282868097 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_56
  have hlo := exp_neg_ge_of (q := (2312000997385133 / 1000000000000000 : ℝ)) (a := (1872530280052422363 / 2500000000000000000 : ℝ)) (lo := (99062828642903 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (36125015578139 / 15625000000000 : ℝ)) (b := (74901211205694525151 / 100000000000000000000 : ℝ)) (hi := (9906282868097 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_57 : (98060864527353 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 57 ∧ ex (57436 / 100000) 57 ≤ (19612172913007 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_57
  have hlo := exp_neg_ge_of (q := (46443338529759 / 20000000000000 : ℝ)) (a := (14961218320148490599 / 20000000000000000000 : ℝ)) (lo := (98060864527353 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2322166926103707 / 1000000000000000 : ℝ)) (b := (4675380725270973717 / 6250000000000000000 : ℝ)) (hi := (19612172913007 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_58 : (12135774847473 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 58 ∧ ex (57436 / 100000) 58 ≤ (97086198822637 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_58
  have hlo := exp_neg_ge_of (q := (4554992281011 / 1953125000000 : ℝ)) (a := (74712744000441640673 / 100000000000000000000 : ℝ)) (lo := (12135774847473 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2332156047436273 / 1000000000000000 : ℝ)) (b := (3735637200228185191 / 5000000000000000000 : ℝ)) (hi := (97086198822637 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_59 : (48068817966143 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 59 ∧ ex (57436 / 100000) 59 ≤ (96137635979757 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_59
  have hlo := exp_neg_ge_of (q := (1170987203331899 / 500000000000000 : ℝ)) (a := (74621105679751700441 / 100000000000000000000 : ℝ)) (lo := (48068817966143 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2341974406170041 / 1000000000000000 : ℝ)) (b := (9327638210544683289 / 12500000000000000000 : ℝ)) (hi := (96137635979757 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_61 : (94314389039009 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 61 ∧ ex (57436 / 100000) 61 ≤ (47157194547149 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_61
  have hlo := exp_neg_ge_of (q := (1180560756541319 / 500000000000000 : ℝ)) (a := (37221360977111518107 / 50000000000000000000 : ℝ)) (lo := (94314389039009 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2361121512496449 / 1000000000000000 : ℝ)) (b := (9305340244959740239 / 12500000000000000000 : ℝ)) (hi := (47157194547149 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_62 : (93437650389077 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 62 ∧ ex (57436 / 100000) 62 ≤ (18687530089533 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_62
  have hlo := exp_neg_ge_of (q := (1185230452941599 / 500000000000000 : ℝ)) (a := (7435586643501649331 / 10000000000000000000 : ℝ)) (lo := (93437650389077 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (592615226314051 / 250000000000000 : ℝ)) (b := (37177933220422142883 / 50000000000000000000 : ℝ)) (hi := (18687530089533 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_63 : (23145724019557 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 63 ∧ ex (57436 / 100000) 63 ≤ (18516579227953 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_63
  have hlo := exp_neg_ge_of (q := (475930172393811 / 200000000000000 : ℝ)) (a := (3713524979167363069 / 5000000000000000000 : ℝ)) (lo := (23145724019557 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1189825430652209 / 500000000000000 : ℝ)) (b := (74270499589517843673 / 100000000000000000000 : ℝ)) (hi := (18516579227953 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_64 : (91749238821517 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 64 ∧ ex (57436 / 100000) 64 ≤ (9174923888569 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_64
  have hlo := exp_neg_ge_of (q := (2388696088305093 / 1000000000000000 : ℝ)) (a := (74186572853452056453 / 100000000000000000000 : ℝ)) (lo := (91749238821517 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (597174021901421 / 250000000000000 : ℝ)) (b := (1159165200936533253 / 1562500000000000000 : ℝ)) (hi := (9174923888569 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_66 : (90141907697457 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 66 ∧ ex (57436 / 100000) 66 ≤ (90141907766089 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_66
  have hlo := exp_neg_ge_of (q := (1203185049113239 / 500000000000000 : ℝ)) (a := (74022856986700753887 / 100000000000000000000 : ℝ)) (lo := (90141907697457 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1203185048732567 / 500000000000000 : ℝ)) (b := (74022856993745609297 / 100000000000000000000 : ℝ)) (hi := (90141907766089 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_67 : (44683345349427 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 67 ∧ ex (57436 / 100000) 67 ≤ (89366690769363 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_67
  have hlo := exp_neg_ge_of (q := (2415007253491659 / 1000000000000000 : ℝ)) (a := (36971490874632712467 / 50000000000000000000 : ℝ)) (lo := (44683345349427 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (241500725270271 / 100000000000000 : ℝ)) (b := (36971490878278919591 / 50000000000000000000 : ℝ)) (hi := (89366690769363 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_68 : (44304739254287 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 68 ∧ ex (57436 / 100000) 68 ≤ (22152369645189 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_68
  have hlo := exp_neg_ge_of (q := (605879111545927 / 250000000000000 : ℝ)) (a := (18466093544280368173 / 25000000000000000000 : ℝ)) (lo := (44304739254287 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (121175822268457 / 50000000000000 : ℝ)) (b := (36932187092321343681 / 50000000000000000000 : ℝ)) (hi := (22152369645189 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_69 : (21967399319577 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 69 ∧ ex (57436 / 100000) 69 ≤ (87869597351979 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_69
  have hlo := exp_neg_ge_of (q := (607975353159571 / 250000000000000 : ℝ)) (a := (36893497973806703541 / 50000000000000000000 : ℝ)) (lo := (21967399319577 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2431901411799913 / 1000000000000000 : ℝ)) (b := (36893497977673149221 / 50000000000000000000 : ℝ)) (hi := (87869597351979 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_71 : (43219651322931 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 71 ∧ ex (57436 / 100000) 71 ≤ (8643930272203 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_71
  have hlo := exp_neg_ge_of (q := (1224156407434727 / 500000000000000 : ℝ)) (a := (73635782593351189881 / 100000000000000000000 : ℝ)) (lo := (43219651322931 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (244831281398833 / 100000000000000 : ℝ)) (b := (18408945650365444283 / 25000000000000000000 : ℝ)) (hi := (8643930272203 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_72 : (85747705370187 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 72 ∧ ex (57436 / 100000) 72 ≤ (85747705447393 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_72
  have hlo := exp_neg_ge_of (q := (491269190565087 / 200000000000000 : ℝ)) (a := (73561878904460338401 / 100000000000000000000 : ℝ)) (lo := (85747705370187 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (24563459519251 / 10000000000000 : ℝ)) (b := (919523486409243097 / 1250000000000000000 : ℝ)) (hi := (85747705447393 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_73 : (85071067350603 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 73 ∧ ex (57436 / 100000) 73 ≤ (21267766857181 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_73
  have hlo := exp_neg_ge_of (q := (2464268285339701 / 1000000000000000 : ℝ)) (a := (36744533627330048641 / 50000000000000000000 : ℝ)) (lo := (85071067350603 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (616067071105361 / 250000000000000 : ℝ)) (b := (18372266815773914669 / 25000000000000000000 : ℝ)) (hi := (21267766857181 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_74 : (84408866661433 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 74 ∧ ex (57436 / 100000) 74 ≤ (84408866740359 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_74
  have hlo := exp_neg_ge_of (q := (2472082827667847 / 1000000000000000 : ℝ)) (a := (2294291152360906237 / 3125000000000000000 : ℝ)) (lo := (84408866661433 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2472082826732853 / 1000000000000000 : ℝ)) (b := (4588582305258121019 / 6250000000000000000 : ℝ)) (hi := (84408866740359 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_76 : (16625162558713 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 76 ∧ ex (57436 / 100000) 76 ≤ (5195363304613 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_76
  have hlo := exp_neg_ge_of (q := (1243700001043089 / 500000000000000 : ℝ)) (a := (73276883127974268979 / 100000000000000000000 : ℝ)) (lo := (16625162558713 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2487400001120909 / 1000000000000000 : ℝ)) (b := (14655376627363225239 / 20000000000000000000 : ℝ)) (hi := (5195363304613 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_77 : (20626008644403 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 77 ∧ ex (57436 / 100000) 77 ≤ (16500806931677 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_77
  have hlo := exp_neg_ge_of (q := (623727020716541 / 250000000000000 : ℝ)) (a := (36604072147167809997 / 50000000000000000000 : ℝ)) (lo := (20626008644403 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2494908081887193 / 1000000000000000 : ℝ)) (b := (585665154426356673 / 800000000000000000 : ℝ)) (hi := (16500806931677 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_78 : (8189484092483 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 78 ∧ ex (57436 / 100000) 78 ≤ (81894841006059 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_78
  have hlo := exp_neg_ge_of (q := (625579820619497 / 250000000000000 : ℝ)) (a := (18285088919386825601 / 25000000000000000000 : ℝ)) (lo := (8189484092483 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2502319281486177 / 1000000000000000 : ℝ)) (b := (18285088921653843823 / 25000000000000000000 : ℝ)) (hi := (81894841006059 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_79 : (81297820627849 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 79 ∧ ex (57436 / 100000) 79 ≤ (16259564141893 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_79
  have hlo := exp_neg_ge_of (q := (2509636069333147 / 1000000000000000 : ℝ)) (a := (36536746104845850803 / 50000000000000000000 : ℝ)) (lo := (81297820627849 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2509636068329293 / 1000000000000000 : ℝ)) (b := (73073492218861502159 / 100000000000000000000 : ℝ)) (hi := (16259564141893 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_81 : (8013874633881 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 81 ∧ ex (57436 / 100000) 81 ≤ (80138746421019 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_81
  have hlo := exp_neg_ge_of (q := (2523995817285389 / 1000000000000000 : ℝ)) (a := (36471222620600748871 / 50000000000000000000 : ℝ)) (lo := (8013874633881 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (630998954064903 / 250000000000000 : ℝ)) (b := (72942445250554773061 / 100000000000000000000 : ℝ)) (hi := (80138746421019 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_82 : (39787978970359 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 82 ∧ ex (57436 / 100000) 82 ≤ (15915191604629 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_82
  have hlo := exp_neg_ge_of (q := (2531043267674411 / 1000000000000000 : ℝ)) (a := (72878216253006746307 / 100000000000000000000 : ℝ)) (lo := (39787978970359 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (50620865332773 / 20000000000000 : ℝ)) (b := (72878216262442753033 / 100000000000000000000 : ℝ)) (hi := (15915191604629 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_83 : (19755968051937 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 83 ∧ ex (57436 / 100000) 83 ≤ (15804774458069 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_83
  have hlo := exp_neg_ge_of (q := (2538005292317283 / 1000000000000000 : ℝ)) (a := (72814821349627415647 / 100000000000000000000 : ℝ)) (lo := (19755968051937 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2538005291272129 / 1000000000000000 : ℝ)) (b := (9101852669892590447 / 12500000000000000000 : ℝ)) (hi := (15804774458069 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_84 : (78482160294621 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 84 ∧ ex (57436 / 100000) 84 ≤ (78482160377347 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_84
  have hlo := exp_neg_ge_of (q := (50897678748279 / 20000000000000 : ℝ)) (a := (568376873781255877 / 781250000000000000 : ℝ)) (lo := (78482160294621 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2544883936359951 / 1000000000000000 : ℝ)) (b := (72752239853586336489 / 100000000000000000000 : ℝ)) (hi := (78482160377347 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_86 : (19357152781133 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 86 ∧ ex (57436 / 100000) 86 ≤ (387143056037 / 5000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_86
  have hlo := exp_neg_ge_of (q := (2558398913919421 / 1000000000000000 : ℝ)) (a := (18157359500170515859 / 25000000000000000000 : ℝ)) (lo := (19357152781133 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2558398912849233 / 1000000000000000 : ℝ)) (b := (36314719005199237581 / 50000000000000000000 : ℝ)) (hi := (387143056037 / 5000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_87 : (38458091292251 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 87 ∧ ex (57436 / 100000) 87 ≤ (76916182667393 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_87
  have hlo := exp_neg_ge_of (q := (2565038987879633 / 1000000000000000 : ℝ)) (a := (36284589953263707091 / 50000000000000000000 : ℝ)) (lo := (38458091292251 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (160314936675127 / 62500000000000 : ℝ)) (b := (72569179916303025741 / 100000000000000000000 : ℝ)) (hi := (76916182667393 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_88 : (76412943958583 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 88 ∧ ex (57436 / 100000) 88 ≤ (38206472020733 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_88
  have hlo := exp_neg_ge_of (q := (321450396702311 / 125000000000000 : ℝ)) (a := (72509659631772590901 / 100000000000000000000 : ℝ)) (lo := (76412943958583 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (20090649785421 / 7812500000000 : ℝ)) (b := (7250965964160363859 / 10000000000000000000 : ℝ)) (hi := (38206472020733 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_89 : (75918628783377 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 89 ∧ ex (57436 / 100000) 89 ≤ (37959314433113 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_89
  have hlo := exp_neg_ge_of (q := (644523296544857 / 250000000000000 : ℝ)) (a := (9056357488806943897 / 12500000000000000000 : ℝ)) (lo := (75918628783377 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (515618637017643 / 200000000000000 : ℝ)) (b := (18112714980084633423 / 25000000000000000000 : ℝ)) (hi := (37959314433113 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_91 : (74955755436647 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 91 ∧ ex (57436 / 100000) 91 ≤ (37477877759679 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_91
  have hlo := exp_neg_ge_of (q := (103634290681313 / 40000000000000 : ℝ)) (a := (36167677999781223633 / 50000000000000000000 : ℝ)) (lo := (74955755436647 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (323857158241181 / 125000000000000 : ℝ)) (b := (72335356009539695419 / 100000000000000000000 : ℝ)) (hi := (37477877759679 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_92 : (74486715272421 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 92 ∧ ex (57436 / 100000) 92 ≤ (74486715355031 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_92
  have hlo := exp_neg_ge_of (q := (649283621997043 / 250000000000000 : ℝ)) (a := (9034827516860519603 / 12500000000000000000 : ℝ)) (lo := (74486715272421 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2597134486879197 / 1000000000000000 : ℝ)) (b := (72278620144904174553 / 100000000000000000000 : ℝ)) (hi := (74486715355031 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_93 : (9253204199949 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 93 ∧ ex (57436 / 100000) 93 ≤ (74025633682083 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_93
  have hlo := exp_neg_ge_of (q := (260334384576603 / 100000000000000 : ℝ)) (a := (18055635356121147107 / 25000000000000000000 : ℝ)) (lo := (9253204199949 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1301671922325877 / 500000000000000 : ℝ)) (b := (36111270717272353451 / 50000000000000000000 : ℝ)) (hi := (74025633682083 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_94 : (73572291962701 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 94 ∧ ex (57436 / 100000) 94 ≤ (73572292045057 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_94
  have hlo := exp_neg_ge_of (q := (326185849003393 / 125000000000000 : ℝ)) (a := (14433421062434629821 / 20000000000000000000 : ℝ)) (lo := (73572291962701 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (521897358181569 / 200000000000000 : ℝ)) (b := (9020888165283859551 / 12500000000000000000 : ℝ)) (hi := (73572292045057 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_96 : (9085999471409 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 96 ∧ ex (57436 / 100000) 96 ≤ (72687995853313 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_96
  have hlo := exp_neg_ge_of (q := (1310789514070719 / 500000000000000 : ℝ)) (a := (4503631562617444107 / 6250000000000000000 : ℝ)) (lo := (9085999471409 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (327697378376607 / 125000000000000 : ℝ)) (b := (3602905250602261719 / 5000000000000000000 : ℝ)) (hi := (72687995853313 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_97 : (36128321972301 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 97 ∧ ex (57436 / 100000) 97 ≤ (72256644026467 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_97
  have hlo := exp_neg_ge_of (q := (1313765499253303 / 500000000000000 : ℝ)) (a := (36002256988460232601 / 50000000000000000000 : ℝ)) (lo := (36128321972301 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1313765498686867 / 500000000000000 : ℝ)) (b := (36002256993558832597 / 50000000000000000000 : ℝ)) (hi := (72256644026467 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_98 : (17958059222307 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 98 ∧ ex (57436 / 100000) 98 ≤ (8979029621363 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_98
  have hlo := exp_neg_ge_of (q := (658355480486473 / 250000000000000 : ℝ)) (a := (71951511858888994557 / 100000000000000000000 : ℝ)) (lo := (17958059222307 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1316710960404473 / 500000000000000 : ℝ)) (b := (35975755934557674847 / 50000000000000000000 : ℝ)) (hi := (8979029621363 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_99 : (71414593624411 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 99 ∧ ex (57436 / 100000) 99 ≤ (71414593705889 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_99
  have hlo := exp_neg_ge_of (q := (2639253038023063 / 1000000000000000 : ℝ)) (a := (2875963450609820467 / 4000000000000000000 : ℝ)) (lo := (71414593624411 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (527850607376449 / 200000000000000 : ℝ)) (b := (7189908627549923503 / 10000000000000000000 : ℝ)) (hi := (71414593705889 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_101 : (70598906663289 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 101 ∧ ex (57436 / 100000) 101 ≤ (70598906744343 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_101
  have hlo := exp_neg_ge_of (q := (2650740620958451 / 1000000000000000 : ℝ)) (a := (1435918340324962257 / 2000000000000000000 : ℝ)) (lo := (70598906663289 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2650740619810451 / 1000000000000000 : ℝ)) (b := (8974489628318952381 / 12500000000000000000 : ℝ)) (hi := (70598906744343 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_102 : (70200532258709 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 102 ∧ ex (57436 / 100000) 102 ≤ (70200532339541 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_102
  have hlo := exp_neg_ge_of (q := (21251195087569 / 8000000000000 : ℝ)) (a := (71745150445436949859 / 100000000000000000000 : ℝ)) (lo := (70200532258709 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2656399384794793 / 1000000000000000 : ℝ)) (b := (448407190348519209 / 625000000000000000 : ℝ)) (hi := (70200532339541 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_103 : (1090754057609 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 103 ∧ ex (57436 / 100000) 103 ≤ (34904129883789 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_103
  have hlo := exp_neg_ge_of (q := (2662002942590283 / 1000000000000000 : ℝ)) (a := (71694914539416814701 / 100000000000000000000 : ℝ)) (lo := (1090754057609 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1331001470717889 / 500000000000000 : ℝ)) (b := (71694914549764165313 / 100000000000000000000 : ℝ)) (hi := (34904129883789 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_104 : (69421937595083 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 104 ∧ ex (57436 / 100000) 104 ≤ (69421937675449 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_104
  have hlo := exp_neg_ge_of (q := (2667552357743967 / 1000000000000000 : ℝ)) (a := (14329039735826747217 / 20000000000000000000 : ℝ)) (lo := (69421937595083 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2667552356586439 / 1000000000000000 : ℝ)) (b := (35822599344750503033 / 50000000000000000000 : ℝ)) (hi := (69421937675449 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_106 : (8583320628711 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 106 ∧ ex (57436 / 100000) 106 ≤ (34333282554783 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_106
  have hlo := exp_neg_ge_of (q := (2678492879011837 / 1000000000000000 : ℝ)) (a := (71547286167776966033 / 100000000000000000000 : ℝ)) (lo := (8583320628711 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2678492877848681 / 1000000000000000 : ℝ)) (b := (71547286178180445489 / 100000000000000000000 : ℝ)) (hi := (34333282554783 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_107 : (8537154597871 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 107 ∧ ex (57436 / 100000) 107 ≤ (13659447372519 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_107
  have hlo := exp_neg_ge_of (q := (1341942985140633 / 500000000000000 : ℝ)) (a := (3574953489563129159 / 5000000000000000000 : ℝ)) (lo := (8537154597871 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2683885969115491 / 1000000000000000 : ℝ)) (b := (8937383725210310147 / 12500000000000000000 : ℝ)) (hi := (13659447372519 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_108 : (13586660611481 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 108 ∧ ex (57436 / 100000) 108 ≤ (33966651568389 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_108
  have hlo := exp_neg_ge_of (q := (2689228892532793 / 1000000000000000 : ℝ)) (a := (71451333987211118857 / 100000000000000000000 : ℝ)) (lo := (13586660611481 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2689228891364517 / 1000000000000000 : ℝ)) (b := (71451333997646420383 / 100000000000000000000 : ℝ)) (hi := (33966651568389 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_109 : (8446829524333 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 109 ∧ ex (57436 / 100000) 109 ≤ (3378731813689 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_109
  have hlo := exp_neg_ge_of (q := (2694522570560767 / 1000000000000000 : ℝ)) (a := (35702034790997483217 / 50000000000000000000 : ℝ)) (lo := (8446829524333 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (336815321173763 / 125000000000000 : ℝ)) (b := (71404069592444693403 / 100000000000000000000 : ℝ)) (hi := (3378731813689 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_111 : (33436306516981 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 111 ∧ ex (57436 / 100000) 111 ≤ (33436306556277 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_111
  have hlo := exp_neg_ge_of (q := (676241441838239 / 250000000000000 : ℝ)) (a := (14262183910085738231 / 20000000000000000000 : ℝ)) (lo := (33436306516981 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2704965766177833 / 1000000000000000 : ℝ)) (b := (3565545978045229443 / 5000000000000000000 : ℝ)) (hi := (33436306556277 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_112 : (8316127690337 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 112 ∧ ex (57436 / 100000) 112 ≤ (66529021601023 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_112
  have hlo := exp_neg_ge_of (q := (2710117012645921 / 1000000000000000 : ℝ)) (a := (71265016825692939631 / 100000000000000000000 : ℝ)) (lo := (8316127690337 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (542023402293743 / 200000000000000 : ℝ)) (b := (3563250841809033681 / 5000000000000000000 : ℝ)) (hi := (66529021601023 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_113 : (8273778266199 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 113 ∧ ex (57436 / 100000) 113 ≤ (66190226207653 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_113
  have hlo := exp_neg_ge_of (q := (678805617121521 / 250000000000000 : ℝ)) (a := (71219551285336280479 / 100000000000000000000 : ℝ)) (lo := (8273778266199 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1357611233653443 / 500000000000000 : ℝ)) (b := (71219551295835081451 / 100000000000000000000 : ℝ)) (hi := (66190226207653 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_114 : (32928059172281 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 114 ∧ ex (57436 / 100000) 114 ≤ (32928059211177 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_114
  have hlo := exp_neg_ge_of (q := (2720282941751851 / 1000000000000000 : ℝ)) (a := (711745149515007497 / 1000000000000000000 : ℝ)) (lo := (32928059172281 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2720282940570747 / 1000000000000000 : ℝ)) (b := (71174514962009893537 / 100000000000000000000 : ℝ)) (hi := (32928059211177 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_116 : (6520154831957 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 116 ∧ ex (57436 / 100000) 116 ≤ (32600774198411 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_116
  have hlo := exp_neg_ge_of (q := (2730272063098697 / 1000000000000000 : ℝ)) (a := (71085699054256887111 / 100000000000000000000 : ℝ)) (lo := (6520154831957 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1365136030957011 / 500000000000000 : ℝ)) (b := (2843427962591387913 / 4000000000000000000 : ℝ)) (hi := (32600774198411 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_117 : (64880885426531 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 117 ∧ ex (57436 / 100000) 117 ≤ (64880885503511 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_117
  have hlo := exp_neg_ge_of (q := (1367601111063311 / 500000000000000 : ℝ)) (a := (2220059517972921639 / 3125000000000000000 : ℝ)) (lo := (64880885426531 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (109408088837611 / 40000000000000 : ℝ)) (b := (71041904585669690359 / 100000000000000000000 : ℝ)) (hi := (64880885503511 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_118 : (4035281786699 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 118 ∧ ex (57436 / 100000) 118 ≤ (64564508663893 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_118
  have hlo := exp_neg_ge_of (q := (548018084369113 / 200000000000000 : ℝ)) (a := (35499254728493353391 / 50000000000000000000 : ℝ)) (lo := (4035281786699 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (548018084131523 / 200000000000000 : ℝ)) (b := (70998509467530720807 / 100000000000000000000 : ℝ)) (hi := (64564508663893 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_119 : (32126162456589 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 119 ∧ ex (57436 / 100000) 119 ≤ (12850464997923 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_119
  have hlo := exp_neg_ge_of (q := (2744937370442233 / 1000000000000000 : ℝ)) (a := (17738876679895868323 / 25000000000000000000 : ℝ)) (lo := (32126162456589 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1372468684626373 / 500000000000000 : ℝ)) (b := (70955506730134759279 / 100000000000000000000 : ℝ)) (hi := (12850464997923 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_121 : (63640179261561 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 121 ∧ ex (57436 / 100000) 121 ≤ (31820089668727 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_121
  have hlo := exp_neg_ge_of (q := (688627564677487 / 250000000000000 : ℝ)) (a := (70870651356914533199 / 100000000000000000000 : ℝ)) (lo := (63640179261561 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (110180410300703 / 40000000000000 : ℝ)) (b := (70870651367478820361 / 100000000000000000000 : ℝ)) (hi := (31820089668727 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_122 : (63340044950989 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 122 ∧ ex (57436 / 100000) 122 ≤ (15835011256631 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_122
  have hlo := exp_neg_ge_of (q := (2759237528193997 / 1000000000000000 : ℝ)) (a := (70828785644105090781 / 100000000000000000000 : ℝ)) (lo := (63340044950989 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (344904690875203 / 125000000000000 : ℝ)) (b := (70828785654663164107 / 100000000000000000000 : ℝ)) (hi := (15835011256631 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_123 : (63043758943909 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 123 ∧ ex (57436 / 100000) 123 ≤ (63043759019091 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_123
  have hlo := exp_neg_ge_of (q := (552785241458541 / 200000000000000 : ℝ)) (a := (70787286125558750983 / 100000000000000000000 : ℝ)) (lo := (63043758943909 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2763926206100333 / 1000000000000000 : ℝ)) (b := (35393643068055328241 / 50000000000000000000 : ℝ)) (hi := (63043759019091 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_124 : (62751241207789 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 124 ∧ ex (57436 / 100000) 124 ≤ (31375620641311 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_124
  have hlo := exp_neg_ge_of (q := (346072115120239 / 125000000000000 : ℝ)) (a := (35373073329905394489 / 50000000000000000000 : ℝ)) (lo := (62751241207789 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (138428845988477 / 50000000000000 : ℝ)) (b := (14149229334071317889 / 20000000000000000000 : ℝ)) (hi := (31375620641311 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_126 : (31088600898587 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 126 ∧ ex (57436 / 100000) 126 ≤ (62177201871323 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_126
  have hlo := exp_neg_ge_of (q := (1388883438508827 / 500000000000000 : ℝ)) (a := (35332462036689009043 / 50000000000000000000 : ℝ)) (lo := (31088600898587 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1388883437912641 / 500000000000000 : ℝ)) (b := (35332462041955883383 / 50000000000000000000 : ℝ)) (hi := (62177201871323 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_127 : (61895531190049 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 127 ∧ ex (57436 / 100000) 127 ≤ (61895531263863 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_127
  have hlo := exp_neg_ge_of (q := (2173677574937 / 781250000000 : ℝ)) (a := (14124965881549311771 / 20000000000000000000 : ℝ)) (lo := (61895531190049 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (695576823681747 / 250000000000000 : ℝ)) (b := (35312414709137179529 / 50000000000000000000 : ℝ)) (hi := (61895531263863 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_128 : (7702166354087 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 128 ∧ ex (57436 / 100000) 128 ≤ (30808665453089 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_128
  have hlo := exp_neg_ge_of (q := (22294496826607 / 8000000000000 : ℝ)) (a := (70585071695774297347 / 100000000000000000000 : ℝ)) (lo := (7702166354087 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2786812102133503 / 1000000000000000 : ℝ)) (b := (70585071706296199571 / 100000000000000000000 : ℝ)) (hi := (30808665453089 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_129 : (958477052451 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 129 ∧ ex (57436 / 100000) 129 ≤ (61342531430019 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_129
  have hlo := exp_neg_ge_of (q := (2791281853510173 / 1000000000000000 : ℝ)) (a := (70545645506223414847 / 100000000000000000000 : ℝ)) (lo := (958477052451 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2791281852317801 / 1000000000000000 : ℝ)) (b := (70545645516739468781 / 100000000000000000000 : ℝ)) (hi := (61342531430019 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_131 : (6080286706211 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 131 ∧ ex (57436 / 100000) 131 ≤ (30401433567311 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_131
  have hlo := exp_neg_ge_of (q := (2800118335494817 / 1000000000000000 : ℝ)) (a := (70467766609406833987 / 100000000000000000000 : ℝ)) (lo := (6080286706211 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (560023666860489 / 200000000000000 : ℝ)) (b := (35233883309955668631 / 50000000000000000000 : ℝ)) (hi := (30401433567311 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_132 : (15134468198599 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 132 ∧ ex (57436 / 100000) 132 ≤ (1891808527081 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_132
  have hlo := exp_neg_ge_of (q := (2804486113197711 / 1000000000000000 : ℝ)) (a := (35214651833869883893 / 50000000000000000000 : ℝ)) (lo := (15134468198599 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2804486112005339 / 1000000000000000 : ℝ)) (b := (70429303678238567167 / 100000000000000000000 : ℝ)) (hi := (1891808527081 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_133 : (60276020385323 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 133 ∧ ex (57436 / 100000) 133 ≤ (30138010228603 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_133
  have hlo := exp_neg_ge_of (q := (56176418524529 / 20000000000000 : ℝ)) (a := (14078230354422719383 / 20000000000000000000 : ℝ)) (lo := (60276020385323 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1404410462517039 / 500000000000000 : ℝ)) (b := (35195575891303369519 / 50000000000000000000 : ℝ)) (hi := (30138010228603 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_134 : (468884760767 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 134 ∧ ex (57436 / 100000) 134 ≤ (60017249449751 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_134
  have hlo := exp_neg_ge_of (q := (2813123268440809 / 1000000000000000 : ℝ)) (a := (70353306096617858229 / 100000000000000000000 : ℝ)) (lo := (468884760767 / 7812500000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2813123267248437 / 1000000000000000 : ℝ)) (b := (70353306107105389009 / 100000000000000000000 : ℝ)) (hi := (60017249449751 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_136 : (59508717705001 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 136 ∧ ex (57436 / 100000) 136 ≤ (59508717775969 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_136
  have hlo := exp_neg_ge_of (q := (1410816230556181 / 500000000000000 : ℝ)) (a := (35139257325006898313 / 50000000000000000000 : ℝ)) (lo := (59508717705001 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (282163245991999 / 100000000000000 : ℝ)) (b := (70278514660490239673 / 100000000000000000000 : ℝ)) (hi := (59508717775969 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_137 : (592588439279 / 10000000000000 : ℝ) ≤ ex (57436 / 100000) 137 ∧ ex (57436 / 100000) 137 ≤ (59258843998571 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_137
  have hlo := exp_neg_ge_of (q := (565168049099929 / 200000000000000 : ℝ)) (a := (4390097485307142981 / 6250000000000000000 : ℝ)) (lo := (592588439279 / 10000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2825840244307273 / 1000000000000000 : ℝ)) (b := (70241559775385252993 / 100000000000000000000 : ℝ)) (hi := (59258843998571 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_138 : (7376478153633 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 138 ∧ ex (57436 / 100000) 138 ≤ (59011825299441 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_138
  have hlo := exp_neg_ge_of (q := (566003485509579 / 200000000000000 : ℝ)) (a := (70204892865705510899 / 100000000000000000000 : ℝ)) (lo := (7376478153633 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2830017426355523 / 1000000000000000 : ℝ)) (b := (14040978575234208329 / 20000000000000000000 : ℝ)) (hi := (59011825299441 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_139 : (14691902162341 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 139 ∧ ex (57436 / 100000) 139 ≤ (58767608719449 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_139
  have hlo := exp_neg_ge_of (q := (708541112293487 / 250000000000000 : ℝ)) (a := (14033701929104832819 / 20000000000000000000 : ℝ)) (lo := (14691902162341 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (113366577919263 / 40000000000000 : ℝ)) (b := (35084254827992155807 / 50000000000000000000 : ℝ)) (hi := (58767608719449 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_141 : (2914368836887 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 141 ∧ ex (57436 / 100000) 141 ≤ (29143688403627 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_141
  have hlo := exp_neg_ge_of (q := (177648108223663 / 62500000000000 : ℝ)) (a := (70096577486115695979 / 100000000000000000000 : ℝ)) (lo := (2914368836887 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (710592432596559 / 250000000000000 : ℝ)) (b := (70096577496565175901 / 100000000000000000000 : ℝ)) (hi := (29143688403627 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_142 : (29025631042089 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 142 ∧ ex (57436 / 100000) 142 ≤ (5805126215341 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_142
  have hlo := exp_neg_ge_of (q := (88950900929527 / 31250000000000 : ℝ)) (a := (3503051019817200877 / 5000000000000000000 : ℝ)) (lo := (29025631042089 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2846428828552491 / 1000000000000000 : ℝ)) (b := (35030510203394119087 / 50000000000000000000 : ℝ)) (hi := (5805126215341 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_143 : (57817750823581 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 143 ∧ ex (57436 / 100000) 143 ≤ (11563550178507 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_143
  have hlo := exp_neg_ge_of (q := (712614860694271 / 250000000000000 : ℝ)) (a := (70025730679307555271 / 100000000000000000000 : ℝ)) (lo := (57817750823581 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (356307430198089 / 125000000000000 : ℝ)) (b := (35012865344873269613 / 50000000000000000000 : ℝ)) (hi := (11563550178507 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_144 : (28793398172309 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 144 ∧ ex (57436 / 100000) 144 ≤ (57586796413297 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_144
  have hlo := exp_neg_ge_of (q := (114178478707419 / 40000000000000 : ℝ)) (a := (69990704475707404171 / 100000000000000000000 : ℝ)) (lo := (28793398172309 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2854461966493103 / 1000000000000000 : ℝ)) (b := (69990704486141199753 / 100000000000000000000 : ℝ)) (hi := (57586796413297 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_146 : (3570773562729 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 146 ∧ ex (57436 / 100000) 146 ≤ (57132377071801 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_146
  have hlo := exp_neg_ge_of (q := (715596075046351 / 250000000000000 : ℝ)) (a := (69921427579436687603 / 100000000000000000000 : ℝ)) (lo := (3570773562729 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2862384298993031 / 1000000000000000 : ℝ)) (b := (69921427589860231581 / 100000000000000000000 : ℝ)) (hi := (57132377071801 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_147 : (14227206132367 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 147 ∧ ex (57436 / 100000) 147 ≤ (28454412298669 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_147
  have hlo := exp_neg_ge_of (q := (1433152430741619 / 500000000000000 : ℝ)) (a := (69887169569179464311 / 100000000000000000000 : ℝ)) (lo := (14227206132367 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1433152430145433 / 500000000000000 : ℝ)) (b := (8735896197449740811 / 12500000000000000000 : ℝ)) (hi := (28454412298669 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_148 : (56687653544333 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 148 ∧ ex (57436 / 100000) 148 ≤ (2834382680597 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_148
  have hlo := exp_neg_ge_of (q := (2870198842500161 / 1000000000000000 : ℝ)) (a := (69853160432830495881 / 100000000000000000000 : ℝ)) (lo := (56687653544333 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (717549710326947 / 250000000000000 : ℝ)) (b := (17463290110810982773 / 25000000000000000000 : ℝ)) (hi := (2834382680597 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_149 : (5646882284279 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 149 ∧ ex (57436 / 100000) 149 ≤ (7058602863767 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_149
  have hlo := exp_neg_ge_of (q := (2874066601223837 / 1000000000000000 : ℝ)) (a := (69819396699031577217 / 100000000000000000000 : ℝ)) (lo := (5646882284279 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (574813320006293 / 200000000000000 : ℝ)) (b := (4363712294340000303 / 6250000000000000000 : ℝ)) (hi := (7058602863767 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_151 : (7004752794403 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 151 ∧ ex (57436 / 100000) 151 ≤ (56038022422057 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_151
  have hlo := exp_neg_ge_of (q := (2881724848014023 / 1000000000000000 : ℝ)) (a := (3487629595413680493 / 5000000000000000000 : ℝ)) (lo := (7004752794403 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2881724846821651 / 1000000000000000 : ℝ)) (b := (69752591918672148317 / 100000000000000000000 : ℝ)) (hi := (56038022422057 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_152 : (6978246869561 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 152 ∧ ex (57436 / 100000) 152 ≤ (55825975023069 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_152
  have hlo := exp_neg_ge_of (q := (2885516016894271 / 1000000000000000 : ℝ)) (a := (4357471516093669973 / 6250000000000000000 : ℝ)) (lo := (6978246869561 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2885516015701899 / 1000000000000000 : ℝ)) (b := (69719544267892366717 / 100000000000000000000 : ℝ)) (hi := (55825975023069 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_153 : (55616112559501 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 153 ∧ ex (57436 / 100000) 153 ≤ (55616112625831 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_153
  have hlo := exp_neg_ge_of (q := (2889282325471963 / 1000000000000000 : ℝ)) (a := (69686728817975527589 / 100000000000000000000 : ℝ)) (lo := (55616112559501 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (288928232427959 / 100000000000000 : ℝ)) (b := (3484336441418216351 / 5000000000000000000 : ℝ)) (hi := (55616112625831 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_154 : (11081679717533 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 154 ∧ ex (57436 / 100000) 154 ≤ (13852099663437 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_154
  have hlo := exp_neg_ge_of (q := (578604819532659 / 200000000000000 : ℝ)) (a := (34827071228120718699 / 50000000000000000000 : ℝ)) (lo := (11081679717533 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2893024096470923 / 1000000000000000 : ℝ)) (b := (69654142466625406103 / 100000000000000000000 : ℝ)) (hi := (13852099663437 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_156 : (10999854762289 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 156 ∧ ex (57436 / 100000) 156 ≤ (687490923463 / 12500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_156
  have hlo := exp_neg_ge_of (q := (2900435297264847 / 1000000000000000 : ℝ)) (a := (69589644742091440867 / 100000000000000000000 : ℝ)) (lo := (10999854762289 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (116017411842899 / 40000000000000 : ℝ)) (b := (13917928950493173391 / 20000000000000000000 : ℝ)) (hi := (687490923463 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_157 : (27398896989363 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 157 ∧ ex (57436 / 100000) 157 ≤ (54797794044081 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_157
  have hlo := exp_neg_ge_of (q := (1452052670850429 / 500000000000000 : ℝ)) (a := (34778863713856294907 / 50000000000000000000 : ℝ)) (lo := (27398896989363 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (580821068101697 / 200000000000000 : ℝ)) (b := (34778863719041151553 / 50000000000000000000 : ℝ)) (hi := (54797794044081 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_158 : (6824790558437 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 158 ∧ ex (57436 / 100000) 158 ≤ (27299162266307 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_158
  have hlo := exp_neg_ge_of (q := (726938021027593 / 250000000000000 : ℝ)) (a := (69526027264092161099 / 100000000000000000000 : ℝ)) (lo := (6824790558437 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1453876041459 / 500000000000 : ℝ)) (b := (1738150681861429421 / 2500000000000000000 : ℝ)) (hi := (27299162266307 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_159 : (13600208171241 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 159 ∧ ex (57436 / 100000) 159 ≤ (27200416374923 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_159
  have hlo := exp_neg_ge_of (q := (363921977316027 / 125000000000000 : ℝ)) (a := (34747270706705710637 / 50000000000000000000 : ℝ)) (lo := (13600208171241 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2911375817335843 / 1000000000000000 : ℝ)) (b := (13898908284754357811 / 20000000000000000000 : ℝ)) (hi := (27200416374923 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_161 : (5401165555953 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 161 ∧ ex (57436 / 100000) 161 ≤ (54011655623949 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_161
  have hlo := exp_neg_ge_of (q := (72963885300337 / 25000000000000 : ℝ)) (a := (69432201571416544173 / 100000000000000000000 : ℝ)) (lo := (5401165555953 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2918555410821107 / 1000000000000000 : ℝ)) (b := (1084878149715120213 / 1562500000000000000 : ℝ)) (hi := (54011655623949 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_162 : (10763981718847 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 162 ∧ ex (57436 / 100000) 162 ≤ (26909954329213 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_162
  have hlo := exp_neg_ge_of (q := (730527958011269 / 250000000000000 : ℝ)) (a := (69401342172173031119 / 100000000000000000000 : ℝ)) (lo := (10763981718847 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2922111830852703 / 1000000000000000 : ℝ)) (b := (694013421825196181 / 1000000000000000000 : ℝ)) (hi := (26909954329213 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_163 : (13407504018371 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 163 ∧ ex (57436 / 100000) 163 ≤ (6703752017181 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_163
  have hlo := exp_neg_ge_of (q := (23405170930211 / 8000000000000 : ℝ)) (a := (69370686267367522217 / 100000000000000000000 : ℝ)) (lo := (13407504018371 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2925646365084003 / 1000000000000000 : ℝ)) (b := (13874137255541913729 / 20000000000000000000 : ℝ)) (hi := (6703752017181 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_164 : (53441948849507 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 164 ∧ ex (57436 / 100000) 164 ≤ (53441948913247 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_164
  have hlo := exp_neg_ge_of (q := (292915928242611 / 100000000000000 : ℝ)) (a := (13868046255791457027 / 20000000000000000000 : ℝ)) (lo := (53441948849507 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1464579640616869 / 500000000000000 : ℝ)) (b := (8667528911161853737 / 12500000000000000000 : ℝ)) (hi := (53441948913247 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_166 : (26535588422287 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 166 ∧ ex (57436 / 100000) 166 ≤ (1658474278371 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_166
  have hlo := exp_neg_ge_of (q := (734030326765367 / 250000000000000 : ℝ)) (a := (34639956989311963443 / 50000000000000000000 : ℝ)) (lo := (26535588422287 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (587224261173819 / 200000000000000 : ℝ)) (b := (69279913988952566109 / 100000000000000000000 : ℝ)) (hi := (1658474278371 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_167 : (52888416860091 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 167 ∧ ex (57436 / 100000) 167 ≤ (13222104230793 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_167
  have hlo := exp_neg_ge_of (q := (2939570927040691 / 1000000000000000 : ℝ)) (a := (34625023373285878971 / 50000000000000000000 : ℝ)) (lo := (52888416860091 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2939570925848319 / 1000000000000000 : ℝ)) (b := (69250046756895975239 / 100000000000000000000 : ℝ)) (hi := (13222104230793 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_168 : (13176842933043 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 168 ∧ ex (57436 / 100000) 168 ≤ (52707371795037 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_168
  have hlo := exp_neg_ge_of (q := (2942999952151059 / 1000000000000000 : ℝ)) (a := (13844074117679154221 / 20000000000000000000 : ℝ)) (lo := (13176842933043 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2942999950958687 / 1000000000000000 : ℝ)) (b := (69220370598715603879 / 100000000000000000000 : ℝ)) (hi := (52707371795037 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_169 : (2101120612221 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 169 ∧ ex (57436 / 100000) 169 ≤ (3283000960511 / 62500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_169
  have hlo := exp_neg_ge_of (q := (147320431342211 / 50000000000000 : ℝ)) (a := (13838176631044812601 / 20000000000000000000 : ℝ)) (lo := (2101120612221 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (368301078206481 / 125000000000000 : ℝ)) (b := (69190883165539539649 / 100000000000000000000 : ℝ)) (hi := (3283000960511 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_171 : (208697066693 / 4000000000000 : ℝ) ≤ ex (57436 / 100000) 171 ∧ ex (57436 / 100000) 171 ≤ (1304356668387 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_171
  have hlo := exp_neg_ge_of (q := (2953165881253871 / 1000000000000000 : ℝ)) (a := (13826493056037268847 / 20000000000000000000 : ℝ)) (lo := (208697066693 / 4000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2953165880061499 / 1000000000000000 : ℝ)) (b := (69132465290493192429 / 100000000000000000000 : ℝ)) (hi := (1304356668387 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_172 : (51999824851649 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 172 ∧ ex (57436 / 100000) 172 ≤ (5199982491367 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_172
  have hlo := exp_neg_ge_of (q := (1478257464321789 / 500000000000000 : ℝ)) (a := (34551765174669233741 / 50000000000000000000 : ℝ)) (lo := (51999824851649 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1478257463725603 / 500000000000000 : ℝ)) (b := (34551765179820521343 / 50000000000000000000 : ℝ)) (hi := (5199982491367 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_173 : (51826972471289 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 173 ∧ ex (57436 / 100000) 173 ≤ (10365394506621 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_173
  have hlo := exp_neg_ge_of (q := (739961140289187 / 250000000000000 : ℝ)) (a := (69074775163587862477 / 100000000000000000000 : ℝ)) (lo := (51826972471289 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (369980569995547 / 125000000000000 : ℝ)) (b := (13814955034777238349 / 20000000000000000000 : ℝ)) (hi := (10365394506621 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_174 : (25827842993609 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 174 ∧ ex (57436 / 100000) 174 ≤ (5165568604883 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_174
  have hlo := exp_neg_ge_of (q := (148157750129893 / 50000000000000 : ℝ)) (a := (34523098788496333951 / 50000000000000000000 : ℝ)) (lo := (25827842993609 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (185197187587843 / 62500000000000 : ℝ)) (b := (34523098793643388983 / 50000000000000000000 : ℝ)) (hi := (5165568604883 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_176 : (1026354378461 / 20000000000000 : ℝ) ≤ ex (57436 / 100000) 176 ∧ ex (57436 / 100000) 176 ≤ (2565885949213 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_176
  have hlo := exp_neg_ge_of (q := (742429797082779 / 250000000000000 : ℝ)) (a := (34494783402733724129 / 50000000000000000000 : ℝ)) (lo := (1026354378461 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (371214898392343 / 125000000000000 : ℝ)) (b := (34494783407876599431 / 50000000000000000000 : ℝ)) (hi := (2565885949213 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_177 : (51150993610781 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 177 ∧ ex (57436 / 100000) 177 ≤ (51150993671791 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_177
  have hlo := exp_neg_ge_of (q := (743243340335527 / 250000000000000 : ℝ)) (a := (34480754757008509323 / 50000000000000000000 : ℝ)) (lo := (51150993610781 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (371621670018717 / 125000000000000 : ℝ)) (b := (3448075476214931419 / 5000000000000000000 : ℝ)) (hi := (51150993671791 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_178 : (12746436176641 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 178 ∧ ex (57436 / 100000) 178 ≤ (25492872383689 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_178
  have hlo := exp_neg_ge_of (q := (595241840177353 / 200000000000000 : ℝ)) (a := (34466810803501813273 / 50000000000000000000 : ℝ)) (lo := (12746436176641 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2976209199694393 / 1000000000000000 : ℝ)) (b := (68933621617281120919 / 100000000000000000000 : ℝ)) (hi := (25492872383689 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_179 : (50821950951489 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 179 ∧ ex (57436 / 100000) 179 ≤ (50821951012107 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_179
  have hlo := exp_neg_ge_of (q := (2979426912383699 / 1000000000000000 : ℝ)) (a := (68905901118814372767 / 100000000000000000000 : ℝ)) (lo := (50821950951489 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2979426911191327 / 1000000000000000 : ℝ)) (b := (2153309410283993031 / 3125000000000000000 : ℝ)) (hi := (50821951012107 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_181 : (25249322977837 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 181 ∧ ex (57436 / 100000) 181 ≤ (12624661503977 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_181
  have hlo := exp_neg_ge_of (q := (2985808755818843 / 1000000000000000 : ℝ)) (a := (68850954703854539003 / 100000000000000000000 : ℝ)) (lo := (25249322977837 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2985808754626471 / 1000000000000000 : ℝ)) (b := (68850954714119837427 / 100000000000000000000 : ℝ)) (hi := (12624661503977 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_182 : (50339094267921 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 182 ∧ ex (57436 / 100000) 182 ≤ (10067818865593 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_182
  have hlo := exp_neg_ge_of (q := (23351353763519 / 7812500000000 : ℝ)) (a := (68823725011001594143 / 100000000000000000000 : ℝ)) (lo := (50339094267921 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2988973280538059 / 1000000000000000 : ℝ)) (b := (13764745004252576991 / 20000000000000000000 : ℝ)) (hi := (10067818865593 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_183 : (50180916814863 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 183 ∧ ex (57436 / 100000) 183 ≤ (25090458437359 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_183
  have hlo := exp_neg_ge_of (q := (1496060233843501 / 500000000000000 : ℝ)) (a := (34398327601676945033 / 50000000000000000000 : ℝ)) (lo := (50180916814863 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (299212046649463 / 100000000000000 : ℝ)) (b := (17199163803402795037 / 25000000000000000000 : ℝ)) (hi := (25090458437359 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_184 : (25012047173563 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 184 ∧ ex (57436 / 100000) 184 ≤ (10004818881359 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_184
  have hlo := exp_neg_ge_of (q := (29952505026813 / 10000000000000 : ℝ)) (a := (171924358690195041 / 250000000000000000 : ℝ)) (lo := (25012047173563 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (93601578171529 / 31250000000000 : ℝ)) (b := (1074527241973927159 / 1562500000000000000 : ℝ)) (hi := (10004818881359 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_186 : (1988577568907 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 186 ∧ ex (57436 / 100000) 186 ≤ (24857219640987 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_186
  have hlo := exp_neg_ge_of (q := (1500729930227459 / 500000000000000 : ℝ)) (a := (17179096798216743911 / 25000000000000000000 : ℝ)) (lo := (1988577568907 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (600291971852509 / 200000000000000 : ℝ)) (b := (34358193601556219903 / 50000000000000000000 : ℝ)) (hi := (24857219640987 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_187 : (24780784946269 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 187 ∧ ex (57436 / 100000) 187 ≤ (9912313990331 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_187
  have hlo := exp_neg_ge_of (q := (751134886529401 / 250000000000000 : ℝ)) (a := (13737987834972747733 / 20000000000000000000 : ℝ)) (lo := (24780784946269 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (187783721557827 / 62500000000000 : ℝ)) (b := (68689939185105295821 / 100000000000000000000 : ℝ)) (hi := (9912313990331 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_188 : (49409982183353 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 188 ∧ ex (57436 / 100000) 188 ≤ (4940998224229 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_188
  have hlo := exp_neg_ge_of (q := (3007602806712013 / 1000000000000000 : ℝ)) (a := (429147764448941717 / 625000000000000000 : ℝ)) (lo := (49409982183353 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3007602805519641 / 1000000000000000 : ℝ)) (b := (68663642322068356247 / 100000000000000000000 : ℝ)) (hi := (4940998224229 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_189 : (615745732731 / 12500000000000 : ℝ) ≤ ex (57436 / 100000) 189 ∧ ex (57436 / 100000) 189 ≤ (24629829338619 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_189
  have hlo := exp_neg_ge_of (q := (150532490825533 / 50000000000000 : ℝ)) (a := (17159373735683867967 / 25000000000000000000 : ℝ)) (lo := (615745732731 / 12500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3010649815318287 / 1000000000000000 : ℝ)) (b := (17159373738242327221 / 25000000000000000000 : ℝ)) (hi := (24629829338619 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_191 : (24481367826481 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 191 ∧ ex (57436 / 100000) 191 ≤ (24481367855683 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_191
  have hlo := exp_neg_ge_of (q := (1508347883536933 / 500000000000000 : ℝ)) (a := (17146410544064128389 / 25000000000000000000 : ℝ)) (lo := (24481367826481 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1508347882940747 / 500000000000000 : ℝ)) (b := (68585642186482702457 / 100000000000000000000 : ℝ)) (hi := (24481367855683 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_192 : (48816102913439 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 192 ∧ ex (57436 / 100000) 192 ≤ (12204025742917 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_192
  have hlo := exp_neg_ge_of (q := (9436547008809 / 3125000000000 : ℝ)) (a := (68559933589124528829 / 100000000000000000000 : ℝ)) (lo := (48816102913439 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (754923760406627 / 250000000000000 : ℝ)) (b := (8569991699918366351 / 12500000000000000000 : ℝ)) (hi := (12204025742917 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_193 : (12167666906343 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 193 ∧ ex (57436 / 100000) 193 ≤ (12167666920857 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_193
  have hlo := exp_neg_ge_of (q := (3022678737840413 / 1000000000000000 : ℝ)) (a := (8566796014416071863 / 12500000000000000000 : ℝ)) (lo := (12167666906343 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3022678736648041 / 1000000000000000 : ℝ)) (b := (68534368125547211549 / 100000000000000000000 : ℝ)) (hi := (12167666920857 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_194 : (24263206940599 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 194 ∧ ex (57436 / 100000) 194 ≤ (24263206969541 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_194
  have hlo := exp_neg_ge_of (q := (3025647013180617 / 1000000000000000 : ℝ)) (a := (68508944222835620883 / 100000000000000000000 : ℝ)) (lo := (24263206940599 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (756411752997061 / 250000000000000 : ℝ)) (b := (34254472116525261057 / 50000000000000000000 : ℝ)) (hi := (24263206969541 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_196 : (48241388846993 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 196 ∧ ex (57436 / 100000) 196 ≤ (24120694452269 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_196
  have hlo := exp_neg_ge_of (q := (3031537936616643 / 1000000000000000 : ℝ)) (a := (34229257587040418683 / 50000000000000000000 : ℝ)) (lo := (48241388846993 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3031537935424271 / 1000000000000000 : ℝ)) (b := (13691703036857661051 / 20000000000000000000 : ℝ)) (hi := (24120694452269 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_197 : (24050293587141 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 197 ∧ ex (57436 / 100000) 197 ≤ (48100587231659 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_197
  have hlo := exp_neg_ge_of (q := (1517230447289477 / 500000000000000 : ℝ)) (a := (2737340282908352113 / 4000000000000000000 : ℝ)) (lo := (24050293587141 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1517230446693291 / 500000000000000 : ℝ)) (b := (68433507082912589473 / 100000000000000000000 : ℝ)) (hi := (48100587231659 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_198 : (11990226566759 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 198 ∧ ex (57436 / 100000) 198 ≤ (47960906324247 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_198
  have hlo := exp_neg_ge_of (q := (3037369052690717 / 1000000000000000 : ℝ)) (a := (8551079332681307103 / 12500000000000000000 : ℝ)) (lo := (11990226566759 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (379671131437293 / 125000000000000 : ℝ)) (b := (68408634671650591261 / 100000000000000000000 : ℝ)) (hi := (47960906324247 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_199 : (1912893264437 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 199 ∧ ex (57436 / 100000) 199 ≤ (47822331667971 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_199
  have hlo := exp_neg_ge_of (q := (3040262560069763 / 1000000000000000 : ℝ)) (a := (68383896524321069481 / 100000000000000000000 : ℝ)) (lo := (1912893264437 / 40000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3040262558877391 / 1000000000000000 : ℝ)) (b := (68383896534517554871 / 100000000000000000000 : ℝ)) (hi := (47822331667971 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_201 : (23774222143617 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 201 ∧ ex (57436 / 100000) 201 ≤ (23774222171977 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_201
  have hlo := exp_neg_ge_of (q := (1523003103966907 / 500000000000000 : ℝ)) (a := (34167408758530847667 / 50000000000000000000 : ℝ)) (lo := (23774222143617 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1523003103370721 / 500000000000000 : ℝ)) (b := (68334817527250959703 / 100000000000000000000 : ℝ)) (hi := (23774222171977 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_202 : (47413103865863 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 202 ∧ ex (57436 / 100000) 202 ≤ (23706551961211 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_202
  have hlo := exp_neg_ge_of (q := (3048856635620359 / 1000000000000000 : ℝ)) (a := (17077618480549258433 / 25000000000000000000 : ℝ)) (lo := (47413103865863 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3048856634427987 / 1000000000000000 : ℝ)) (b := (6831047393238271717 / 10000000000000000000 : ℝ)) (hi := (23706551961211 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_203 : (23639407088349 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 203 ∧ ex (57436 / 100000) 203 ≤ (5909851779137 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_203
  have hlo := exp_neg_ge_of (q := (762923246765861 / 250000000000000 : ℝ)) (a := (68286259151139811239 / 100000000000000000000 : ℝ)) (lo := (23639407088349 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (95365405808471 / 31250000000000 : ℝ)) (b := (34143129580660966599 / 50000000000000000000 : ℝ)) (hi := (5909851779137 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_204 : (23572780973113 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 204 ∧ ex (57436 / 100000) 204 ≤ (23572781001233 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_204
  have hlo := exp_neg_ge_of (q := (381814425075671 / 125000000000000 : ℝ)) (a := (68262171892582965153 / 100000000000000000000 : ℝ)) (lo := (23572780973113 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (610903079882599 / 200000000000000 : ℝ)) (b := (68262171902761553423 / 100000000000000000000 : ℝ)) (hi := (23572781001233 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_206 : (46882117920561 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 206 ∧ ex (57436 / 100000) 206 ≤ (46882117976487 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_206
  have hlo := exp_neg_ge_of (q := (3060118957246987 / 1000000000000000 : ℝ)) (a := (34107187382910629393 / 50000000000000000000 : ℝ)) (lo := (46882117920561 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (612023791210923 / 200000000000000 : ℝ)) (b := (17053593693998202771 / 25000000000000000000 : ℝ)) (hi := (46882117976487 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_207 : (4675190071627 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 207 ∧ ex (57436 / 100000) 207 ≤ (46751900772041 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_207
  have hlo := exp_neg_ge_of (q := (3062900367040901 / 1000000000000000 : ℝ)) (a := (34095331185960219633 / 50000000000000000000 : ℝ)) (lo := (4675190071627 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3062900365848529 / 1000000000000000 : ℝ)) (b := (4261916398880531623 / 6250000000000000000 : ℝ)) (hi := (46751900772041 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_208 : (46622670142593 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 208 ∧ ex (57436 / 100000) 208 ≤ (4662267019821 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_208
  have hlo := exp_neg_ge_of (q := (766417093099563 / 250000000000000 : ℝ)) (a := (13633414487675257329 / 20000000000000000000 : ℝ)) (lo := (46622670142593 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (76641709280147 / 25000000000000 : ℝ)) (b := (34083536224270443127 / 50000000000000000000 : ℝ)) (hi := (4662267019821 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_209 : (1452950438571 / 31250000000000 : ℝ) ≤ ex (57436 / 100000) 209 ∧ ex (57436 / 100000) 209 ≤ (46494414089737 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_209
  have hlo := exp_neg_ge_of (q := (383552887737439 / 125000000000000 : ℝ)) (a := (6814360374854382999 / 10000000000000000000 : ℝ)) (lo := (1452950438571 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (153421155035357 / 50000000000000 : ℝ)) (b := (68143603758704980827 / 100000000000000000000 : ℝ)) (hi := (46494414089737 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

end PsiOmega.Locate.Z3

#print axioms PsiOmega.Locate.Z3.exB_209
