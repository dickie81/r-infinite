import DHLocate2Trig

/-! # Generated (`gen_locate_zero.py 2`): the interval evaluation of `PReG cZ 28 12`, `PImG cZ 28 12`, `AReG cZ 28 12`

The three open inequalities of `DHLocate2Base` (`H1`, `H2`, `H3`) from the atom bounds of `DHLocate2Exp` /
`DHLocate2Trig`, `κ` (`PsiOmega.kappa_bounds`) and `log n` (`PsiOmega.Num.log_bound_n`), by interval products
(`mul_bounds_of`) and block sums; then `dh_zero_located` = `dh_zero_near_of_center' H1 H2 H3`. -/

open Real Finset

namespace PsiOmega.Locate.Z2

theorem lgB_2 : (346573590228867 / 500000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (138629436131547 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_2
  constructor <;> linarith [h.1, h.2]

theorem eC_2 : (-528463509630723 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 2 * cCG cZ 2 ∧ ex (65083 / 100000) 2 * cCG cZ 2 ≤ (-21138539784927 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 cCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_2 : (-30025081704089 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 2 * cCG cZ 2) ∧ kappa * (ex (65083 / 100000) 2 * cCG cZ 2) ≤ (-75062702128557 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_2 : (-355507384569073 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 2 * sCG cZ 2 ∧ ex (65083 / 100000) 2 * sCG cZ 2 ≤ (-177753684793199 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 sCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_2 : (-100992197886589 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 2 * sCG cZ 2) ∧ kappa * (ex (65083 / 100000) 2 * sCG cZ 2) ≤ (-100992193630323 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_2 : (-91575747945257 / 250000000000000 : ℝ) ≤ Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2) ∧ Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2) ≤ (-183151490636447 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_2 eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_2 : (-52029501830519 / 500000000000000 : ℝ) ≤ kappa * (Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2)) ∧ kappa * (Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2)) ≤ (-13007375084487 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_3 : (1098612288561369 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288829637 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_3
  constructor <;> linarith [h.1, h.2]

theorem eC_3 : (237439475734321 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 3 * cCG cZ 3 ∧ ex (65083 / 100000) 3 * cCG cZ 3 ≤ (474878966600887 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 cCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_3 : (134903158473149 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 3 * cCG cZ 3) ∧ kappa * (ex (65083 / 100000) 3 * cCG cZ 3) ≤ (2107861918311 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_3 : (-5872433633493 / 50000000000000 : ℝ) ≤ ex (65083 / 100000) 3 * sCG cZ 3 ∧ ex (65083 / 100000) 3 * sCG cZ 3 ≤ (-117448657600023 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 sCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_3 : (-1668235331619 / 50000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 3 * sCG cZ 3) ∧ kappa * (ex (65083 / 100000) 3 * sCG cZ 3) ≤ (-16682351175677 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_3 : (130426962915647 / 250000000000000 : ℝ) ≤ Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3) ∧ Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3) ≤ (260853934207227 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_3 eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_3 : (148206267664343 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3)) ∧ kappa * (Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3)) ≤ (148206272423199 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_4 : (693147180505767 / 500000000000000 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (693147180650437 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_4
  constructor <;> linarith [h.1, h.2]

theorem eC_4 : (152888169212651 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 4 * cCG cZ 4 ∧ ex (65083 / 100000) 4 * cCG cZ 4 ≤ (19111022878203 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 cCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_4 : (375745340841509 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 4 * sCG cZ 4 ∧ ex (65083 / 100000) 4 * sCG cZ 4 ≤ (187872677348229 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 sCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_4 : (1695584054759 / 8000000000000 : ℝ) ≤ Real.log 4 * (ex (65083 / 100000) 4 * cCG cZ 4) ∧ Real.log 4 * (ex (65083 / 100000) 4 * cCG cZ 4) ≤ (211948026037959 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_4 eC_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_6 : (1791759469113201 / 1000000000000000 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (1791759469474139 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_6
  constructor <;> linarith [h.1, h.2]

theorem eC_6 : (-292710070618833 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 6 * cCG cZ 6 ∧ ex (65083 / 100000) 6 * cCG cZ 6 ≤ (-146355028811009 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 cCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_6 : (-6672228012231 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 6 * sCG cZ 6 ∧ ex (65083 / 100000) 6 * sCG cZ 6 ≤ (-53377817621283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 sCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_6 : (-262233020420869 / 500000000000000 : ℝ) ≤ Real.log 6 * (ex (65083 / 100000) 6 * cCG cZ 6) ∧ Real.log 6 * (ex (65083 / 100000) 6 * cCG cZ 6) ≤ (-524466017448921 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_6 eC_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_7 : (972955074470179 / 500000000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (972955074651209 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_7
  constructor <;> linarith [h.1, h.2]

theorem eC_7 : (-43715312136459 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 7 * cCG cZ 7 ∧ ex (65083 / 100000) 7 * cCG cZ 7 ≤ (-174861236582091 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 cCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_7 : (-24837208145821 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 7 * cCG cZ 7) ∧ kappa * (ex (65083 / 100000) 7 * cCG cZ 7) ≤ (-776162701453 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_7 : (221022221198499 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 7 * sCG cZ 7 ∧ ex (65083 / 100000) 7 * sCG cZ 7 ≤ (6906944786801 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_7 sCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_7 : (62787781265553 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 7 * sCG cZ 7) ∧ kappa * (ex (65083 / 100000) 7 * sCG cZ 7) ≤ (2511511386743 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_7 : (-68052855653007 / 200000000000000 : ℝ) ≤ Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7) ∧ Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7) ≤ (-340264254921351 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_7 eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_7 : (-4833097541129 / 50000000000000 : ℝ) ≤ kappa * (Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7)) ∧ kappa * (Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7)) ≤ (-96661944191127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_8 : (2079441541559079 / 1000000000000000 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (519860385493349 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_8
  constructor <;> linarith [h.1, h.2]

theorem eC_8 : (52784417636119 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 8 * cCG cZ 8 ∧ ex (65083 / 100000) 8 * cCG cZ 8 ≤ (13196107499607 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 cCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_8 : (14994946891741 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 8 * cCG cZ 8) ∧ kappa * (ex (65083 / 100000) 8 * cCG cZ 8) ≤ (2998990080723 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_8 : (-252920582698731 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 8 * sCG cZ 8 ∧ ex (65083 / 100000) 8 * sCG cZ 8 ≤ (-50584114056491 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 sCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_8 : (-8981179662577 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 8 * sCG cZ 8) ∧ kappa * (ex (65083 / 100000) 8 * sCG cZ 8) ≤ (-71849433773411 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_8 : (109762110779549 / 1000000000000000 : ℝ) ≤ Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8) ∧ Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8) ≤ (54881068254059 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_8 eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_8 : (31181115480159 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8)) ∧ kappa * (Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8)) ≤ (7795280697277 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_9 : (2197224577213583 / 1000000000000000 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (274653072205603 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_9
  constructor <;> linarith [h.1, h.2]

theorem eC_9 : (211715831259047 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 9 * cCG cZ 9 ∧ ex (65083 / 100000) 9 * cCG cZ 9 ≤ (211715843206649 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 cCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_9 : (-1742934449823 / 15625000000000 : ℝ) ≤ ex (65083 / 100000) 9 * sCG cZ 9 ∧ ex (65083 / 100000) 9 * sCG cZ 9 ≤ (-55773896434633 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 sCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_9 : (465187227827581 / 1000000000000000 : ℝ) ≤ Real.log 9 * (ex (65083 / 100000) 9 * cCG cZ 9) ∧ Real.log 9 * (ex (65083 / 100000) 9 * cCG cZ 9) ≤ (29074203385653 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_9 eC_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_11 : (2397895272674763 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895273114743 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_11
  constructor <;> linarith [h.1, h.2]

theorem eC_11 : (-47652249921949 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 11 * cCG cZ 11 ∧ ex (65083 / 100000) 11 * cCG cZ 11 ≤ (-2978265451591 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_11 cCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_11 : (-17630050913499 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 11 * sCG cZ 11 ∧ ex (65083 / 100000) 11 * sCG cZ 11 ≤ (-88150243810881 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 sCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_11 : (-28566276210281 / 62500000000000 : ℝ) ≤ Real.log 11 * (ex (65083 / 100000) 11 * cCG cZ 11) ∧ Real.log 11 * (ex (65083 / 100000) 11 * cCG cZ 11) ≤ (-457060393417 / 1000000000000 : ℝ) := by
  exact mul_bounds_of lgB_11 eC_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_12 : (248490664966427 / 100000000000000 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ (1242453325052681 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_12
  constructor <;> linarith [h.1, h.2]

theorem eC_12 : (29183540438979 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 12 * cCG cZ 12 ∧ ex (65083 / 100000) 12 * cCG cZ 12 ≤ (116734171855783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 cCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_12 : (8290432263783 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 12 * cCG cZ 12) ∧ kappa * (ex (65083 / 100000) 12 * cCG cZ 12) ≤ (16580865962147 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_12 : (160477042816307 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 12 * sCG cZ 12 ∧ ex (65083 / 100000) 12 * sCG cZ 12 ≤ (160477052930241 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 sCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_12 : (45588164881593 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 12 * sCG cZ 12) ∧ kappa * (ex (65083 / 100000) 12 * sCG cZ 12) ≤ (45588167754751 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_12 : (14503674739513 / 50000000000000 : ℝ) ≤ Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12) ∧ Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12) ≤ (145036759969489 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_12 eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_12 : (82403801043463 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12)) ∧ kappa * (Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12)) ≤ (10300476023461 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_13 : (641237339334437 / 250000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (512989871555873 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_13
  constructor <;> linarith [h.1, h.2]

theorem eC_13 : (-149378722840569 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 13 * cCG cZ 13 ∧ ex (65083 / 100000) 13 * cCG cZ 13 ≤ (-149378713256139 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 cCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_13 : (-42435364754651 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 13 * cCG cZ 13) ∧ kappa * (ex (65083 / 100000) 13 * cCG cZ 13) ≤ (-8487072406383 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_13 : (-14344718085233 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 13 * sCG cZ 13 ∧ ex (65083 / 100000) 13 * sCG cZ 13 ≤ (-28689433777429 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 sCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_13 : (-32600270382507 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 13 * sCG cZ 13) ∧ kappa * (ex (65083 / 100000) 13 * sCG cZ 13) ≤ (-32600267663259 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_13 : (-19157442960791 / 50000000000000 : ℝ) ≤ Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13) ∧ Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13) ≤ (-383148834566273 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_13 eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_13 : (-6802785098411 / 62500000000000 : ℝ) ≤ kappa * (Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13)) ∧ kappa * (Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13)) ≤ (-21768910914431 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_14 : (32988216618643 / 12500000000000 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ (65976433248333 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_14
  constructor <;> linarith [h.1, h.2]

theorem eC_14 : (10686425782287 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 14 * cCG cZ 14 ∧ ex (65083 / 100000) 14 * cCG cZ 14 ≤ (170982821683223 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 cCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_14 : (-10927544489849 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 14 * sCG cZ 14 ∧ ex (65083 / 100000) 14 * sCG cZ 14 ≤ (-2185508532643 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 sCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_14 : (112808361147243 / 250000000000000 : ℝ) ≤ Real.log 14 * (ex (65083 / 100000) 14 * cCG cZ 14) ∧ Real.log 14 * (ex (65083 / 100000) 14 * cCG cZ 14) ≤ (28202091803487 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_14 eC_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_16 : (1386294361052777 / 500000000000000 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (1386294361310171 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_16
  constructor <;> linarith [h.1, h.2]

theorem eC_16 : (-14726222209397 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 16 * cCG cZ 16 ∧ ex (65083 / 100000) 16 * cCG cZ 16 ≤ (-117809767856091 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 cCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_16 : (114894036080679 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 16 * sCG cZ 16 ∧ ex (65083 / 100000) 16 * sCG cZ 16 ≤ (11489404588411 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 sCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_16 : (-326638060996603 / 1000000000000000 : ℝ) ≤ Real.log 16 * (ex (65083 / 100000) 16 * cCG cZ 16) ∧ Real.log 16 * (ex (65083 / 100000) 16 * cCG cZ 16) ≤ (-326638033711671 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_16 eC_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_17 : (2833213343915281 / 1000000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344477039 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_17
  constructor <;> linarith [h.1, h.2]

theorem eC_17 : (-39188677365933 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 17 * cCG cZ 17 ∧ ex (65083 / 100000) 17 * cCG cZ 17 ≤ (-39188674795161 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 cCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_17 : (-44530727981939 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 17 * cCG cZ 17) ∧ kappa * (ex (65083 / 100000) 17 * cCG cZ 17) ≤ (-5566340632591 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_17 : (21282604310481 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 17 * sCG cZ 17 ∧ ex (65083 / 100000) 17 * sCG cZ 17 ≤ (21282614544039 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 sCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_17 : (1209188376591 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 17 * sCG cZ 17) ∧ kappa * (ex (65083 / 100000) 17 * sCG cZ 17) ≤ (1209188958019 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_17 : (-444119534662267 / 1000000000000000 : ℝ) ≤ Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17) ∧ Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17) ≤ (-222059752720013 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_17 eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_17 : (-63082526378853 / 500000000000000 : ℝ) ≤ kappa * (Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17)) ∧ kappa * (Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17)) ≤ (-126165044456279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_18 : (1445185878875393 / 500000000000000 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ (578074351668731 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_18
  constructor <;> linarith [h.1, h.2]

theorem eC_18 : (-75770081655421 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 18 * cCG cZ 18 ∧ ex (65083 / 100000) 18 * cCG cZ 18 ≤ (-75770076404991 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 cCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_18 : (-8609876939353 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 18 * cCG cZ 18) ∧ kappa * (ex (65083 / 100000) 18 * cCG cZ 18) ≤ (-43049381713689 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_18 : (-2039700980141 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 18 * sCG cZ 18 ∧ ex (65083 / 100000) 18 * sCG cZ 18 ≤ (-3263519478489 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 sCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_18 : (-4635490433271 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 18 * sCG cZ 18) ∧ kappa * (ex (65083 / 100000) 18 * sCG cZ 18) ≤ (-2317743732509 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_18 : (-109501852072111 / 250000000000000 : ℝ) ≤ Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18) ∧ Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18) ≤ (-43800737784721 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_18 eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_18 : (-124428725741599 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18)) ∧ kappa * (Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18)) ≤ (-124428717093881 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_19 : (58888779580361 / 20000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (1472219489816001 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_19
  constructor <;> linarith [h.1, h.2]

theorem eC_19 : (-73572627342421 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 19 * cCG cZ 19 ∧ ex (65083 / 100000) 19 * cCG cZ 19 ≤ (-147145244261861 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 cCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_19 : (504061676201 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 19 * sCG cZ 19 ∧ ex (65083 / 100000) 19 * sCG cZ 19 ≤ (252036020293 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 sCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_19 : (-54157527945241 / 125000000000000 : ℝ) ≤ Real.log 19 * (ex (65083 / 100000) 19 * cCG cZ 19) ∧ Real.log 19 * (ex (65083 / 100000) 19 * cCG cZ 19) ≤ (-86652038556351 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_19 eC_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_21 : (1522261218785741 / 500000000000000 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ (3044522438210293 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_21
  constructor <;> linarith [h.1, h.2]

theorem eC_21 : (-14269791337651 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 21 * cCG cZ 21 ∧ ex (65083 / 100000) 21 * cCG cZ 21 ≤ (-11415831048643 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 cCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_21 : (62748009582061 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 21 * sCG cZ 21 ∧ ex (65083 / 100000) 21 * sCG cZ 21 ≤ (125496029299967 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 sCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_21 : (-17377879966423 / 100000000000000 : ℝ) ≤ Real.log 21 * (ex (65083 / 100000) 21 * cCG cZ 21) ∧ Real.log 21 * (ex (65083 / 100000) 21 * cCG cZ 21) ≤ (-173778768855593 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_21 eC_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_22 : (3091042453205323 / 1000000000000000 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ (386380306731437 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_22
  constructor <;> linarith [h.1, h.2]

theorem eC_22 : (69391826793023 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 22 * cCG cZ 22 ∧ ex (65083 / 100000) 22 * cCG cZ 22 ≤ (34695918378553 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 cCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_22 : (19712763805701 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 22 * cCG cZ 22) ∧ kappa * (ex (65083 / 100000) 22 * cCG cZ 22) ≤ (19712766636289 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_22 : (114347088622137 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 22 * sCG cZ 22 ∧ ex (65083 / 100000) 22 * sCG cZ 22 ≤ (446668353927 / 3906250000000 : ℝ) := by
  exact mul_bounds_of exB_22 sCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_22 : (32483611601711 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 22 * sCG cZ 22) ∧ kappa * (ex (65083 / 100000) 22 * sCG cZ 22) ≤ (32483614437723 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_22 : (13405817657669 / 62500000000000 : ℝ) ≤ Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22) ∧ Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22) ≤ (53623278341737 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_22 eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_22 : (7616623724179 / 125000000000000 : ℝ) ≤ kappa * (Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22)) ∧ kappa * (Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22)) ≤ (15233249638909 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_23 : (97984194242981 / 31250000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (78387355410673 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_23
  constructor <;> linarith [h.1, h.2]

theorem eC_23 : (127769739502889 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 23 * cCG cZ 23 ∧ ex (65083 / 100000) 23 * cCG cZ 23 ≤ (25553949867649 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 cCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_23 : (36296705429719 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 23 * cCG cZ 23) ∧ kappa * (ex (65083 / 100000) 23 * cCG cZ 23) ≤ (18148354111869 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_23 : (-11827853715851 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 23 * sCG cZ 23 ∧ ex (65083 / 100000) 23 * sCG cZ 23 ≤ (-4731139528099 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 sCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_23 : (-6720090748567 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 23 * sCG cZ 23) ∧ kappa * (ex (65083 / 100000) 23 * sCG cZ 23) ≤ (-6720087967089 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_23 : (400621279162437 / 1000000000000000 : ℝ) ≤ Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23) ∧ Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23) ≤ (80124262016877 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_23 eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_23 : (113808109926587 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23)) ∧ kappa * (Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23)) ≤ (56904059355433 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_24 : (397256728774203 / 125000000000000 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (3178053830849101 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_24
  constructor <;> linarith [h.1, h.2]

theorem eC_24 : (-2319487946253 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 24 * cCG cZ 24 ∧ ex (65083 / 100000) 24 * cCG cZ 24 ≤ (-4638966308227 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 cCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_24 : (-63153062520303 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 24 * sCG cZ 24 ∧ ex (65083 / 100000) 24 * sCG cZ 24 ≤ (-126306115404421 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 sCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_24 : (-3685728776599 / 250000000000000 : ℝ) ≤ Real.log 24 * (ex (65083 / 100000) 24 * cCG cZ 24) ∧ Real.log 24 * (ex (65083 / 100000) 24 * cCG cZ 24) ≤ (-14742884643999 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_24 eC_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_26 : (162904826893321 / 50000000000000 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ (1629048269263539 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_26
  constructor <;> linarith [h.1, h.2]

theorem eC_26 : (38143971675893 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 26 * cCG cZ 26 ∧ ex (65083 / 100000) 26 * cCG cZ 26 ≤ (19071990420029 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 cCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_26 : (56875254568023 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 26 * sCG cZ 26 ∧ ex (65083 / 100000) 26 * sCG cZ 26 ≤ (113750518332721 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 sCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_26 : (124276742057701 / 1000000000000000 : ℝ) ≤ Real.log 26 * (ex (65083 / 100000) 26 * cCG cZ 26) ∧ Real.log 26 * (ex (65083 / 100000) 26 * cCG cZ 26) ≤ (124276771940637 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_26 eC_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_27 : (51497451028891 / 15625000000000 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ (411979608313923 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_27
  constructor <;> linarith [h.1, h.2]

theorem eC_27 : (43719126140697 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 27 * cCG cZ 27 ∧ ex (65083 / 100000) 27 * cCG cZ 27 ≤ (87438261291259 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 cCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_27 : (993575004127 / 40000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 27 * cCG cZ 27) ∧ kappa * (ex (65083 / 100000) 27 * cCG cZ 27) ≤ (2483937766269 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_27 : (-77837449034193 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 27 * sCG cZ 27 ∧ ex (65083 / 100000) 27 * sCG cZ 27 ≤ (-77837440033527 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 sCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_27 : (-22111988096611 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 27 * sCG cZ 27) ∧ kappa * (ex (65083 / 100000) 27 * sCG cZ 27) ≤ (-22111985539709 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_27 : (11527288614177 / 40000000000000 : ℝ) ≤ Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27) ∧ Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27) ≤ (288182245107387 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_27 eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_27 : (319791125741 / 3906250000000 : ℝ) ≤ kappa * (Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27)) ∧ kappa * (Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27)) ≤ (81866536641891 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_28 : (3332204510019711 / 1000000000000000 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ (1666102255341693 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_28
  constructor <;> linarith [h.1, h.2]

theorem eC_28 : (-2195645884271 / 20000000000000 : ℝ) ≤ ex (65083 / 100000) 28 * cCG cZ 28 ∧ ex (65083 / 100000) 28 * cCG cZ 28 ≤ (-27445571351271 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 cCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_28 : (-31186849170793 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 28 * cCG cZ 28) ∧ kappa * (ex (65083 / 100000) 28 * cCG cZ 28) ≤ (-31186846668491 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_28 : (-15955809232881 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 28 * sCG cZ 28 ∧ ex (65083 / 100000) 28 * sCG cZ 28 ≤ (-31911609690933 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 sCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_28 : (-4532711030577 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 28 * sCG cZ 28) ∧ kappa * (ex (65083 / 100000) 28 * sCG cZ 28) ≤ (-1133177446051 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_28 : (-182908527985781 / 500000000000000 : ℝ) ≤ Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28) ∧ Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28) ≤ (-91454256636773 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_28 eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_28 : (-103920959480917 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28)) ∧ kappa * (Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28)) ≤ (-2598023778051 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_29 : (673459165966167 / 200000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295830495533 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_29
  constructor <;> linarith [h.1, h.2]

theorem eC_29 : (45907833736421 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 29 * cCG cZ 29 ∧ ex (65083 / 100000) 29 * cCG cZ 29 ≤ (22953921145661 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 cCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_29 : (50939622832199 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 29 * sCG cZ 29 ∧ ex (65083 / 100000) 29 * sCG cZ 29 ≤ (50939627121761 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 sCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_29 : (154585257097217 / 1000000000000000 : ℝ) ≤ Real.log 29 * (ex (65083 / 100000) 29 * cCG cZ 29) ∧ Real.log 29 * (ex (65083 / 100000) 29 * cCG cZ 29) ≤ (19323160741827 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_29 eC_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_31 : (3433987204329301 / 1000000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (42924840062443 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_31
  constructor <;> linarith [h.1, h.2]

theorem eC_31 : (-21072245682877 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 31 * cCG cZ 31 ∧ ex (65083 / 100000) 31 * cCG cZ 31 ≤ (-42144487256271 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 cCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_31 : (2636365322579 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 31 * sCG cZ 31 ∧ ex (65083 / 100000) 31 * sCG cZ 31 ≤ (32954570636963 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 sCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_31 : (-289447288222081 / 1000000000000000 : ℝ) ≤ Real.log 31 * (ex (65083 / 100000) 31 * cCG cZ 31) ∧ Real.log 31 * (ex (65083 / 100000) 31 * cCG cZ 31) ≤ (-289447259942107 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_31 eC_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_32 : (3465735902643809 / 1000000000000000 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (433216987913807 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_32
  constructor <;> linarith [h.1, h.2]

theorem eC_32 : (10310384030551 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 32 * cCG cZ 32 ∧ ex (65083 / 100000) 32 * cCG cZ 32 ≤ (103103848425797 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 cCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_32 : (29289640370263 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 32 * cCG cZ 32) ∧ kappa * (ex (65083 / 100000) 32 * cCG cZ 32) ≤ (7322410669267 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_32 : (-2354383422651 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 32 * sCG cZ 32 ∧ ex (65083 / 100000) 32 * sCG cZ 32 ≤ (-9417529648743 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 sCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_32 : (-1337661983081 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 32 * sCG cZ 32) ∧ kappa * (ex (65083 / 100000) 32 * sCG cZ 32) ≤ (-5350645635907 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_32 : (357330681047259 / 1000000000000000 : ℝ) ≤ Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32) ∧ Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32) ≤ (89332677314691 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_32 eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_32 : (25377539551687 / 250000000000000 : ℝ) ≤ kappa * (Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32)) ∧ kappa * (Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32)) ≤ (101510166221047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_33 : (699301512262101 / 200000000000000 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (3496507561977559 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_33
  constructor <;> linarith [h.1, h.2]

theorem eC_33 : (-25217333435671 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 33 * cCG cZ 33 ∧ ex (65083 / 100000) 33 * cCG cZ 33 ≤ (-100869325800507 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 cCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_33 : (-14327431941221 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 33 * cCG cZ 33) ∧ kappa * (ex (65083 / 100000) 33 * cCG cZ 33) ≤ (-5730972325247 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_33 : (-1947393118893 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 33 * sCG cZ 33 ∧ ex (65083 / 100000) 33 * sCG cZ 33 ≤ (-4868480820523 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 sCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_33 : (-2766067875983 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 33 * sCG cZ 33) ∧ kappa * (ex (65083 / 100000) 33 * sCG cZ 33) ≤ (-2766066752899 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_33 : (-352690388202933 / 1000000000000000 : ℝ) ≤ Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33) ∧ Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33) ≤ (-70538072073153 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_33 eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_33 : (-50095974126197 / 500000000000000 : ℝ) ≤ kappa * (Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33)) ∧ kappa * (Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33)) ≤ (-25047985086109 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_34 : (3526360524460139 / 1000000000000000 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ (3526360525127523 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_34
  constructor <;> linarith [h.1, h.2]

theorem eC_34 : (90405260580921 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 34 * cCG cZ 34 ∧ ex (65083 / 100000) 34 * cCG cZ 34 ≤ (90405268321611 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 cCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_34 : (44480368056337 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 34 * sCG cZ 34 ∧ ex (65083 / 100000) 34 * sCG cZ 34 ≤ (22240187888531 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 sCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_34 : (79700385529023 / 250000000000000 : ℝ) ≤ Real.log 34 * (ex (65083 / 100000) 34 * cCG cZ 34) ∧ Real.log 34 * (ex (65083 / 100000) 34 * cCG cZ 34) ≤ (318801569472891 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_34 eC_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_36 : (3583518938300017 / 1000000000000000 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ (3583518938967891 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_36
  constructor <;> linarith [h.1, h.2]

theorem eC_36 : (74282410560703 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 36 * cCG cZ 36 ∧ ex (65083 / 100000) 36 * cCG cZ 36 ≤ (580331390657 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_36 cCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_36 : (62496898117269 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 36 * sCG cZ 36 ∧ ex (65083 / 100000) 36 * sCG cZ 36 ≤ (6249690555291 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_36 sCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_36 : (33274053128357 / 125000000000000 : ℝ) ≤ Real.log 36 * (ex (65083 / 100000) 36 * cCG cZ 36) ∧ Real.log 36 * (ex (65083 / 100000) 36 * cCG cZ 36) ≤ (33274056468751 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_36 eC_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_37 : (1805458956244053 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (11284118478613 / 3125000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_37
  constructor <;> linarith [h.1, h.2]

theorem eC_37 : (-73799778984469 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 37 * cCG cZ 37 ∧ ex (65083 / 100000) 37 * cCG cZ 37 ≤ (-73799771612403 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 cCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_37 : (-10482485324771 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 37 * cCG cZ 37) ∧ kappa * (ex (65083 / 100000) 37 * cCG cZ 37) ≤ (-5241242138823 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_37 : (-30195886815617 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 37 * sCG cZ 37 ∧ ex (65083 / 100000) 37 * sCG cZ 37 ≤ (-377448539169 / 6250000000000 : ℝ) := by
  exact mul_bounds_of exB_37 sCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_37 : (-4289009327247 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 37 * sCG cZ 37) ∧ kappa * (ex (65083 / 100000) 37 * sCG cZ 37) ≤ (-8578017608487 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_37 : (-53296988784397 / 200000000000000 : ℝ) ≤ Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37) ∧ Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37) ≤ (-266484917252757 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_37 eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_37 : (-9462848508403 / 125000000000000 : ℝ) ≤ kappa * (Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37)) ∧ kappa * (Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37)) ≤ (-37851390245527 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_38 : (1818793079785123 / 500000000000000 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ (72751723204769 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_38
  constructor <;> linarith [h.1, h.2]

theorem eC_38 : (7794008955841 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 38 * cCG cZ 38 ∧ ex (65083 / 100000) 38 * cCG cZ 38 ≤ (38970048408307 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 cCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_38 : (22141146118589 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 38 * cCG cZ 38) ∧ kappa * (ex (65083 / 100000) 38 * cCG cZ 38) ≤ (22141148180493 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_38 : (52044837362207 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 38 * sCG cZ 38 ∧ ex (65083 / 100000) 38 * sCG cZ 38 ≤ (2081793784353 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 sCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_38 : (2956969526937 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 38 * sCG cZ 38) ∧ kappa * (ex (65083 / 100000) 38 * sCG cZ 38) ≤ (7392424846649 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_38 : (283513791053337 / 1000000000000000 : ℝ) ≤ Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38) ∧ Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38) ≤ (3543922718847 / 12500000000000 : ℝ) := by
  exact mul_bounds_of lgB_38 eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_38 : (40270163339001 / 500000000000000 : ℝ) ≤ kappa * (Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38)) ∧ kappa * (Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38)) ≤ (1610806683863 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_39 : (3663561645973489 / 1000000000000000 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ (3663561646641817 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_39
  constructor <;> linarith [h.1, h.2]

theorem eC_39 : (-84414956808823 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 39 * cCG cZ 39 ∧ ex (65083 / 100000) 39 * cCG cZ 39 ≤ (-42207474864931 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 cCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_39 : (-9237927265697 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 39 * sCG cZ 39 ∧ ex (65083 / 100000) 39 * sCG cZ 39 ≤ (-18475851002239 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 sCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_39 : (-30925939816773 / 100000000000000 : ℝ) ≤ Real.log 39 * (ex (65083 / 100000) 39 * cCG cZ 39) ∧ Real.log 39 * (ex (65083 / 100000) 39 * cCG cZ 39) ≤ (-154629686088551 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_39 eC_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_41 : (3713572066548123 / 1000000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (3713572067216643 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_41
  constructor <;> linarith [h.1, h.2]

theorem eC_41 : (-17608135294543 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 41 * cCG cZ 41 ∧ ex (65083 / 100000) 41 * cCG cZ 41 ≤ (-44020334780043 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 cCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_41 : (2863595630981 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 41 * sCG cZ 41 ∧ ex (65083 / 100000) 41 * sCG cZ 41 ≤ (2863597007091 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 sCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_41 : (-81736349231983 / 250000000000000 : ℝ) ≤ Real.log 41 * (ex (65083 / 100000) 41 * cCG cZ 41) ∧ Real.log 41 * (ex (65083 / 100000) 41 * cCG cZ 41) ≤ (-5108521424977 / 15625000000000 : ℝ) := by
  exact mul_bounds_of lgB_41 eC_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_42 : (3737669618127173 / 1000000000000000 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ (3737669618795767 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_42
  constructor <;> linarith [h.1, h.2]

theorem eC_42 : (74779012060887 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 42 * cCG cZ 42 ∧ ex (65083 / 100000) 42 * cCG cZ 42 ≤ (74779018817881 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 cCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_42 : (21243150245587 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 42 * cCG cZ 42) ∧ kappa * (ex (65083 / 100000) 42 * cCG cZ 42) ≤ (5310788041277 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_42 : (-46028009143437 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 42 * sCG cZ 42 ∧ ex (65083 / 100000) 42 * sCG cZ 42 ≤ (-9205600479819 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 sCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_42 : (-6537796413673 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 42 * sCG cZ 42) ∧ kappa * (ex (65083 / 100000) 42 * sCG cZ 42) ≤ (-13075590911419 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_42 : (139749620726771 / 500000000000000 : ℝ) ≤ Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42) ∧ Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42) ≤ (279499266758951 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_42 eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_42 : (39699938633121 / 500000000000000 : ℝ) ≤ kappa * (Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42)) ∧ kappa * (Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42)) ≤ (3969994222749 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_43 : (1880600057768679 / 500000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600058103007 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_43
  constructor <;> linarith [h.1, h.2]

theorem eC_43 : (-23105078890191 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 43 * cCG cZ 43 ∧ ex (65083 / 100000) 43 * cCG cZ 43 ≤ (-11552537777159 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 cCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_43 : (-6563668718983 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 43 * cCG cZ 43) ∧ kappa * (ex (65083 / 100000) 43 * cCG cZ 43) ≤ (-6563667771331 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_43 : (7309252793477 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 43 * sCG cZ 43 ∧ ex (65083 / 100000) 43 * sCG cZ 43 ≤ (36546267309197 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 sCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_43 : (5191013861897 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 43 * sCG cZ 43) ∧ kappa * (ex (65083 / 100000) 43 * sCG cZ 43) ≤ (10382028673133 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_43 : (-5431426587921 / 31250000000000 : ℝ) ≤ Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43) ∧ Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43) ≤ (-217257032111 / 1250000000000 : ℝ) := by
  exact mul_bounds_of lgB_43 eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_43 : (-771477235893 / 15625000000000 : ℝ) ≤ kappa * (Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43)) ∧ kappa * (Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43)) ≤ (-24687267979879 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_44 : (3784189633762049 / 1000000000000000 : ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ (3784189634430759 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_44
  constructor <;> linarith [h.1, h.2]

theorem eC_44 : (3980181701251 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 44 * cCG cZ 44 ∧ ex (65083 / 100000) 44 * cCG cZ 44 ≤ (1990094122621 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 cCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_44 : (-10637197117427 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 44 * sCG cZ 44 ∧ ex (65083 / 100000) 44 * sCG cZ 44 ≤ (-42548785180059 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 sCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_44 : (15061762334363 / 1000000000000000 : ℝ) ≤ Real.log 44 * (ex (65083 / 100000) 44 * cCG cZ 44) ∧ Real.log 44 * (ex (65083 / 100000) 44 * cCG cZ 44) ≤ (1882723387591 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_44 eC_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_46 : (3828641396332871 / 1000000000000000 : ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ (59822521828151 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_46
  constructor <;> linarith [h.1, h.2]

theorem eC_46 : (-37965713260857 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 46 * cCG cZ 46 ∧ ex (65083 / 100000) 46 * cCG cZ 46 ≤ (-75931420139721 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 cCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_46 : (-32921914558711 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 46 * sCG cZ 46 ∧ ex (65083 / 100000) 46 * sCG cZ 46 ≤ (-6584381639089 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 sCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_46 : (-11628568116577 / 40000000000000 : ℝ) ≤ Real.log 46 * (ex (65083 / 100000) 46 * cCG cZ 46) ∧ Real.log 46 * (ex (65083 / 100000) 46 * cCG cZ 46) ≤ (-290714178429279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_46 eC_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_47 : (385014760155383 / 100000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (60158556284729 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_47
  constructor <;> linarith [h.1, h.2]

theorem eC_47 : (78494128245693 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 47 * cCG cZ 47 ∧ ex (65083 / 100000) 47 * cCG cZ 47 ≤ (19623533628597 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 cCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_47 : (22298536899123 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 47 * cCG cZ 47) ∧ kappa * (ex (65083 / 100000) 47 * cCG cZ 47) ≤ (22298538679929 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_47 : (-5584701477841 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 47 * sCG cZ 47 ∧ ex (65083 / 100000) 47 * sCG cZ 47 ≤ (-4467759933423 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 sCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_47 : (-6345986623837 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 47 * sCG cZ 47) ∧ kappa * (ex (65083 / 100000) 47 * sCG cZ 47) ≤ (-793248106247 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_47 : (302213979601213 / 1000000000000000 : ℝ) ≤ Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47) ∧ Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47) ≤ (151107001894557 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_47 eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_47 : (42926329180159 / 500000000000000 : ℝ) ≤ kappa * (Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47)) ∧ kappa * (Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47)) ≤ (17170533046319 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_48 : (1935600505375829 / 500000000000000 : ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ (3871201011420513 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_48
  constructor <;> linarith [h.1, h.2]

theorem eC_48 : (-42451233846809 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 48 * cCG cZ 48 ∧ ex (65083 / 100000) 48 * cCG cZ 48 ≤ (-53064034521 / 1250000000000 : ℝ) := by
  exact mul_bounds_of exB_48 cCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_48 : (-1507438240131 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 48 * cCG cZ 48) ∧ kappa * (ex (65083 / 100000) 48 * cCG cZ 48) ≤ (-188429752363 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_48 : (13679471975047 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 48 * sCG cZ 48 ∧ ex (65083 / 100000) 48 * sCG cZ 48 ≤ (34198683058339 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 sCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_48 : (3886051318913 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 48 * sCG cZ 48) ∧ kappa * (ex (65083 / 100000) 48 * sCG cZ 48) ≤ (19430258367629 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_48 : (-20542157425477 / 125000000000000 : ℝ) ≤ Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48) ∧ Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48) ≤ (-41084308814451 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_48 eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_48 : (-4668477151879 / 100000000000000 : ℝ) ≤ kappa * (Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48)) ∧ kappa * (Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48)) ≤ (-46684764659413 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_49 : (389182029795439 / 100000000000000 : ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ (389182029862327 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_49
  constructor <;> linarith [h.1, h.2]

theorem eC_49 : (-9137186771521 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 49 * cCG cZ 49 ∧ ex (65083 / 100000) 49 * cCG cZ 49 ≤ (-4568591847881 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 cCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_49 : (-77296445717239 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 49 * sCG cZ 49 ∧ ex (65083 / 100000) 49 * sCG cZ 49 ≤ (-77296439540023 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 sCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_49 : (-14224115579887 / 200000000000000 : ℝ) ≤ Real.log 49 * (ex (65083 / 100000) 49 * cCG cZ 49) ∧ Real.log 49 * (ex (65083 / 100000) 49 * cCG cZ 49) ≤ (-4445034621663 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_49 eC_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_51 : (982956408142021 / 250000000000000 : ℝ) ≤ Real.log 51 ∧ Real.log 51 ≤ (982956408309251 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_51
  constructor <;> linarith [h.1, h.2]

theorem eC_51 : (-7193989977611 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 51 * cCG cZ 51 ∧ ex (65083 / 100000) 51 * cCG cZ 51 ≤ (-71939893768907 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 cCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_51 : (14258645560167 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 51 * sCG cZ 51 ∧ ex (65083 / 100000) 51 * sCG cZ 51 ≤ (28517297108629 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 sCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_51 : (-282855141992211 / 1000000000000000 : ℝ) ≤ Real.log 51 * (ex (65083 / 100000) 51 * cCG cZ 51) ∧ Real.log 51 * (ex (65083 / 100000) 51 * cCG cZ 51) ≤ (-282855118324813 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_51 eC_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_52 : (3951243718425183 / 1000000000000000 : ℝ) ≤ Real.log 52 ∧ Real.log 52 ≤ (3951243719094119 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_52
  constructor <;> linarith [h.1, h.2]

theorem eC_52 : (507036113527 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 52 * cCG cZ 52 ∧ ex (65083 / 100000) 52 * cCG cZ 52 ≤ (10140725229969 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 cCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_52 : (1440383343233 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 52 * cCG cZ 52) ∧ kappa * (ex (65083 / 100000) 52 * cCG cZ 52) ≤ (1440383763589 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_52 : (-36836731389273 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 52 * sCG cZ 52 ∧ ex (65083 / 100000) 52 * sCG cZ 52 ≤ (-73673456836439 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 sCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_52 : (-10464543431271 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 52 * sCG cZ 52) ∧ kappa * (ex (65083 / 100000) 52 * sCG cZ 52) ≤ (-20929085174513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_52 : (80136930343531 / 1000000000000000 : ℝ) ≤ Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52) ∧ Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52) ≤ (80136953743949 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_52 eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_52 : (4553044509659 / 200000000000000 : ℝ) ≤ kappa * (Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52)) ∧ kappa * (Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52)) ≤ (4553045839173 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_53 : (31762335307167 / 8000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145957032413 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_53
  constructor <;> linarith [h.1, h.2]

theorem eC_53 : (24262827931343 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 53 * cCG cZ 53 ∧ ex (65083 / 100000) 53 * cCG cZ 53 ≤ (48525661689467 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 cCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_53 : (17231402399 / 1250000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 53 * cCG cZ 53) ∧ kappa * (ex (65083 / 100000) 53 * cCG cZ 53) ≤ (3446280893617 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_53 : (451598947999 / 7812500000000 : ℝ) ≤ ex (65083 / 100000) 53 * sCG cZ 53 ∧ ex (65083 / 100000) 53 * sCG cZ 53 ≤ (57804671176699 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 sCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_53 : (8210547030201 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 53 * sCG cZ 53) ∧ kappa * (ex (65083 / 100000) 53 * sCG cZ 53) ≤ (16421095717387 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_53 : (192661019063853 / 1000000000000000 : ℝ) ≤ Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53) ∧ Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53) ≤ (192661042230337 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_53 eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_53 : (27365479040489 / 500000000000000 : ℝ) ≤ kappa * (Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53)) ∧ kappa * (Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53)) ≤ (13682741165523 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_54 : (1994492023204013 / 500000000000000 : ℝ) ≤ Real.log 54 ∧ Real.log 54 ≤ (3988984047076989 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_54
  constructor <;> linarith [h.1, h.2]

theorem eC_54 : (-36939858022179 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 54 * cCG cZ 54 ∧ ex (65083 / 100000) 54 * cCG cZ 54 ≤ (-73879710270131 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 cCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_54 : (2512325065179 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 54 * sCG cZ 54 ∧ ex (65083 / 100000) 54 * sCG cZ 54 ≤ (10049306007147 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 sCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_54 : (-147352504351761 / 500000000000000 : ℝ) ≤ Real.log 54 * (ex (65083 / 100000) 54 * cCG cZ 54) ∧ Real.log 54 * (ex (65083 / 100000) 54 * cCG cZ 54) ≤ (-294704985620799 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_54 eC_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_56 : (2012675845289449 / 500000000000000 : ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ (2012675845623941 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_56
  constructor <;> linarith [h.1, h.2]

theorem eC_56 : (46671116259293 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 56 * cCG cZ 56 ∧ ex (65083 / 100000) 56 * cCG cZ 56 ≤ (46671121901433 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 cCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_56 : (27946267223041 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 56 * sCG cZ 56 ∧ ex (65083 / 100000) 56 * sCG cZ 56 ≤ (55892540094089 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 sCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_56 : (187867656735549 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (65083 / 100000) 56 * cCG cZ 56) ∧ Real.log 56 * (ex (65083 / 100000) 56 * cCG cZ 56) ≤ (18786767947837 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_56 eC_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_57 : (2021525633839149 / 500000000000000 : ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ (404305126834729 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_57
  constructor <;> linarith [h.1, h.2]

theorem eC_57 : (-34908491836447 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 57 * cCG cZ 57 ∧ ex (65083 / 100000) 57 * cCG cZ 57 ≤ (-69816978127079 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 cCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_57 : (-9916770982809 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 57 * cCG cZ 57) ∧ kappa * (ex (65083 / 100000) 57 * cCG cZ 57) ≤ (-19833540390167 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_57 : (700855247399 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 57 * sCG cZ 57 ∧ ex (65083 / 100000) 57 * sCG cZ 57 ≤ (1095086669251 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_57 sCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_57 : (4977457213791 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 57 * sCG cZ 57) ∧ kappa * (ex (65083 / 100000) 57 * sCG cZ 57) ≤ (1244364695693 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_57 : (-282273644390877 / 1000000000000000 : ℝ) ≤ Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57) ∧ Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57) ≤ (-141136810961077 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_57 eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_57 : (-8018802699991 / 100000000000000 : ℝ) ≤ kappa * (Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57)) ∧ kappa * (Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57)) ≤ (-16037604123403 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_58 : (4060443010370279 / 1000000000000000 : ℝ) ≤ Real.log 58 ∧ Real.log 58 ≤ (2030221505569357 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_58
  constructor <;> linarith [h.1, h.2]

theorem eC_58 : (11958205225891 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 58 * cCG cZ 58 ∧ ex (65083 / 100000) 58 * cCG cZ 58 ≤ (11958211490551 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 cCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_58 : (1698537753309 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 58 * cCG cZ 58) ∧ kappa * (ex (65083 / 100000) 58 * cCG cZ 58) ≤ (1698538643139 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_58 : (-70160043402007 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 58 * sCG cZ 58 ∧ ex (65083 / 100000) 58 * sCG cZ 58 ≤ (-8770004638529 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 sCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_58 : (-3986199609089 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 58 * sCG cZ 58) ∧ kappa * (ex (65083 / 100000) 58 * sCG cZ 58) ≤ (-9965498128757 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_58 : (24277805413021 / 500000000000000 : ℝ) ≤ Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58) ∧ Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58) ≤ (48555636272527 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_58 eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_58 : (13793631496549 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58)) ∧ kappa * (Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58)) ≤ (13793638725363 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_59 : (2038768721855667 / 500000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537444570997 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_59
  constructor <;> linarith [h.1, h.2]

theorem eC_59 : (60019833908423 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 59 * cCG cZ 59 ∧ ex (65083 / 100000) 59 * cCG cZ 59 ≤ (30009920429857 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 cCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_59 : (36763868126621 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 59 * sCG cZ 59 ∧ ex (65083 / 100000) 59 * sCG cZ 59 ≤ (36763875064791 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 sCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_59 : (244733120126929 / 1000000000000000 : ℝ) ≤ Real.log 59 * (ex (65083 / 100000) 59 * cCG cZ 59) ∧ Real.log 59 * (ex (65083 / 100000) 59 * cCG cZ 59) ≤ (244733148522677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_59 eC_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_61 : (205543693197337 / 50000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (2055436932483667 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_61
  constructor <;> linarith [h.1, h.2]

theorem eC_61 : (-4813936202941 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 61 * cCG cZ 61 ∧ ex (65083 / 100000) 61 * cCG cZ 61 ≤ (-24069672912157 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 cCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_61 : (-64530967637319 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 61 * sCG cZ 61 ∧ ex (65083 / 100000) 61 * sCG cZ 61 ≤ (-6453095950789 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 sCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_61 : (-24736855655363 / 250000000000000 : ℝ) ≤ Real.log 61 * (ex (65083 / 100000) 61 * cCG cZ 61) ∧ Real.log 61 * (ex (65083 / 100000) 61 * cCG cZ 61) ≤ (-98947389288333 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_61 eC_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_62 : (515891798100539 / 125000000000000 : ℝ) ≤ Real.log 62 ∧ Real.log 62 ≤ (82542687717919 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_62
  constructor <;> linarith [h.1, h.2]

theorem eC_62 : (6797482910741 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 62 * cCG cZ 62 ∧ ex (65083 / 100000) 62 * cCG cZ 62 ≤ (13594967531139 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 cCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_62 : (301722257157 / 15625000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 62 * cCG cZ 62) ∧ kappa * (ex (65083 / 100000) 62 * cCG cZ 62) ≤ (9655113443219 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_62 : (-4865222975619 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 62 * sCG cZ 62 ∧ ex (65083 / 100000) 62 * sCG cZ 62 ≤ (-4865214472179 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 sCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_62 : (-276421578197 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 62 * sCG cZ 62) ∧ kappa * (ex (65083 / 100000) 62 * sCG cZ 62) ≤ (-276421095067 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_62 : (70135313627597 / 250000000000000 : ℝ) ≤ Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62) ∧ Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62) ≤ (140270644932257 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_62 eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_62 : (796958913391 / 10000000000000 : ℝ) ≤ kappa * (Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62)) ∧ kappa * (Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62)) ≤ (19923975345617 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_63 : (828626945227529 / 200000000000000 : ℝ) ≤ Real.log 63 ∧ Real.log 63 ≤ (517891840911853 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_63
  constructor <;> linarith [h.1, h.2]

theorem eC_63 : (-6183178587607 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 63 * cCG cZ 63 ∧ ex (65083 / 100000) 63 * cCG cZ 63 ≤ (-1236634820883 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 cCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_63 : (-878255730531 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 63 * cCG cZ 63) ∧ kappa * (ex (65083 / 100000) 63 * cCG cZ 63) ≤ (-1756510187481 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_63 : (66299287839607 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 63 * sCG cZ 63 ∧ ex (65083 / 100000) 63 * sCG cZ 63 ≤ (8287412105827 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 sCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_63 : (753369531871 / 40000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 63 * sCG cZ 63) ∧ kappa * (ex (65083 / 100000) 63 * sCG cZ 63) ≤ (18834240855479 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_63 : (-51235483862761 / 1000000000000000 : ℝ) ≤ Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63) ∧ Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63) ≤ (-51235446699513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_63 eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_63 : (-2910985453287 / 200000000000000 : ℝ) ≤ kappa * (Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63)) ∧ kappa * (Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63)) ≤ (-7277458354567 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_64 : (1039720770773419 / 250000000000000 : ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ (831776616862279 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_64
  constructor <;> linarith [h.1, h.2]

theorem eC_64 : (-61182626770063 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 64 * cCG cZ 64 ∧ ex (65083 / 100000) 64 * cCG cZ 64 ≤ (-15295654357747 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 cCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_64 : (-20859796577 / 781250000000 : ℝ) ≤ ex (65083 / 100000) 64 * sCG cZ 64 ∧ ex (65083 / 100000) 64 * sCG cZ 64 ≤ (-26700530306821 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 sCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_64 : (-254451391527753 / 1000000000000000 : ℝ) ≤ Real.log 64 * (ex (65083 / 100000) 64 * cCG cZ 64) ∧ Real.log 64 * (ex (65083 / 100000) 64 * cCG cZ 64) ≤ (-31806419076641 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_64 eC_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_66 : (261853421358679 / 62500000000000 : ℝ) ≤ Real.log 66 ∧ Real.log 66 ≤ (837930948612883 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_66
  constructor <;> linarith [h.1, h.2]

theorem eC_66 : (23191314207189 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 66 * cCG cZ 66 ∧ ex (65083 / 100000) 66 * cCG cZ 66 ≤ (23191319197223 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 cCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_66 : (46151046715809 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 66 * sCG cZ 66 ∧ ex (65083 / 100000) 66 * sCG cZ 66 ≤ (46151056688871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 sCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_66 : (19432719907061 / 100000000000000 : ℝ) ≤ Real.log 66 * (ex (65083 / 100000) 66 * cCG cZ 66) ∧ Real.log 66 * (ex (65083 / 100000) 66 * cCG cZ 66) ≤ (194327240945133 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_66 eC_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_67 : (131396644346681 / 31250000000000 : ℝ) ≤ Real.log 67 ∧ Real.log 67 ≤ (840938524093481 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_67
  constructor <;> linarith [h.1, h.2]

theorem eC_67 : (-2594830517141 / 50000000000000 : ℝ) ≤ ex (65083 / 100000) 67 * cCG cZ 67 ∧ ex (65083 / 100000) 67 * cCG cZ 67 ≤ (-10379320020133 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 cCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_67 : (-14742739444747 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 67 * cCG cZ 67) ∧ kappa * (ex (65083 / 100000) 67 * cCG cZ 67) ≤ (-2948547307033 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_67 : (310356972907 / 8000000000000 : ℝ) ≤ ex (65083 / 100000) 67 * sCG cZ 67 ∧ ex (65083 / 100000) 67 * sCG cZ 67 ≤ (19397315921593 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 sCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_67 : (5510369507039 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 67 * sCG cZ 67) ∧ kappa * (ex (65083 / 100000) 67 * sCG cZ 67) ≤ (5510370960077 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_67 : (-13638080908483 / 62500000000000 : ℝ) ≤ Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67) ∧ Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67) ≤ (-6819039106229 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_67 eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_67 : (-61988687748801 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67)) ∧ kappa * (Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67)) ≤ (-61988675494653 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_68 : (1054876926217503 / 250000000000000 : ℝ) ≤ Real.log 68 ∧ Real.log 68 ≤ (421950770628823 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_68
  constructor <;> linarith [h.1, h.2]

theorem eC_68 : (-31962786049863 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 68 * cCG cZ 68 ∧ ex (65083 / 100000) 68 * cCG cZ 68 ≤ (-7990693895249 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 cCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_68 : (-9079957699521 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 68 * cCG cZ 68) ∧ kappa * (ex (65083 / 100000) 68 * cCG cZ 68) ≤ (-1815990945107 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_68 : (-55645997651719 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 68 * sCG cZ 68 ∧ ex (65083 / 100000) 68 * sCG cZ 68 ≤ (-55645987160937 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 sCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_68 : (-15807861806447 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 68 * sCG cZ 68) ∧ kappa * (ex (65083 / 100000) 68 * sCG cZ 68) ≤ (-7903929413117 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_68 : (-134867222051839 / 1000000000000000 : ℝ) ≤ Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68) ∧ Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68) ≤ (-134867177833043 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_68 eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_68 : (-383129514859 / 10000000000000 : ℝ) ≤ kappa * (Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68)) ∧ kappa * (Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68)) ≤ (-7662587784853 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_69 : (1058526626070719 / 250000000000000 : ℝ) ≤ Real.log 69 ∧ Real.log 69 ≤ (4234106505742537 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_69
  constructor <;> linarith [h.1, h.2]

theorem eC_69 : (3618551739327 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 69 * cCG cZ 69 ∧ ex (65083 / 100000) 69 * cCG cZ 69 ≤ (57896838495759 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_69 cCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_69 : (-26239985247413 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 69 * sCG cZ 69 ∧ ex (65083 / 100000) 69 * sCG cZ 69 ≤ (-2623997461097 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_69 sCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_69 : (245141335289097 / 1000000000000000 : ℝ) ≤ Real.log 69 * (ex (65083 / 100000) 69 * cCG cZ 69) ∧ Real.log 69 * (ex (65083 / 100000) 69 * cCG cZ 69) ≤ (245141380536819 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_69 eC_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_71 : (852535975342409 / 200000000000000 : ℝ) ≤ Real.log 71 ∧ Real.log 71 ≤ (4262679878246141 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_71
  constructor <;> linarith [h.1, h.2]

theorem eC_71 : (-29756515914307 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 71 * cCG cZ 71 ∧ ex (65083 / 100000) 71 * cCG cZ 71 ≤ (-5951302079341 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 cCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_71 : (18741908613859 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 71 * sCG cZ 71 ∧ ex (65083 / 100000) 71 * sCG cZ 71 ≤ (18741919608349 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 sCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_71 : (-31710625408657 / 125000000000000 : ℝ) ≤ Real.log 71 * (ex (65083 / 100000) 71 * cCG cZ 71) ∧ Real.log 71 * (ex (65083 / 100000) 71 * cCG cZ 71) ≤ (-126842478069207 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_71 eC_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_72 : (133645816208753 / 31250000000000 : ℝ) ≤ Real.log 72 ∧ Real.log 72 ≤ (106916653006191 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_72
  constructor <;> linarith [h.1, h.2]

theorem eC_72 : (-425935970593 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 72 * cCG cZ 72 ∧ ex (65083 / 100000) 72 * cCG cZ 72 ≤ (-8518713847419 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_72 cCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_72 : (-1209994832633 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 72 * cCG cZ 72) ∧ kappa * (ex (65083 / 100000) 72 * cCG cZ 72) ≤ (-4839976169049 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_72 : (-7429410499781 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 72 * sCG cZ 72 ∧ ex (65083 / 100000) 72 * sCG cZ 72 ≤ (-7429409103263 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_72 sCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_72 : (-8442159324303 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 72 * sCG cZ 72) ∧ kappa * (ex (65083 / 100000) 72 * sCG cZ 72) ≤ (-16884315474833 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_72 : (-18215859348299 / 250000000000000 : ℝ) ≤ Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72) ∧ Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72) ≤ (-2914535590879 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_72 eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_72 : (-4139795125117 / 200000000000000 : ℝ) ≤ kappa * (Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72)) ∧ kappa * (Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72)) ≤ (-20698962097393 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_73 : (4290459440806191 / 1000000000000000 : ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ (4290459442404939 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_73
  constructor <;> linarith [h.1, h.2]

theorem eC_73 : (58969431006047 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 73 * cCG cZ 73 ∧ ex (65083 / 100000) 73 * cCG cZ 73 ≤ (29484721139133 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 cCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_73 : (1675197957601 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 73 * cCG cZ 73) ∧ kappa * (ex (65083 / 100000) 73 * cCG cZ 73) ≤ (16751982778213 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_73 : (-16655593980351 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 73 * sCG cZ 73 ∧ ex (65083 / 100000) 73 * sCG cZ 73 ≤ (-16655582752167 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 sCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_73 : (-4731505212533 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 73 * sCG cZ 73) ∧ kappa * (ex (65083 / 100000) 73 * sCG cZ 73) ≤ (-118287550571 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_73 : (253005951978863 / 1000000000000000 : ℝ) ≤ Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73) ∧ Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73) ≤ (12650300021807 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_73 eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_73 : (8984211115511 / 125000000000000 : ℝ) ≤ kappa * (Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73)) ∧ kappa * (Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73)) ≤ (35936851344893 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_74 : (2152032546428071 / 500000000000000 : ℝ) ≤ Real.log 74 ∧ Real.log 74 ≤ (1076016273621007 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_74
  constructor <;> linarith [h.1, h.2]

theorem eC_74 : (17530760356973 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 74 * cCG cZ 74 ∧ ex (65083 / 100000) 74 * cCG cZ 74 ≤ (17530771664629 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 cCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_74 : (58151205698841 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 74 * sCG cZ 74 ∧ ex (65083 / 100000) 74 * sCG cZ 74 ≤ (29075608524771 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 sCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_74 : (75453533703673 / 1000000000000000 : ℝ) ≤ Real.log 74 * (ex (65083 / 100000) 74 * cCG cZ 74) ∧ Real.log 74 * (ex (65083 / 100000) 74 * cCG cZ 74) ≤ (754535824011 / 10000000000000 : ℝ) := by
  exact mul_bounds_of lgB_74 eC_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_76 : (4330733339927761 / 1000000000000000 : ℝ) ≤ Real.log 76 ∧ Real.log 76 ≤ (4330733341608359 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_76
  constructor <;> linarith [h.1, h.2]

theorem eC_76 : (-22686173508843 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 76 * cCG cZ 76 ∧ ex (65083 / 100000) 76 * cCG cZ 76 ≤ (-22686162025851 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 cCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_76 : (-13803020892729 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 76 * sCG cZ 76 ∧ ex (65083 / 100000) 76 * sCG cZ 76 ≤ (-55212072052341 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 sCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_76 : (-98247768008259 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (65083 / 100000) 76 * cCG cZ 76) ∧ Real.log 76 * (ex (65083 / 100000) 76 * cCG cZ 76) ≤ (-24561929560089 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_76 eC_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_77 : (4343805421490343 / 1000000000000000 : ℝ) ≤ Real.log 77 ∧ Real.log 77 ≤ (4343805423194797 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_77
  constructor <;> linarith [h.1, h.2]

theorem eC_77 : (52813285146991 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 77 * cCG cZ 77 ∧ ex (65083 / 100000) 77 * cCG cZ 77 ≤ (52813296775417 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 cCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_77 : (3750786886657 / 250000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 77 * cCG cZ 77) ∧ kappa * (ex (65083 / 100000) 77 * cCG cZ 77) ≤ (15003150850021 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_77 : (-6678691546701 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 77 * sCG cZ 77 ∧ ex (65083 / 100000) 77 * sCG cZ 77 ≤ (-6678688646837 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 sCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_77 : (-474319077173 / 62500000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 77 * sCG cZ 77) ∧ kappa * (ex (65083 / 100000) 77 * sCG cZ 77) ≤ (-1517820387921 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_77 : (114705317174107 / 500000000000000 : ℝ) ≤ Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77) ∧ Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77) ≤ (229410684949853 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_77 eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_77 : (65170753652463 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77)) ∧ kappa * (Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77)) ≤ (65170768027329 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_78 : (4356708826321779 / 1000000000000000 : ℝ) ≤ Real.log 78 ∧ Real.log 78 ≤ (4356708828048589 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_78
  constructor <;> linarith [h.1, h.2]

theorem eC_78 : (6294722057911 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 78 * cCG cZ 78 ∧ ex (65083 / 100000) 78 * cCG cZ 78 ≤ (31473621899643 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 cCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_78 : (4470496558631 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 78 * cCG cZ 78) ∧ kappa * (ex (65083 / 100000) 78 * cCG cZ 78) ≤ (4470498207723 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_78 : (4953776167127 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 78 * sCG cZ 78 ∧ ex (65083 / 100000) 78 * sCG cZ 78 ≤ (4953777330179 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 sCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_78 : (439769999049 / 31250000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 78 * sCG cZ 78) ∧ kappa * (ex (65083 / 100000) 78 * sCG cZ 78) ≤ (3518160818389 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_78 : (34280338936179 / 250000000000000 : ℝ) ≤ Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78) ∧ Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78) ≤ (137121406380839 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_78 eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_78 : (38953303630059 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78)) ∧ kappa * (Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78)) ≤ (19476659007361 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_79 : (546180981511877 / 125000000000000 : ℝ) ≤ Real.log 79 ∧ Real.log 79 ≤ (4369447853842793 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_79
  constructor <;> linarith [h.1, h.2]

theorem eC_79 : (-22584392172209 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 79 * cCG cZ 79 ∧ ex (65083 / 100000) 79 * cCG cZ 79 ≤ (-45168772675733 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 cCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_79 : (7342242965419 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 79 * sCG cZ 79 ∧ ex (65083 / 100000) 79 * sCG cZ 79 ≤ (18355613242491 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 sCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_79 : (-98681323907203 / 500000000000000 : ℝ) ≤ Real.log 79 * (ex (65083 / 100000) 79 * cCG cZ 79) ∧ Real.log 79 * (ex (65083 / 100000) 79 * cCG cZ 79) ≤ (-197362596749749 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_79 eC_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_81 : (4394449154292799 / 1000000000000000 : ℝ) ≤ Real.log 81 ∧ Real.log 81 ≤ (4394449156078747 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_81
  constructor <;> linarith [h.1, h.2]

theorem eC_81 : (4047585028789 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 81 * cCG cZ 81 ∧ ex (65083 / 100000) 81 * cCG cZ 81 ≤ (6476138397643 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 cCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_81 : (-47232875881527 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 81 * sCG cZ 81 ∧ ex (65083 / 100000) 81 * sCG cZ 81 ≤ (-5904108013263 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 sCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_81 : (1778690660669 / 12500000000000 : ℝ) ≤ Real.log 81 * (ex (65083 / 100000) 81 * cCG cZ 81) ∧ Real.log 81 * (ex (65083 / 100000) 81 * cCG cZ 81) ≤ (71147652290429 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_81 eC_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_82 : (4406719246881137 / 1000000000000000 : ℝ) ≤ Real.log 82 ∧ Real.log 82 ≤ (4406719248684467 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_82
  constructor <;> linarith [h.1, h.2]

theorem eC_82 : (51616423623781 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 82 * cCG cZ 82 ∧ ex (65083 / 100000) 82 * cCG cZ 82 ≤ (25808217701207 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 cCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_82 : (2932628853901 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 82 * cCG cZ 82) ∧ kappa * (ex (65083 / 100000) 82 * cCG cZ 82) ≤ (14663147615569 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_82 : (23732574229443 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 82 * sCG cZ 82 ∧ ex (65083 / 100000) 82 * sCG cZ 82 ≤ (23732585975337 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 sCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_82 : (6741926994971 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 82 * sCG cZ 82) ∧ kappa * (ex (65083 / 100000) 82 * sCG cZ 82) ≤ (1348386066347 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_82 : (45491817487617 / 200000000000000 : ℝ) ≤ Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82) ∧ Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82) ≤ (227459139436297 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_82 eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_82 : (64616360072223 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82)) ∧ kappa * (Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82)) ≤ (64616374843827 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_83 : (4418840607410211 / 1000000000000000 : ℝ) ≤ Real.log 83 ∧ Real.log 83 ≤ (552355076153737 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_83
  constructor <;> linarith [h.1, h.2]

theorem eC_83 : (-6807957798791 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 83 * cCG cZ 83 ∧ ex (65083 / 100000) 83 * cCG cZ 83 ≤ (-6807951919911 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 cCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_83 : (-3867996283973 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 83 * cCG cZ 83) ∧ kappa * (ex (65083 / 100000) 83 * cCG cZ 83) ≤ (-3867992943839 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_83 : (683691054831 / 12500000000000 : ℝ) ≤ ex (65083 / 100000) 83 * sCG cZ 83 ∧ ex (65083 / 100000) 83 * sCG cZ 83 ≤ (54695296192901 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 sCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_83 : (1553778409109 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 83 * sCG cZ 83) ∧ kappa * (ex (65083 / 100000) 83 * sCG cZ 83) ≤ (1942223430631 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_83 : (-60166560774443 / 1000000000000000 : ℝ) ≤ Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83) ∧ Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83) ≤ (-30083254396999 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_83 eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_83 : (-1709205905597 / 100000000000000 : ℝ) ≤ kappa * (Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83)) ∧ kappa * (Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83)) ≤ (-8546022144707 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_84 : (4430816798453847 / 1000000000000000 : ℝ) ≤ Real.log 84 ∧ Real.log 84 ≤ (443081680028893 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_84
  constructor <;> linarith [h.1, h.2]

theorem eC_84 : (-6985160224879 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 84 * cCG cZ 84 ∧ ex (65083 / 100000) 84 * cCG cZ 84 ≤ (-27940634985953 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 cCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_84 : (-565094657437 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 84 * sCG cZ 84 ∧ ex (65083 / 100000) 84 * sCG cZ 84 ≤ (-2260366866677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 sCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_84 : (-247599722216831 / 1000000000000000 : ℝ) ≤ Real.log 84 * (ex (65083 / 100000) 84 * cCG cZ 84) ∧ Real.log 84 * (ex (65083 / 100000) 84 * cCG cZ 84) ≤ (-49519933942091 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_84 eC_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_86 : (1113586823964601 / 250000000000000 : ℝ) ≤ Real.log 86 ∧ Real.log 86 ≤ (2227173648860837 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_86
  constructor <;> linarith [h.1, h.2]

theorem eC_86 : (12601327288977 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 86 * cCG cZ 86 ∧ ex (65083 / 100000) 86 * cCG cZ 86 ≤ (50405320935557 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 cCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_86 : (-1387418001111 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 86 * sCG cZ 86 ∧ ex (65083 / 100000) 86 * sCG cZ 86 ≤ (-11099338136171 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 sCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_86 : (8980910101421 / 40000000000000 : ℝ) ≤ Real.log 86 * (ex (65083 / 100000) 86 * cCG cZ 86) ∧ Real.log 86 * (ex (65083 / 100000) 86 * cCG cZ 86) ≤ (224522805100093 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_86 eC_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_87 : (2232954059128449 / 500000000000000 : ℝ) ≤ Real.log 87 ∧ Real.log 87 ≤ (178636324805323 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_87
  constructor <;> linarith [h.1, h.2]

theorem eC_87 : (6753248143907 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 87 * cCG cZ 87 ∧ ex (65083 / 100000) 87 * cCG cZ 87 ≤ (16883126238859 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 cCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_87 : (959228137769 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 87 * cCG cZ 87) ∧ kappa * (ex (65083 / 100000) 87 * cCG cZ 87) ≤ (1918456943589 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_87 : (42988493259559 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 87 * sCG cZ 87 ∧ ex (65083 / 100000) 87 * sCG cZ 87 ≤ (42988505029827 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 sCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_87 : (2442426012263 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 87 * sCG cZ 87) ∧ kappa * (ex (65083 / 100000) 87 * sCG cZ 87) ≤ (12212133405003 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_87 : (150796928552387 / 1000000000000000 : ℝ) ≤ Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87) ∧ Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87) ≤ (30159396225341 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_87 eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_87 : (42838247277233 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87)) ∧ kappa * (Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87)) ≤ (2677391388281 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_88 : (1119334203519521 / 250000000000000 : ℝ) ≤ Real.log 88 ∧ Real.log 88 ≤ (4477336815966447 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_88
  constructor <;> linarith [h.1, h.2]

theorem eC_88 : (-32356205451397 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 88 * cCG cZ 88 ∧ ex (65083 / 100000) 88 * cCG cZ 88 ≤ (-6471238733373 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 cCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_88 : (-9191719906937 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 88 * cCG cZ 88) ∧ kappa * (ex (65083 / 100000) 88 * cCG cZ 88) ≤ (-4595858279599 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_88 : (43555969372027 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 88 * sCG cZ 88 ∧ ex (65083 / 100000) 88 * sCG cZ 88 ≤ (1742239246833 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 sCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_88 : (12373338132747 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 88 * sCG cZ 88) ∧ kappa * (ex (65083 / 100000) 88 * sCG cZ 88) ≤ (12373341484539 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_88 : (-28973925978503 / 200000000000000 : ℝ) ≤ Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88) ∧ Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88) ≤ (-72434788534047 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_88 eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_88 : (-41154425941381 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88)) ∧ kappa * (Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88)) ≤ (-41154410935069 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_89 : (897727273865943 / 200000000000000 : ℝ) ≤ Real.log 89 ∧ Real.log 89 ≤ (448863637122959 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_89
  constructor <;> linarith [h.1, h.2]

theorem eC_89 : (-50444447857343 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 89 * cCG cZ 89 ∧ ex (65083 / 100000) 89 * cCG cZ 89 ≤ (-25222218031227 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 cCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_89 : (-18879100932369 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 89 * sCG cZ 89 ∧ ex (65083 / 100000) 89 * sCG cZ 89 ≤ (-18879089176521 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 sCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_89 : (-45285356675813 / 200000000000000 : ℝ) ≤ Real.log 89 * (ex (65083 / 100000) 89 * cCG cZ 89) ∧ Real.log 89 * (ex (65083 / 100000) 89 * cCG cZ 89) ≤ (-113213365170129 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_89 eC_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_91 : (4510859506110189 / 1000000000000000 : ℝ) ≤ Real.log 91 ∧ Real.log 91 ≤ (1127714877007811 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_91
  constructor <;> linarith [h.1, h.2]

theorem eC_91 : (10296910839707 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 91 * cCG cZ 91 ∧ ex (65083 / 100000) 91 * cCG cZ 91 ≤ (51484565929293 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 cCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_91 : (-12949339549361 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 91 * sCG cZ 91 ∧ ex (65083 / 100000) 91 * sCG cZ 91 ≤ (-2589865573359 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 sCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_91 : (116119795362153 / 500000000000000 : ℝ) ≤ Real.log 91 * (ex (65083 / 100000) 91 * cCG cZ 91) ∧ Real.log 91 * (ex (65083 / 100000) 91 * cCG cZ 91) ≤ (232239643739013 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_91 eC_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_92 : (452178857664043 / 100000000000000 : ℝ) ≤ Real.log 92 ∧ Real.log 92 ≤ (452178857857123 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_92
  constructor <;> linarith [h.1, h.2]

theorem eC_92 : (14211497872121 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 92 * cCG cZ 92 ∧ ex (65083 / 100000) 92 * cCG cZ 92 ≤ (888218981847 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_92 cCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_92 : (1009297181763 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 92 * cCG cZ 92) ∧ kappa * (ex (65083 / 100000) 92 * cCG cZ 92) ≤ (8074380770689 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_92 : (44392205115353 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 92 * sCG cZ 92 ∧ ex (65083 / 100000) 92 * sCG cZ 92 ≤ (4439221681041 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 sCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_92 : (394090474473 / 31250000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 92 * sCG cZ 92) ∧ kappa * (ex (65083 / 100000) 92 * sCG cZ 92) ≤ (6305449252729 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_92 : (128522777470213 / 1000000000000000 : ℝ) ≤ Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92) ∧ Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92) ≤ (2570456606327 / 20000000000000 : ℝ) := by
  exact mul_bounds_of lgB_92 eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_92 : (9127656933863 / 250000000000000 : ℝ) ≤ kappa * (Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92)) ∧ kappa * (Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92)) ≤ (36510642747933 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_93 : (11331498731857 / 2500000000000 : ℝ) ≤ Real.log 93 ∧ Real.log 93 ≤ (453259949468283 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_93
  constructor <;> linarith [h.1, h.2]

theorem eC_93 : (-32286129713739 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 93 * cCG cZ 93 ∧ ex (65083 / 100000) 93 * cCG cZ 93 ≤ (-32286118075659 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 cCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_93 : (-9171812858387 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 93 * cCG cZ 93) ∧ kappa * (ex (65083 / 100000) 93 * cCG cZ 93) ≤ (-9171809552251 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_93 : (41198483341601 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 93 * sCG cZ 93 ∧ ex (65083 / 100000) 93 * sCG cZ 93 ≤ (10299623747927 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 sCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_93 : (11703625755357 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 93 * sCG cZ 93) ∧ kappa * (ex (65083 / 100000) 93 * sCG cZ 93) ≤ (11703629064909 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_93 : (-73170047612879 / 500000000000000 : ℝ) ≤ Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93) ∧ Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93) ≤ (-73170021206183 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_93 eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_93 : (-41572154327249 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93)) ∧ kappa * (Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93)) ≤ (-4157213932407 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_94 : (4543294781857799 / 1000000000000000 : ℝ) ≤ Real.log 94 ∧ Real.log 94 ≤ (181731791352263 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_94
  constructor <;> linarith [h.1, h.2]

theorem eC_94 : (-4942289786473 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 94 * cCG cZ 94 ∧ ex (65083 / 100000) 94 * cCG cZ 94 ≤ (-386116298423 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_94 cCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_94 : (-16100008790279 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 94 * sCG cZ 94 ∧ ex (65083 / 100000) 94 * sCG cZ 94 ≤ (-16099997165969 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 sCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_94 : (-224542794069433 / 1000000000000000 : ℝ) ≤ Real.log 94 * (ex (65083 / 100000) 94 * cCG cZ 94) ∧ Real.log 94 * (ex (65083 / 100000) 94 * cCG cZ 94) ≤ (-224542740968379 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_94 eC_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_96 : (4564348191052399 / 1000000000000000 : ℝ) ≤ Real.log 96 ∧ Real.log 96 ≤ (570543524127167 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_96
  constructor <;> linarith [h.1, h.2]

theorem eC_96 : (5843711039749 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 96 * cCG cZ 96 ∧ ex (65083 / 100000) 96 * cCG cZ 96 ≤ (1869987996171 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 cCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_96 : (-1052689398561 / 50000000000000 : ℝ) ≤ ex (65083 / 100000) 96 * sCG cZ 96 ∧ ex (65083 / 100000) 96 * sCG cZ 96 ≤ (-21053776417811 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 sCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_96 : (21338185530649 / 100000000000000 : ℝ) ≤ Real.log 96 * (ex (65083 / 100000) 96 * cCG cZ 96) ∧ Real.log 96 * (ex (65083 / 100000) 96 * cCG cZ 96) ≤ (213381908282181 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_96 eC_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_97 : (1143677744521613 / 250000000000000 : ℝ) ≤ Real.log 97 ∧ Real.log 97 ≤ (2287355490029429 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_97
  constructor <;> linarith [h.1, h.2]

theorem eC_97 : (36917178294649 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 97 * cCG cZ 97 ∧ ex (65083 / 100000) 97 * cCG cZ 97 ≤ (9229297461069 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 cCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_97 : (10487396711229 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 97 * cCG cZ 97) ∧ kappa * (ex (65083 / 100000) 97 * cCG cZ 97) ≤ (10487399992237 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_97 : (7016253914923 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 97 * sCG cZ 97 ∧ ex (65083 / 100000) 97 * sCG cZ 97 ≤ (35081281118173 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 sCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_97 : (1245731689683 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 97 * sCG cZ 97) ∧ kappa * (ex (65083 / 100000) 97 * sCG cZ 97) ≤ (2491464199187 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_97 : (33777084164901 / 200000000000000 : ℝ) ≤ Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97) ∧ Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97) ≤ (168885473733527 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_97 eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_97 : (4797680886641 / 100000000000000 : ℝ) ≤ kappa * (Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97)) ∧ kappa * (Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97)) ≤ (11994205974189 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_98 : (2292483739126111 / 500000000000000 : ℝ) ≤ Real.log 98 ∧ Real.log 98 ≤ (2292483740115861 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_98
  constructor <;> linarith [h.1, h.2]

theorem eC_98 : (-17822125663771 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 98 * cCG cZ 98 ∧ ex (65083 / 100000) 98 * cCG cZ 98 ≤ (-8911057101417 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 cCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_98 : (-632861552221 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 98 * cCG cZ 98) ∧ kappa * (ex (65083 / 100000) 98 * cCG cZ 98) ≤ (-1012577832391 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_98 : (5918126963081 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 98 * sCG cZ 98 ∧ ex (65083 / 100000) 98 * sCG cZ 98 ≤ (2959064200227 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_98 sCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_98 : (2689945358397 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 98 * sCG cZ 98) ∧ kappa * (ex (65083 / 100000) 98 * sCG cZ 98) ≤ (13449730058607 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_98 : (-40856933298497 / 500000000000000 : ℝ) ≤ Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98) ∧ Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98) ≤ (-8171381401369 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_98 eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_98 : (-11606598545689 / 500000000000000 : ℝ) ≤ kappa * (Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98)) ∧ kappa * (Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98)) ≤ (-11606591076781 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_99 : (1148779962428723 / 250000000000000 : ℝ) ≤ Real.log 99 ∧ Real.log 99 ≤ (4595119851701133 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_99
  constructor <;> linarith [h.1, h.2]

theorem eC_99 : (-50187914925077 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 99 * cCG cZ 99 ∧ ex (65083 / 100000) 99 * cCG cZ 99 ≤ (-25093951713799 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 cCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_99 : (103968080573 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 99 * sCG cZ 99 ∧ ex (65083 / 100000) 99 * sCG cZ 99 ≤ (1299606725133 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 sCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_99 : (-230619484187709 / 1000000000000000 : ℝ) ≤ Real.log 99 * (ex (65083 / 100000) 99 * cCG cZ 99) ∧ Real.log 99 * (ex (65083 / 100000) 99 * cCG cZ 99) ≤ (-230619431255729 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_99 eC_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_101 : (4615120516419061 / 1000000000000000 : ℝ) ≤ Real.log 101 ∧ Real.log 101 ≤ (2307560259208903 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_101
  constructor <;> linarith [h.1, h.2]

theorem eC_101 : (15222634975871 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 101 * cCG cZ 101 ∧ ex (65083 / 100000) 101 * cCG cZ 101 ≤ (6089056267531 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 cCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_101 : (-979082821977 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 101 * sCG cZ 101 ∧ ex (65083 / 100000) 101 * sCG cZ 101 ≤ (-39163301481141 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 sCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_101 : (140508589982201 / 1000000000000000 : ℝ) ≤ Real.log 101 * (ex (65083 / 100000) 101 * cCG cZ 101) ∧ Real.log 101 * (ex (65083 / 100000) 101 * cCG cZ 101) ≤ (28101728518083 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_101 eC_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_102 : (289060800803807 / 62500000000000 : ℝ) ≤ Real.log 102 ∧ Real.log 102 ≤ (4624972814865459 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_102
  constructor <;> linarith [h.1, h.2]

theorem eC_102 : (48155712032559 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 102 * cCG cZ 102 ∧ ex (65083 / 100000) 102 * cCG cZ 102 ≤ (48155723400987 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_102 cCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_102 : (13680028629663 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 102 * cCG cZ 102) ∧ kappa * (ex (65083 / 100000) 102 * cCG cZ 102) ≤ (3420007964799 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_102 : (26262028727 / 2500000000000 : ℝ) ≤ ex (65083 / 100000) 102 * sCG cZ 102 ∧ ex (65083 / 100000) 102 * sCG cZ 102 ≤ (10504822810091 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_102 sCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_102 : (298419680403 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 102 * sCG cZ 102) ∧ kappa * (ex (65083 / 100000) 102 * sCG cZ 102) ≤ (746050004901 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_102 : (13919928683409 / 62500000000000 : ℝ) ≤ Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102) ∧ Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102) ≤ (111359455804873 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_102 eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_102 : (7908720061419 / 125000000000000 : ℝ) ≤ kappa * (Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102)) ∧ kappa * (Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102)) ≤ (2530791018211 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_103 : (1158682246951293 / 250000000000000 : ℝ) ≤ Real.log 103 ∧ Real.log 103 ≤ (4634728989815243 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_103
  constructor <;> linarith [h.1, h.2]

theorem eC_103 : (293684654601 / 25000000000000 : ℝ) ≤ ex (65083 / 100000) 103 * cCG cZ 103 ∧ ex (65083 / 100000) 103 * cCG cZ 103 ≤ (11747397485731 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 cCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_103 : (1668593117393 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 103 * cCG cZ 103) ∧ kappa * (ex (65083 / 100000) 103 * cCG cZ 103) ≤ (41714868067 / 12500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_103 : (742913643019 / 15625000000000 : ℝ) ≤ ex (65083 / 100000) 103 * sCG cZ 103 ∧ ex (65083 / 100000) 103 * sCG cZ 103 ≤ (9509296900351 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 sCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_103 : (13506956631349 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 103 * sCG cZ 103) ∧ kappa * (ex (65083 / 100000) 103 * sCG cZ 103) ≤ (105523123869 / 7812500000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_103 : (1701435977441 / 31250000000000 : ℝ) ≤ Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103) ∧ Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103) ≤ (54446003682001 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_103 eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_103 : (15466953780067 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103)) ∧ kappa * (Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103)) ≤ (3093393733383 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_104 : (290274431169741 / 62500000000000 : ℝ) ≤ Real.log 104 ∧ Real.log 104 ≤ (464439090073119 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_104
  constructor <;> linarith [h.1, h.2]

theorem eC_104 : (-3690947034643 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 104 * cCG cZ 104 ∧ ex (65083 / 100000) 104 * cCG cZ 104 ≤ (-36909459062897 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 cCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_104 : (31723523006333 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 104 * sCG cZ 104 ∧ ex (65083 / 100000) 104 * sCG cZ 104 ≤ (15861767140743 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 sCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_104 : (-21427751028471 / 125000000000000 : ℝ) ≤ Real.log 104 * (ex (65083 / 100000) 104 * cCG cZ 104) ∧ Real.log 104 * (ex (65083 / 100000) 104 * cCG cZ 104) ≤ (-42855488937061 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_104 eC_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_106 : (4663439093684591 / 1000000000000000 : ℝ) ≤ Real.log 106 ∧ Real.log 106 ≤ (4663439095709723 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_106
  constructor <;> linarith [h.1, h.2]

theorem eC_106 : (-5094056908461 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 106 * cCG cZ 106 ∧ ex (65083 / 100000) 106 * cCG cZ 106 ≤ (-318377860167 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_106 cCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_106 : (-23899446464477 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 106 * sCG cZ 106 ∧ ex (65083 / 100000) 106 * sCG cZ 106 ≤ (-47798881726859 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_106 sCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_106 : (-742369504459 / 31250000000000 : ℝ) ≤ Real.log 106 * (ex (65083 / 100000) 106 * cCG cZ 106) ∧ Real.log 106 * (ex (65083 / 100000) 106 * cCG cZ 106) ≤ (-11877886077331 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_106 eC_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_107 : (2336414417016759 / 500000000000000 : ℝ) ≤ Real.log 107 ∧ Real.log 107 ≤ (4672828836063211 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_107
  constructor <;> linarith [h.1, h.2]

theorem eC_107 : (39296320865319 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 107 * cCG cZ 107 ∧ ex (65083 / 100000) 107 * cCG cZ 107 ≤ (19648166001977 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 cCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_107 : (2232652251573 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 107 * cCG cZ 107) ∧ kappa * (ex (65083 / 100000) 107 * cCG cZ 107) ≤ (11163264422119 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_107 : (-27173740334247 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 107 * sCG cZ 107 ∧ ex (65083 / 100000) 107 * sCG cZ 107 ≤ (-27173729211861 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 sCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_107 : (-7719490171721 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 107 * sCG cZ 107) ∧ kappa * (ex (65083 / 100000) 107 * sCG cZ 107) ≤ (-7719487012083 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_107 : (36724996242179 / 200000000000000 : ℝ) ≤ Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107) ∧ Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107) ≤ (18362503333959 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_107 eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_107 : (13041002271901 / 250000000000000 : ℝ) ≤ kappa * (Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107)) ∧ kappa * (Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107)) ≤ (2086560955851 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_108 : (58526640333687 / 12500000000000 : ℝ) ≤ Real.log 108 ∧ Real.log 108 ≤ (292633201795563 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_108
  constructor <;> linarith [h.1, h.2]

theorem eC_108 : (21307663386723 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 108 * cCG cZ 108 ∧ ex (65083 / 100000) 108 * cCG cZ 108 ≤ (42615337891911 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 cCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_108 : (12106121282747 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 108 * cCG cZ 108) ∧ kappa * (ex (65083 / 100000) 108 * cCG cZ 108) ≤ (12106124441271 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_108 : (10477044805359 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 108 * sCG cZ 108 ∧ ex (65083 / 100000) 108 * sCG cZ 108 ≤ (2619262587561 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 sCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_108 : (5952617741159 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 108 * sCG cZ 108) ∧ kappa * (ex (65083 / 100000) 108 * sCG cZ 108) ≤ (5952620891531 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_108 : (199530552221761 / 1000000000000000 : ℝ) ≤ Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108) ∧ Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108) ≤ (49882651091639 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_108 eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_108 : (56682448492107 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108)) ∧ kappa * (Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108)) ≤ (56682463305351 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_109 : (4691347881799053 / 1000000000000000 : ℝ) ≤ Real.log 109 ∧ Real.log 109 ≤ (4691347883837257 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_109
  constructor <;> linarith [h.1, h.2]

theorem eC_109 : (1453065888033 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 109 * cCG cZ 109 ∧ ex (65083 / 100000) 109 * cCG cZ 109 ≤ (726535700143 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 cCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_109 : (47114767594909 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 109 * sCG cZ 109 ∧ ex (65083 / 100000) 109 * sCG cZ 109 ≤ (23557389339041 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 sCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_109 : (3408418787969 / 250000000000000 : ℝ) ≤ Real.log 109 * (ex (65083 / 100000) 109 * cCG cZ 109) ∧ Real.log 109 * (ex (65083 / 100000) 109 * cCG cZ 109) ≤ (13633726877593 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_109 eC_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_111 : (4709530200880691 / 1000000000000000 : ℝ) ≤ Real.log 111 ∧ Real.log 111 ≤ (4709530202926659 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_111
  constructor <;> linarith [h.1, h.2]

theorem eC_111 : (-42138897837901 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 111 * cCG cZ 111 ∧ ex (65083 / 100000) 111 * cCG cZ 111 ≤ (-42138886853721 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 cCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_111 : (-10005551538991 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 111 * sCG cZ 111 ∧ ex (65083 / 100000) 111 * sCG cZ 111 ≤ (-5002773030821 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 sCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_111 : (-49613603021409 / 250000000000000 : ℝ) ≤ Real.log 111 * (ex (65083 / 100000) 111 * cCG cZ 111) ∧ Real.log 111 * (ex (65083 / 100000) 111 * cCG cZ 111) ≤ (-198454360269093 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_111 eC_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_112 : (2359249435431363 / 500000000000000 : ℝ) ≤ Real.log 112 ∧ Real.log 112 ≤ (4718498872912321 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_112
  constructor <;> linarith [h.1, h.2]

theorem eC_112 : (-2396888469893 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 112 * cCG cZ 112 ∧ ex (65083 / 100000) 112 * cCG cZ 112 ≤ (-4793766057263 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 cCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_112 : (-1361811569439 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 112 * cCG cZ 112) ∧ kappa * (ex (65083 / 100000) 112 * cCG cZ 112) ≤ (-1361808477941 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_112 : (-46129098805089 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 112 * sCG cZ 112 ∧ ex (65083 / 100000) 112 * sCG cZ 112 ≤ (-11532271966851 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 sCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_112 : (-1310431028177 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 112 * sCG cZ 112) ∧ kappa * (ex (65083 / 100000) 112 * sCG cZ 112) ≤ (-6552153587301 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_112 : (-11309715543687 / 500000000000000 : ℝ) ≤ Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112) ∧ Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112) ≤ (-180955037827 / 8000000000000 : ℝ) := by
  exact mul_bounds_of lgB_112 eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_112 : (-1606426588879 / 250000000000000 : ℝ) ≤ kappa * (Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112)) ∧ kappa * (Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112)) ≤ (-6425691765499 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_113 : (2363693909139639 / 500000000000000 : ℝ) ≤ Real.log 113 ∧ Real.log 113 ≤ (4727387820332341 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_113
  constructor <;> linarith [h.1, h.2]

theorem eC_113 : (36439142020869 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 113 * cCG cZ 113 ∧ ex (65083 / 100000) 113 * cCG cZ 113 ≤ (36439152893991 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_113 cCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_113 : (10351596623653 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 113 * cCG cZ 113) ∧ kappa * (ex (65083 / 100000) 113 * cCG cZ 113) ≤ (64697498203 / 6250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_113 : (-14127272529181 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 113 * sCG cZ 113 ∧ ex (65083 / 100000) 113 * sCG cZ 113 ≤ (-17659083873 / 625000000000 : ℝ) := by
  exact mul_bounds_of exB_113 sCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_113 : (-4013262072163 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 113 * sCG cZ 113) ∧ kappa * (ex (65083 / 100000) 113 * sCG cZ 113) ≤ (-8026521058783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_113 : (43065489024501 / 250000000000000 : ℝ) ≤ Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113) ∧ Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113) ≤ (86131003787141 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_113 eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_113 : (61170014723 / 1250000000000 : ℝ) ≤ kappa * (Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113)) ∧ kappa * (Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113)) ≤ (48936026401733 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_114 : (4736198447960769 / 1000000000000000 : ℝ) ≤ Real.log 114 ∧ Real.log 114 ≤ (4736198450017151 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_114
  constructor <;> linarith [h.1, h.2]

theorem eC_114 : (21562350656437 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 114 * cCG cZ 114 ∧ ex (65083 / 100000) 114 * cCG cZ 114 ≤ (43124712137789 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_114 cCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_114 : (1945129563061 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 114 * sCG cZ 114 ∧ ex (65083 / 100000) 114 * sCG cZ 114 ≤ (972565455781 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_114 sCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_114 : (40849428685361 / 200000000000000 : ℝ) ≤ Real.log 114 * (ex (65083 / 100000) 114 * cCG cZ 114) ∧ Real.log 114 * (ex (65083 / 100000) 114 * cCG cZ 114) ≤ (204247194784433 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_114 eC_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_116 : (950718038134279 / 200000000000000 : ℝ) ≤ Real.log 116 ∧ Real.log 116 ≤ (4753590192733993 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_116
  constructor <;> linarith [h.1, h.2]

theorem eC_116 : (-31261895392117 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 116 * cCG cZ 116 ∧ ex (65083 / 100000) 116 * cCG cZ 116 ≤ (-781547116399 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 cCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_116 : (1025805703343 / 31250000000000 : ℝ) ≤ ex (65083 / 100000) 116 * sCG cZ 116 ∧ ex (65083 / 100000) 116 * sCG cZ 116 ≤ (16412896624297 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 sCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_116 : (-37151559835561 / 250000000000000 : ℝ) ≤ Real.log 116 * (ex (65083 / 100000) 116 * cCG cZ 116) ∧ Real.log 116 * (ex (65083 / 100000) 116 * cCG cZ 116) ≤ (-18575773530309 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_116 eC_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_117 : (1190543483590551 / 250000000000000 : ℝ) ≤ Real.log 117 ∧ Real.log 117 ≤ (952434787285543 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_117
  constructor <;> linarith [h.1, h.2]

theorem eC_117 : (-44426818632833 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 117 * cCG cZ 117 ∧ ex (65083 / 100000) 117 * cCG cZ 117 ≤ (-44426807907301 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 cCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_117 : (-12620728158087 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 117 * cCG cZ 117) ∧ kappa * (ex (65083 / 100000) 117 * cCG cZ 117) ≤ (-12620725111187 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_117 : (-7633171214739 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 117 * sCG cZ 117 ∧ ex (65083 / 100000) 117 * sCG cZ 117 ≤ (-7633160538693 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 sCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_117 : (-1084211990077 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 117 * sCG cZ 117) ∧ kappa * (ex (65083 / 100000) 117 * sCG cZ 117) ≤ (-135526309207 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_117 : (-211568237771679 / 1000000000000000 : ℝ) ≤ Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117) ∧ Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117) ≤ (-42313637320613 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_117 eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_117 : (-3005105134659 / 50000000000000 : ℝ) ≤ kappa * (Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117)) ∧ kappa * (Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117)) ≤ (-939095127457 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_118 : (954136924805911 / 200000000000000 : ℝ) ≤ Real.log 118 ∧ Real.log 118 ≤ (74541947282779 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_118
  constructor <;> linarith [h.1, h.2]

theorem eC_118 : (-372969389999 / 20000000000000 : ℝ) ≤ ex (65083 / 100000) 118 * cCG cZ 118 ∧ ex (65083 / 100000) 118 * cCG cZ 118 ≤ (-18648458881503 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 cCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_118 : (-5297639384633 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 118 * cCG cZ 118) ∧ kappa * (ex (65083 / 100000) 118 * cCG cZ 118) ≤ (-2648818184077 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_118 : (-40765865390163 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 118 * sCG cZ 118 ∧ ex (65083 / 100000) 118 * sCG cZ 118 ≤ (-20382927370963 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 sCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_118 : (-2316145612273 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 118 * sCG cZ 118) ∧ kappa * (ex (65083 / 100000) 118 * sCG cZ 118) ≤ (-11580725036423 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_118 : (-88965966743667 / 1000000000000000 : ℝ) ≤ Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118) ∧ Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118) ≤ (-88965916047833 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_118 eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_118 : (-25273366766879 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118)) ∧ kappa * (Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118)) ≤ (-12636676182627 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_119 : (955824698534977 / 200000000000000 : ℝ) ≤ Real.log 119 ∧ Real.log 119 ≤ (238956174737293 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_119
  constructor <;> linarith [h.1, h.2]

theorem eC_119 : (2838298632177 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 119 * cCG cZ 119 ∧ ex (65083 / 100000) 119 * cCG cZ 119 ≤ (709574989471 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_119 cCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_119 : (-1198993177597 / 31250000000000 : ℝ) ≤ ex (65083 / 100000) 119 * sCG cZ 119 ∧ ex (65083 / 100000) 119 * sCG cZ 119 ≤ (-38367771056279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_119 sCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_119 : (1695572459033 / 15625000000000 : ℝ) ≤ Real.log 119 * (ex (65083 / 100000) 119 * cCG cZ 119) ∧ Real.log 119 * (ex (65083 / 100000) 119 * cCG cZ 119) ≤ (108516688110877 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_119 eC_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_121 : (4795790545159091 / 1000000000000000 : ℝ) ≤ Real.log 121 ∧ Real.log 121 ≤ (1198947636808773 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_121
  constructor <;> linarith [h.1, h.2]

theorem eC_121 : (14280657737983 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 121 * cCG cZ 121 ∧ ex (65083 / 100000) 121 * cCG cZ 121 ≤ (28561325978897 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 cCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_121 : (4200557091551 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 121 * sCG cZ 121 ∧ ex (65083 / 100000) 121 * sCG cZ 121 ≤ (33604467243457 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 sCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_121 : (136974086716943 / 1000000000000000 : ℝ) ≤ Real.log 121 * (ex (65083 / 100000) 121 * cCG cZ 121) ∧ Real.log 121 * (ex (65083 / 100000) 121 * cCG cZ 121) ≤ (27394827429219 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_121 eC_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_122 : (4804021044295607 / 1000000000000000 : ℝ) ≤ Real.log 122 ∧ Real.log 122 ≤ (4804021046371607 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_122
  constructor <;> linarith [h.1, h.2]

theorem eC_122 : (-10221294605141 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 122 * cCG cZ 122 ∧ ex (65083 / 100000) 122 * cCG cZ 122 ≤ (-10221284181013 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 cCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_122 : (-18147847489 / 6250000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 122 * cCG cZ 122) ∧ kappa * (ex (65083 / 100000) 122 * cCG cZ 122) ≤ (-2903652636963 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_122 : (2666200069289 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 122 * sCG cZ 122 ∧ ex (65083 / 100000) 122 * sCG cZ 122 ≤ (21329605788301 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 sCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_122 : (12118585061933 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 122 * sCG cZ 122) ∧ kappa * (ex (65083 / 100000) 122 * sCG cZ 122) ≤ (12118588035667 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_122 : (-24551657202131 / 500000000000000 : ℝ) ≤ Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122) ∧ Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122) ≤ (-1534477009541 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_122 eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_122 : (-6974611302679 / 500000000000000 : ℝ) ≤ kappa * (Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122)) ∧ kappa * (Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122)) ≤ (-871825523331 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_123 : (300761522183423 / 62500000000000 : ℝ) ≤ Real.log 123 ∧ Real.log 123 ≤ (300761522313173 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_123
  constructor <;> linarith [h.1, h.2]

theorem eC_123 : (-2507940081539 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 123 * cCG cZ 123 ∧ ex (65083 / 100000) 123 * cCG cZ 123 ≤ (-20063515437611 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_123 cCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_123 : (-11399251525963 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 123 * cCG cZ 123) ∧ kappa * (ex (65083 / 100000) 123 * cCG cZ 123) ≤ (-11399248563187 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_123 : (17139560709467 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 123 * sCG cZ 123 ∧ ex (65083 / 100000) 123 * sCG cZ 123 ≤ (1071223194237 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_123 sCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_123 : (486899001819 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 123 * sCG cZ 123) ∧ kappa * (ex (65083 / 100000) 123 * sCG cZ 123) ≤ (4868992972137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_123 : (-193098720459237 / 1000000000000000 : ℝ) ≤ Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123) ∧ Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123) ≤ (-193098670187727 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_123 eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_123 : (-13713824968717 / 250000000000000 : ℝ) ≤ kappa * (Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123)) ∧ kappa * (Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123)) ≤ (-6856910699223 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_124 : (4820281565167387 / 1000000000000000 : ℝ) ≤ Real.log 124 ∧ Real.log 124 ≤ (1205070391810847 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_124
  constructor <;> linarith [h.1, h.2]

theorem eC_124 : (-18825922045027 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 124 * cCG cZ 124 ∧ ex (65083 / 100000) 124 * cCG cZ 124 ≤ (-37651833732559 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 cCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_124 : (-863778825647 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 124 * sCG cZ 124 ∧ ex (65083 / 100000) 124 * sCG cZ 124 ≤ (-21594460305421 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 sCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_124 : (-18149249004001 / 100000000000000 : ℝ) ≤ Real.log 124 * (ex (65083 / 100000) 124 * cCG cZ 124) ∧ Real.log 124 * (ex (65083 / 100000) 124 * cCG cZ 124) ≤ (-181492440035801 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_124 eC_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_126 : (1209070476628457 / 250000000000000 : ℝ) ≤ Real.log 126 ∧ Real.log 126 ≤ (4836281908589829 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_126
  constructor <;> linarith [h.1, h.2]

theorem eC_126 : (3010504942559 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 126 * cCG cZ 126 ∧ ex (65083 / 100000) 126 * cCG cZ 126 ≤ (30105059674619 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_126 cCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_126 : (-30640430766551 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 126 * sCG cZ 126 ∧ ex (65083 / 100000) 126 * sCG cZ 126 ≤ (-15320210256371 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_126 sCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_126 : (29119301166337 / 200000000000000 : ℝ) ≤ Real.log 126 * (ex (65083 / 100000) 126 * cCG cZ 126) ∧ Real.log 126 * (ex (65083 / 100000) 126 * cCG cZ 126) ≤ (72798277730689 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_126 eC_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_127 : (4844187086020941 / 1000000000000000 : ℝ) ≤ Real.log 127 ∧ Real.log 127 ≤ (2422093544048471 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_127
  constructor <;> linarith [h.1, h.2]

theorem eC_127 : (42484535901923 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 127 * cCG cZ 127 ∧ ex (65083 / 100000) 127 * cCG cZ 127 ≤ (42484546111909 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_127 cCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_127 : (12068966337021 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 127 * cCG cZ 127) ∧ kappa * (ex (65083 / 100000) 127 * cCG cZ 127) ≤ (6034484618733 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_127 : (4617872124077 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 127 * sCG cZ 127 ∧ ex (65083 / 100000) 127 * sCG cZ 127 ≤ (461788228287 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_127 sCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_127 : (262368139517 / 200000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 127 * sCG cZ 127) ∧ kappa * (ex (65083 / 100000) 127 * sCG cZ 127) ≤ (655921791743 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_127 : (25725380021461 / 125000000000000 : ℝ) ≤ Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127) ∧ Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127) ≤ (205803089718969 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_127 eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_127 : (58464330871423 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127)) ∧ kappa * (Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127)) ≤ (3654021559173 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_128 : (4852030263481967 / 1000000000000000 : ℝ) ≤ Real.log 128 ∧ Real.log 128 ≤ (303251891597373 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_128
  constructor <;> linarith [h.1, h.2]

theorem eC_128 : (4568107892747 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 128 * cCG cZ 128 ∧ ex (65083 / 100000) 128 * cCG cZ 128 ≤ (5710137394627 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_128 cCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_128 : (6488518611657 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 128 * cCG cZ 128) ∧ kappa * (ex (65083 / 100000) 128 * cCG cZ 128) ≤ (6488521485053 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_128 : (8965281832239 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 128 * sCG cZ 128 ∧ ex (65083 / 100000) 128 * sCG cZ 128 ≤ (1434445498457 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_128 sCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_128 : (10187394762649 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 128 * sCG cZ 128) ∧ kappa * (ex (65083 / 100000) 128 * sCG cZ 128) ≤ (636712352567 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_128 : (13852873589037 / 125000000000000 : ℝ) ≤ Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128) ∧ Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128) ≤ (110823037836899 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_128 eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_128 : (1259299546757 / 40000000000000 : ℝ) ≤ kappa * (Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128)) ∧ kappa * (Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128)) ≤ (31482502624197 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_129 : (2429906201962011 / 500000000000000 : ℝ) ≤ Real.log 129 ∧ Real.log 129 ≤ (4859812406000023 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_129
  constructor <;> linarith [h.1, h.2]

theorem eC_129 : (-3339904161743 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 129 * cCG cZ 129 ∧ ex (65083 / 100000) 129 * cCG cZ 129 ≤ (-6679803288927 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 cCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_129 : (401374204569 / 10000000000000 : ℝ) ≤ ex (65083 / 100000) 129 * sCG cZ 129 ∧ ex (65083 / 100000) 129 * sCG cZ 129 ≤ (40137430562221 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 sCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_129 : (-64925230720359 / 1000000000000000 : ℝ) ≤ Real.log 129 * (ex (65083 / 100000) 129 * cCG cZ 129) ∧ Real.log 129 * (ex (65083 / 100000) 129 * cCG cZ 129) ≤ (-64925181758599 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_129 eC_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_131 : (2437598661381751 / 500000000000000 : ℝ) ≤ Real.log 131 ∧ Real.log 131 ≤ (2437598662419751 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_131
  constructor <;> linarith [h.1, h.2]

theorem eC_131 : (-36614359355781 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 131 * cCG cZ 131 ∧ ex (65083 / 100000) 131 * cCG cZ 131 ≤ (-36614349367577 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_131 cCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_131 : (-20332279740151 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 131 * sCG cZ 131 ∧ ex (65083 / 100000) 131 * sCG cZ 131 ≤ (-635383430437 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_131 sCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_131 : (-2789097293469 / 15625000000000 : ℝ) ≤ Real.log 131 * (ex (65083 / 100000) 131 * cCG cZ 131) ∧ Real.log 131 * (ex (65083 / 100000) 131 * cCG cZ 131) ≤ (-89251089005769 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_131 eC_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_132 : (4882801922148721 / 1000000000000000 : ℝ) ≤ Real.log 132 ∧ Real.log 132 ≤ (2441400962112361 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_132
  constructor <;> linarith [h.1, h.2]

theorem eC_132 : (-2026123361619 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 132 * cCG cZ 132 ∧ ex (65083 / 100000) 132 * cCG cZ 132 ≤ (-405224176967 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_132 cCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_132 : (-1151158374543 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 132 * cCG cZ 132) ∧ kappa * (ex (65083 / 100000) 132 * cCG cZ 132) ≤ (-575578483669 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_132 : (-4087851993319 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 132 * sCG cZ 132 ∧ ex (65083 / 100000) 132 * sCG cZ 132 ≤ (-2554906873859 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_132 sCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_132 : (-1451591357029 / 125000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 132 * sCG cZ 132) ∧ kappa * (ex (65083 / 100000) 132 * sCG cZ 132) ≤ (-5806364014617 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_132 : (-989315904883 / 25000000000000 : ℝ) ≤ Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132) ∧ Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132) ≤ (-4946573475489 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_132 eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_132 : (-2810439163153 / 250000000000000 : ℝ) ≤ kappa * (Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132)) ∧ kappa * (Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132)) ≤ (-5620871452813 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_133 : (611293640973013 / 125000000000000 : ℝ) ≤ Real.log 133 ∧ Real.log 133 ≤ (978069825972021 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_133
  constructor <;> linarith [h.1, h.2]

theorem eC_133 : (25618587602701 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 133 * cCG cZ 133 ∧ ex (65083 / 100000) 133 * cCG cZ 133 ≤ (6404649371309 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 cCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_133 : (7277703870717 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 133 * cCG cZ 133) ∧ kappa * (ex (65083 / 100000) 133 * cCG cZ 133) ≤ (7277706678139 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_133 : (-16305258189149 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 133 * sCG cZ 133 ∧ ex (65083 / 100000) 133 * sCG cZ 133 ≤ (-6522101297137 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 sCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_133 : (-926396431189 / 100000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 133 * sCG cZ 133) ∧ kappa * (ex (65083 / 100000) 133 * sCG cZ 133) ≤ (-2315990375401 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_133 : (125283837537929 / 1000000000000000 : ℝ) ≤ Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133) ∧ Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133) ≤ (125283885920161 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_133 eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_133 : (2224407048527 / 62500000000000 : ℝ) ≤ kappa * (Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133)) ∧ kappa * (Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133)) ≤ (35590526520811 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_134 : (2448919899756631 / 500000000000000 : ℝ) ≤ Real.log 134 ∧ Real.log 134 ≤ (2448919900794631 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_134
  constructor <;> linarith [h.1, h.2]

theorem eC_134 : (41217232859623 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 134 * cCG cZ 134 ∧ ex (65083 / 100000) 134 * cCG cZ 134 ≤ (2060862135287 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_134 cCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_134 : (-1025961084359 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 134 * sCG cZ 134 ∧ ex (65083 / 100000) 134 * sCG cZ 134 ≤ (-8015282717 / 3906250000000 : ℝ) := by
  exact mul_bounds_of exB_134 sCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_134 : (201875403525667 / 1000000000000000 : ℝ) ≤ Real.log 134 * (ex (65083 / 100000) 134 * cCG cZ 134) ∧ Real.log 134 * (ex (65083 / 100000) 134 * cCG cZ 134) ≤ (201875451835939 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_134 eC_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_136 : (2456327442649201 / 500000000000000 : ℝ) ≤ Real.log 136 ∧ Real.log 136 ≤ (4912654887374403 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_136
  constructor <;> linarith [h.1, h.2]

theorem eC_136 : (-2891403512527 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 136 * cCG cZ 136 ∧ ex (65083 / 100000) 136 * cCG cZ 136 ≤ (-2891393797727 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 cCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_136 : (40769875443449 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 136 * sCG cZ 136 ∧ ex (65083 / 100000) 136 * sCG cZ 136 ≤ (20384942604731 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 sCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_136 : (-3551116899297 / 250000000000000 : ℝ) ≤ Real.log 136 * (ex (65083 / 100000) 136 * cCG cZ 136) ∧ Real.log 136 * (ex (65083 / 100000) 136 * cCG cZ 136) ≤ (-568176794629 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_136 eC_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_137 : (196799237015619 / 40000000000000 : ℝ) ≤ Real.log 137 ∧ Real.log 137 ≤ (1229995231866619 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_137
  constructor <;> linarith [h.1, h.2]

theorem eC_137 : (-3204446526183 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 137 * cCG cZ 137 ∧ ex (65083 / 100000) 137 * cCG cZ 137 ≤ (-32044455560511 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 cCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_137 : (-4551580525979 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 137 * cCG cZ 137) ∧ kappa * (ex (65083 / 100000) 137 * cCG cZ 137) ≤ (-568947393501 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_137 : (12528378124017 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 137 * sCG cZ 137 ∧ ex (65083 / 100000) 137 * sCG cZ 137 ≤ (12528382969659 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 sCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_137 : (7118099356683 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 137 * sCG cZ 137) ∧ kappa * (ex (65083 / 100000) 137 * sCG cZ 137) ≤ (284724084391 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_137 : (-78829078959533 / 500000000000000 : ℝ) ≤ Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137) ∧ Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137) ≤ (-39414527530559 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_137 eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_137 : (-4478737875529 / 100000000000000 : ℝ) ≤ kappa * (Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137)) ∧ kappa * (Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137)) ≤ (-44787365177211 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_138 : (985450736943911 / 200000000000000 : ℝ) ≤ Real.log 138 ∧ Real.log 138 ≤ (1231813421698889 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_138
  constructor <;> linarith [h.1, h.2]

theorem eC_138 : (-9981218583417 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 138 * cCG cZ 138 ∧ ex (65083 / 100000) 138 * cCG cZ 138 ≤ (-9981216167463 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 cCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_138 : (-5670910063079 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 138 * cCG cZ 138) ∧ kappa * (ex (65083 / 100000) 138 * cCG cZ 138) ≤ (-11341817380869 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_138 : (-6715885296541 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 138 * sCG cZ 138 ∧ ex (65083 / 100000) 138 * sCG cZ 138 ≤ (-3357937838813 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 sCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_138 : (-119240142099 / 62500000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 138 * sCG cZ 138) ∧ kappa * (ex (65083 / 100000) 138 * sCG cZ 138) ≤ (-1907839541051 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_138 : (-39343996851083 / 200000000000000 : ℝ) ≤ Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138) ∧ Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138) ≤ (-196719936556457 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_138 eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_138 : (-2794201251579 / 50000000000000 : ℝ) ≤ kappa * (Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138)) ∧ kappa * (Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138)) ≤ (-6985501435163 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_139 : (2467236966346521 / 500000000000000 : ℝ) ≤ Real.log 139 ∧ Real.log 139 ≤ (4934473934769043 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_139
  constructor <;> linarith [h.1, h.2]

theorem eC_139 : (-883132276287 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 139 * cCG cZ 139 ∧ ex (65083 / 100000) 139 * cCG cZ 139 ≤ (-22078297302341 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 cCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_139 : (-33709265325111 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 139 * sCG cZ 139 ∧ ex (65083 / 100000) 139 * sCG cZ 139 ≤ (-6741851140887 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 sCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_139 : (-108944829957287 / 1000000000000000 : ℝ) ≤ Real.log 139 * (ex (65083 / 100000) 139 * cCG cZ 139) ∧ Real.log 139 * (ex (65083 / 100000) 139 * cCG cZ 139) ≤ (-13618097814581 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_139 eC_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_141 : (2474379944970259 / 500000000000000 : ℝ) ≤ Real.log 141 ∧ Real.log 141 ≤ (4948759892016519 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_141
  constructor <;> linarith [h.1, h.2]

theorem lgB_142 : (4955827057163611 / 1000000000000000 : ℝ) ≤ Real.log 142 ∧ Real.log 142 ≤ (1238956764809903 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_142
  constructor <;> linarith [h.1, h.2]

theorem lgB_143 : (4962844629822257 / 1000000000000000 : ℝ) ≤ Real.log 143 ∧ Real.log 143 ≤ (2481422315949129 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_143
  constructor <;> linarith [h.1, h.2]

theorem lgB_144 : (4969813299138351 / 1000000000000000 : ℝ) ≤ Real.log 144 ∧ Real.log 144 ≤ (4969813301214351 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_144
  constructor <;> linarith [h.1, h.2]

theorem PReB_0 : (562083245682027 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 1 * cCG cZ 1 + kappa * (ex (65083 / 100000) 2 * cCG cZ 2) - kappa * (ex (65083 / 100000) 3 * cCG cZ 3) - ex (65083 / 100000) 4 * cCG cZ 4 ∧ ex (65083 / 100000) 1 * cCG cZ 1 + kappa * (ex (65083 / 100000) 2 * cCG cZ 2) - kappa * (ex (65083 / 100000) 3 * cCG cZ 3) - ex (65083 / 100000) 4 * cCG cZ 4 ≤ (281041634028543 / 500000000000000 : ℝ) := by
  have h0 : ex (65083 / 100000) 1 * cCG cZ 1 = (1 : ℝ) := by rw [ex_oneG, cCG_one]; norm_num
  have h1 := keC_2
  have h2 := keC_3
  have h3 := eC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_1 : (-569095280520739 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 6 * cCG cZ 6 + kappa * (ex (65083 / 100000) 7 * cCG cZ 7) - kappa * (ex (65083 / 100000) 8 * cCG cZ 8) - ex (65083 / 100000) 9 * cCG cZ 9 ∧ ex (65083 / 100000) 6 * cCG cZ 6 + kappa * (ex (65083 / 100000) 7 * cCG cZ 7) - kappa * (ex (65083 / 100000) 8 * cCG cZ 8) - ex (65083 / 100000) 9 * cCG cZ 9 ≤ (-284547624332899 / 500000000000000 : ℝ) := by
  have h0 := eC_6
  have h1 := keC_7
  have h2 := keC_8
  have h3 := eC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_2 : (-71498682570993 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 11 * cCG cZ 11 + kappa * (ex (65083 / 100000) 12 * cCG cZ 12) - kappa * (ex (65083 / 100000) 13 * cCG cZ 13) - ex (65083 / 100000) 14 * cCG cZ 14 ∧ ex (65083 / 100000) 11 * cCG cZ 11 + kappa * (ex (65083 / 100000) 12 * cCG cZ 12) - kappa * (ex (65083 / 100000) 13 * cCG cZ 13) - ex (65083 / 100000) 14 * cCG cZ 14 ≤ (-285994704739471 / 1000000000000000 : ℝ) := by
  have h0 := eC_11
  have h1 := keC_12
  have h2 := keC_13
  have h3 := eC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_3 : (5570824063687 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 16 * cCG cZ 16 + kappa * (ex (65083 / 100000) 17 * cCG cZ 17) - kappa * (ex (65083 / 100000) 18 * cCG cZ 18) - ex (65083 / 100000) 19 * cCG cZ 19 ∧ ex (65083 / 100000) 16 * cCG cZ 16 + kappa * (ex (65083 / 100000) 17 * cCG cZ 17) - kappa * (ex (65083 / 100000) 18 * cCG cZ 18) - ex (65083 / 100000) 19 * cCG cZ 19 ≤ (6963536616197 / 250000000000000 : ℝ) := by
  have h0 := eC_16
  have h1 := keC_17
  have h2 := keC_18
  have h3 := eC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_4 : (-34512071730207 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 21 * cCG cZ 21 + kappa * (ex (65083 / 100000) 22 * cCG cZ 22) - kappa * (ex (65083 / 100000) 23 * cCG cZ 23) - ex (65083 / 100000) 24 * cCG cZ 24 ∧ ex (65083 / 100000) 21 * cCG cZ 21 + kappa * (ex (65083 / 100000) 22 * cCG cZ 22) - kappa * (ex (65083 / 100000) 23 * cCG cZ 23) - ex (65083 / 100000) 24 * cCG cZ 24 ≤ (-69024118144139 / 1000000000000000 : ℝ) := by
  have h0 := eC_21
  have h1 := keC_22
  have h2 := keC_23
  have h3 := eC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_5 : (48262351156237 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 26 * cCG cZ 26 + kappa * (ex (65083 / 100000) 27 * cCG cZ 27) - kappa * (ex (65083 / 100000) 28 * cCG cZ 28) - ex (65083 / 100000) 29 * cCG cZ 29 ∧ ex (65083 / 100000) 26 * cCG cZ 26 + kappa * (ex (65083 / 100000) 27 * cCG cZ 27) - kappa * (ex (65083 / 100000) 28 * cCG cZ 28) - ex (65083 / 100000) 29 * cCG cZ 29 ≤ (301639837107 / 6250000000000 : ℝ) := by
  have h0 := eC_26
  have h1 := keC_27
  have h2 := keC_28
  have h3 := eC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_6 : (-116749749056621 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 31 * cCG cZ 31 + kappa * (ex (65083 / 100000) 32 * cCG cZ 32) - kappa * (ex (65083 / 100000) 33 * cCG cZ 33) - ex (65083 / 100000) 34 * cCG cZ 34 ∧ ex (65083 / 100000) 31 * cCG cZ 31 + kappa * (ex (65083 / 100000) 32 * cCG cZ 32) - kappa * (ex (65083 / 100000) 33 * cCG cZ 33) - ex (65083 / 100000) 34 * cCG cZ 34 ≤ (-116749728533953 / 1000000000000000 : ℝ) := by
  have h0 := eC_31
  have h1 := keC_32
  have h2 := keC_33
  have h3 := eC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_7 : (11559124146053 / 100000000000000 : ℝ) ≤ ex (65083 / 100000) 36 * cCG cZ 36 + kappa * (ex (65083 / 100000) 37 * cCG cZ 37) - kappa * (ex (65083 / 100000) 38 * cCG cZ 38) - ex (65083 / 100000) 39 * cCG cZ 39 ∧ ex (65083 / 100000) 36 * cCG cZ 36 + kappa * (ex (65083 / 100000) 37 * cCG cZ 37) - kappa * (ex (65083 / 100000) 38 * cCG cZ 38) - ex (65083 / 100000) 39 * cCG cZ 39 ≤ (57795630069519 / 500000000000000 : ℝ) := by
  have h0 := eC_36
  have h1 := keC_37
  have h2 := keC_38
  have h3 := eC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_8 : (-14412594732427 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 41 * cCG cZ 41 + kappa * (ex (65083 / 100000) 42 * cCG cZ 42) - kappa * (ex (65083 / 100000) 43 * cCG cZ 43) - ex (65083 / 100000) 44 * cCG cZ 44 ∧ ex (65083 / 100000) 41 * cCG cZ 41 + kappa * (ex (65083 / 100000) 42 * cCG cZ 42) - kappa * (ex (65083 / 100000) 43 * cCG cZ 43) - ex (65083 / 100000) 44 * cCG cZ 44 ≤ (-57650361658263 / 1000000000000000 : ℝ) := by
  have h0 := eC_41
  have h1 := keC_42
  have h2 := keC_43
  have h3 := eC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_9 : (-4659803615967 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 46 * cCG cZ 46 + kappa * (ex (65083 / 100000) 47 * cCG cZ 47) - kappa * (ex (65083 / 100000) 48 * cCG cZ 48) - ex (65083 / 100000) 49 * cCG cZ 49 ∧ ex (65083 / 100000) 46 * cCG cZ 46 + kappa * (ex (65083 / 100000) 47 * cCG cZ 47) - kappa * (ex (65083 / 100000) 48 * cCG cZ 48) - ex (65083 / 100000) 49 * cCG cZ 49 ≤ (-11649500997851 / 500000000000000 : ℝ) := by
  have h0 := eC_46
  have h1 := keC_47
  have h2 := keC_48
  have h3 := eC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_10 : (-1216755941503 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 51 * cCG cZ 51 + kappa * (ex (65083 / 100000) 52 * cCG cZ 52) - kappa * (ex (65083 / 100000) 53 * cCG cZ 53) - ex (65083 / 100000) 54 * cCG cZ 54 ∧ ex (65083 / 100000) 51 * cCG cZ 51 + kappa * (ex (65083 / 100000) 52 * cCG cZ 52) - kappa * (ex (65083 / 100000) 53 * cCG cZ 53) - ex (65083 / 100000) 54 * cCG cZ 54 ≤ (-6083764589393 / 1000000000000000 : ℝ) := by
  have h0 := eC_51
  have h1 := keC_52
  have h2 := keC_53
  have h3 := eC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_11 : (-36579343852317 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 56 * cCG cZ 56 + kappa * (ex (65083 / 100000) 57 * cCG cZ 57) - kappa * (ex (65083 / 100000) 58 * cCG cZ 58) - ex (65083 / 100000) 59 * cCG cZ 59 ∧ ex (65083 / 100000) 56 * cCG cZ 56 + kappa * (ex (65083 / 100000) 57 * cCG cZ 57) - kappa * (ex (65083 / 100000) 58 * cCG cZ 58) - ex (65083 / 100000) 59 * cCG cZ 59 ≤ (-1463173116151 / 40000000000000 : ℝ) := by
  have h0 := eC_56
  have h1 := keC_57
  have h2 := keC_58
  have h3 := eC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_12 : (59936181249293 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 61 * cCG cZ 61 + kappa * (ex (65083 / 100000) 62 * cCG cZ 62) - kappa * (ex (65083 / 100000) 63 * cCG cZ 63) - ex (65083 / 100000) 64 * cCG cZ 64 ∧ ex (65083 / 100000) 61 * cCG cZ 61 + kappa * (ex (65083 / 100000) 62 * cCG cZ 62) - kappa * (ex (65083 / 100000) 63 * cCG cZ 63) - ex (65083 / 100000) 64 * cCG cZ 64 ≤ (14984050916617 / 250000000000000 : ℝ) := by
  have h0 := eC_61
  have h1 := keC_62
  have h2 := keC_63
  have h3 := eC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_13 : (-17176994800593 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 66 * cCG cZ 66 + kappa * (ex (65083 / 100000) 67 * cCG cZ 67) - kappa * (ex (65083 / 100000) 68 * cCG cZ 68) - ex (65083 / 100000) 69 * cCG cZ 69 ∧ ex (65083 / 100000) 66 * cCG cZ 66 + kappa * (ex (65083 / 100000) 67 * cCG cZ 67) - kappa * (ex (65083 / 100000) 68 * cCG cZ 68) - ex (65083 / 100000) 69 * cCG cZ 69 ≤ (-1717696827043 / 100000000000000 : ℝ) := by
  have h0 := eC_66
  have h1 := keC_67
  have h2 := keC_68
  have h3 := eC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_14 : (-24658941400497 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 71 * cCG cZ 71 + kappa * (ex (65083 / 100000) 72 * cCG cZ 72) - kappa * (ex (65083 / 100000) 73 * cCG cZ 73) - ex (65083 / 100000) 74 * cCG cZ 74 ∧ ex (65083 / 100000) 71 * cCG cZ 71 + kappa * (ex (65083 / 100000) 72 * cCG cZ 72) - kappa * (ex (65083 / 100000) 73 * cCG cZ 73) - ex (65083 / 100000) 74 * cCG cZ 74 ≤ (-49317868447721 / 500000000000000 : ℝ) := by
  have h0 := eC_71
  have h1 := keC_72
  have h2 := keC_73
  have h3 := eC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_15 : (3568093787259 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 76 * cCG cZ 76 + kappa * (ex (65083 / 100000) 77 * cCG cZ 77) - kappa * (ex (65083 / 100000) 78 * cCG cZ 78) - ex (65083 / 100000) 79 * cCG cZ 79 ∧ ex (65083 / 100000) 76 * cCG cZ 76 + kappa * (ex (65083 / 100000) 77 * cCG cZ 77) - kappa * (ex (65083 / 100000) 78 * cCG cZ 78) - ex (65083 / 100000) 79 * cCG cZ 79 ≤ (14272390025663 / 500000000000000 : ℝ) := by
  have h0 := eC_76
  have h1 := keC_77
  have h2 := keC_78
  have h3 := eC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_16 : (53396543707781 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 81 * cCG cZ 81 + kappa * (ex (65083 / 100000) 82 * cCG cZ 82) - kappa * (ex (65083 / 100000) 83 * cCG cZ 83) - ex (65083 / 100000) 84 * cCG cZ 84 ∧ ex (65083 / 100000) 81 * cCG cZ 81 + kappa * (ex (65083 / 100000) 82 * cCG cZ 82) - kappa * (ex (65083 / 100000) 83 * cCG cZ 83) - ex (65083 / 100000) 84 * cCG cZ 84 ≤ (106793117686789 / 1000000000000000 : ℝ) := by
  have h0 := eC_81
  have h1 := keC_82
  have h2 := keC_83
  have h3 := eC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_17 : (478534972621 / 4000000000000 : ℝ) ≤ ex (65083 / 100000) 86 * cCG cZ 86 + kappa * (ex (65083 / 100000) 87 * cCG cZ 87) - kappa * (ex (65083 / 100000) 88 * cCG cZ 88) - ex (65083 / 100000) 89 * cCG cZ 89 ∧ ex (65083 / 100000) 86 * cCG cZ 86 + kappa * (ex (65083 / 100000) 87 * cCG cZ 87) - kappa * (ex (65083 / 100000) 88 * cCG cZ 88) - ex (65083 / 100000) 89 * cCG cZ 89 ≤ (59816886708891 / 500000000000000 : ℝ) := by
  have h0 := eC_86
  have h1 := keC_87
  have h2 := keC_88
  have h3 := eC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_18 : (59076813701517 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 91 * cCG cZ 91 + kappa * (ex (65083 / 100000) 92 * cCG cZ 92) - kappa * (ex (65083 / 100000) 93 * cCG cZ 93) - ex (65083 / 100000) 94 * cCG cZ 94 ∧ ex (65083 / 100000) 91 * cCG cZ 91 + kappa * (ex (65083 / 100000) 92 * cCG cZ 92) - kappa * (ex (65083 / 100000) 93 * cCG cZ 93) - ex (65083 / 100000) 94 * cCG cZ 94 ≤ (118153657423099 / 1000000000000000 : ℝ) := by
  have h0 := eC_91
  have h1 := keC_92
  have h2 := keC_93
  have h3 := eC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_19 : (56243938809387 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 96 * cCG cZ 96 + kappa * (ex (65083 / 100000) 97 * cCG cZ 97) - kappa * (ex (65083 / 100000) 98 * cCG cZ 98) - ex (65083 / 100000) 99 * cCG cZ 99 ∧ ex (65083 / 100000) 96 * cCG cZ 96 + kappa * (ex (65083 / 100000) 97 * cCG cZ 97) - kappa * (ex (65083 / 100000) 98 * cCG cZ 98) - ex (65083 / 100000) 99 * cCG cZ 99 ≤ (112487907239357 / 1000000000000000 : ℝ) := by
  have h0 := eC_96
  have h1 := keC_97
  have h2 := keC_98
  have h3 := eC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_20 : (38848784099471 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 101 * cCG cZ 101 + kappa * (ex (65083 / 100000) 102 * cCG cZ 102) - kappa * (ex (65083 / 100000) 103 * cCG cZ 103) - ex (65083 / 100000) 104 * cCG cZ 104 ∧ ex (65083 / 100000) 101 * cCG cZ 101 + kappa * (ex (65083 / 100000) 102 * cCG cZ 102) - kappa * (ex (65083 / 100000) 103 * cCG cZ 103) - ex (65083 / 100000) 104 * cCG cZ 104 ≤ (15539519461699 / 200000000000000 : ℝ) := by
  have h0 := eC_101
  have h1 := keC_102
  have h2 := keC_103
  have h3 := eC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_21 : (-8943062892439 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 106 * cCG cZ 106 + kappa * (ex (65083 / 100000) 107 * cCG cZ 107) - kappa * (ex (65083 / 100000) 108 * cCG cZ 108) - ex (65083 / 100000) 109 * cCG cZ 109 ∧ ex (65083 / 100000) 106 * cCG cZ 106 + kappa * (ex (65083 / 100000) 107 * cCG cZ 107) - kappa * (ex (65083 / 100000) 108 * cCG cZ 108) - ex (65083 / 100000) 109 * cCG cZ 109 ≤ (-4471517199683 / 500000000000000 : ℝ) := by
  have h0 := eC_106
  have h1 := keC_107
  have h2 := keC_108
  have h3 := eC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_22 : (-96977021257609 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 111 * cCG cZ 111 + kappa * (ex (65083 / 100000) 112 * cCG cZ 112) - kappa * (ex (65083 / 100000) 113 * cCG cZ 113) - ex (65083 / 100000) 114 * cCG cZ 114 ∧ ex (65083 / 100000) 111 * cCG cZ 111 + kappa * (ex (65083 / 100000) 112 * cCG cZ 112) - kappa * (ex (65083 / 100000) 113 * cCG cZ 113) - ex (65083 / 100000) 114 * cCG cZ 114 ≤ (-96976993268189 / 1000000000000000 : ℝ) := by
  have h0 := eC_111
  have h1 := keC_112
  have h2 := keC_113
  have h3 := eC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_23 : (-30645693422561 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 116 * cCG cZ 116 + kappa * (ex (65083 / 100000) 117 * cCG cZ 117) - kappa * (ex (65083 / 100000) 118 * cCG cZ 118) - ex (65083 / 100000) 119 * cCG cZ 119 ∧ ex (65083 / 100000) 116 * cCG cZ 116 + kappa * (ex (65083 / 100000) 117 * cCG cZ 117) - kappa * (ex (65083 / 100000) 118 * cCG cZ 118) - ex (65083 / 100000) 119 * cCG cZ 119 ≤ (-6129135943993 / 100000000000000 : ℝ) := by
  have h0 := eC_116
  have h1 := keC_117
  have h2 := keC_118
  have h3 := eC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_24 : (2334648192921 / 31250000000000 : ℝ) ≤ ex (65083 / 100000) 121 * cCG cZ 121 + kappa * (ex (65083 / 100000) 122 * cCG cZ 122) - kappa * (ex (65083 / 100000) 123 * cCG cZ 123) - ex (65083 / 100000) 124 * cCG cZ 124 ∧ ex (65083 / 100000) 121 * cCG cZ 121 + kappa * (ex (65083 / 100000) 122 * cCG cZ 122) - kappa * (ex (65083 / 100000) 123 * cCG cZ 123) - ex (65083 / 100000) 124 * cCG cZ 124 ≤ (74708768957951 / 1000000000000000 : ℝ) := by
  have h0 := eC_121
  have h1 := keC_122
  have h2 := keC_123
  have h3 := eC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_25 : (12261275213853 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 126 * cCG cZ 126 + kappa * (ex (65083 / 100000) 127 * cCG cZ 127) - kappa * (ex (65083 / 100000) 128 * cCG cZ 128) - ex (65083 / 100000) 129 * cCG cZ 129 ∧ ex (65083 / 100000) 126 * cCG cZ 126 + kappa * (ex (65083 / 100000) 127 * cCG cZ 127) - kappa * (ex (65083 / 100000) 128 * cCG cZ 128) - ex (65083 / 100000) 129 * cCG cZ 129 ≤ (245225634737 / 5000000000000 : ℝ) := by
  have h0 := eC_126
  have h1 := keC_127
  have h2 := keC_128
  have h3 := eC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_26 : (-43705812744373 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 131 * cCG cZ 131 + kappa * (ex (65083 / 100000) 132 * cCG cZ 132) - kappa * (ex (65083 / 100000) 133 * cCG cZ 133) - ex (65083 / 100000) 134 * cCG cZ 134 ∧ ex (65083 / 100000) 131 * cCG cZ 131 + kappa * (ex (65083 / 100000) 132 * cCG cZ 132) - kappa * (ex (65083 / 100000) 133 * cCG cZ 133) - ex (65083 / 100000) 134 * cCG cZ 134 ≤ (-87411600032593 / 1000000000000000 : ℝ) := by
  have h0 := eC_131
  have h1 := keC_132
  have h2 := keC_133
  have h3 := eC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_27 : (857022004749 / 40000000000000 : ℝ) ≤ ex (65083 / 100000) 136 * cCG cZ 136 + kappa * (ex (65083 / 100000) 137 * cCG cZ 137) - kappa * (ex (65083 / 100000) 138 * cCG cZ 138) - ex (65083 / 100000) 139 * cCG cZ 139 ∧ ex (65083 / 100000) 136 * cCG cZ 136 + kappa * (ex (65083 / 100000) 137 * cCG cZ 137) - kappa * (ex (65083 / 100000) 138 * cCG cZ 138) - ex (65083 / 100000) 139 * cCG cZ 139 ≤ (2142557493959 / 100000000000000 : ℝ) := by
  have h0 := eC_136
  have h1 := keC_137
  have h2 := keC_138
  have h3 := eC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_0 : (-443372850231693 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 1 * sCG cZ 1 + kappa * (ex (65083 / 100000) 2 * sCG cZ 2) - kappa * (ex (65083 / 100000) 3 * sCG cZ 3) - ex (65083 / 100000) 4 * sCG cZ 4 ∧ ex (65083 / 100000) 1 * sCG cZ 1 + kappa * (ex (65083 / 100000) 2 * sCG cZ 2) - kappa * (ex (65083 / 100000) 3 * sCG cZ 3) - ex (65083 / 100000) 4 * sCG cZ 4 ≤ (-110843206959863 / 250000000000000 : ℝ) := by
  have h0 : ex (65083 / 100000) 1 * sCG cZ 1 = (0 : ℝ) := by rw [sCG_one]; norm_num
  have h1 := keS_2
  have h2 := keS_3
  have h3 := eS_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_1 : (69714679856267 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 6 * sCG cZ 6 + kappa * (ex (65083 / 100000) 7 * sCG cZ 7) - kappa * (ex (65083 / 100000) 8 * sCG cZ 8) - ex (65083 / 100000) 9 * sCG cZ 9 ∧ ex (65083 / 100000) 6 * sCG cZ 6 + kappa * (ex (65083 / 100000) 7 * sCG cZ 7) - kappa * (ex (65083 / 100000) 8 * sCG cZ 8) - ex (65083 / 100000) 9 * sCG cZ 9 ≤ (139429391515297 / 1000000000000000 : ℝ) := by
  have h0 := eS_6
  have h1 := keS_7
  have h2 := keS_8
  have h3 := eS_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_2 : (5584486411679 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 11 * sCG cZ 11 + kappa * (ex (65083 / 100000) 12 * sCG cZ 12) - kappa * (ex (65083 / 100000) 13 * sCG cZ 13) - ex (65083 / 100000) 14 * sCG cZ 14 ∧ ex (65083 / 100000) 11 * sCG cZ 11 + kappa * (ex (65083 / 100000) 12 * sCG cZ 12) - kappa * (ex (65083 / 100000) 13 * sCG cZ 13) - ex (65083 / 100000) 14 * sCG cZ 14 ≤ (22337958387811 / 500000000000000 : ℝ) := by
  have h0 := eS_11
  have h1 := keS_12
  have h2 := keS_13
  have h3 := eS_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_3 : (62535696694033 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 16 * sCG cZ 16 + kappa * (ex (65083 / 100000) 17 * sCG cZ 17) - kappa * (ex (65083 / 100000) 18 * sCG cZ 18) - ex (65083 / 100000) 19 * sCG cZ 19 ∧ ex (65083 / 100000) 16 * sCG cZ 16 + kappa * (ex (65083 / 100000) 17 * sCG cZ 17) - kappa * (ex (65083 / 100000) 18 * sCG cZ 18) - ex (65083 / 100000) 19 * sCG cZ 19 ≤ (5002856777251 / 40000000000000 : ℝ) := by
  have h0 := eS_16
  have h1 := keS_17
  have h2 := keS_18
  have h3 := eS_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_4 : (291005834137343 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 21 * sCG cZ 21 + kappa * (ex (65083 / 100000) 22 * sCG cZ 22) - kappa * (ex (65083 / 100000) 23 * sCG cZ 23) - ex (65083 / 100000) 24 * sCG cZ 24 ∧ ex (65083 / 100000) 21 * sCG cZ 21 + kappa * (ex (65083 / 100000) 22 * sCG cZ 22) - kappa * (ex (65083 / 100000) 23 * sCG cZ 23) - ex (65083 / 100000) 24 * sCG cZ 24 ≤ (291005859526863 / 1000000000000000 : ℝ) := by
  have h0 := eS_21
  have h1 := keS_22
  have h2 := keS_23
  have h3 := eS_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_5 : (-1175313635679 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 26 * sCG cZ 26 + kappa * (ex (65083 / 100000) 27 * sCG cZ 27) - kappa * (ex (65083 / 100000) 28 * sCG cZ 28) - ex (65083 / 100000) 29 * sCG cZ 29 ∧ ex (65083 / 100000) 26 * sCG cZ 26 + kappa * (ex (65083 / 100000) 27 * sCG cZ 27) - kappa * (ex (65083 / 100000) 28 * sCG cZ 28) - ex (65083 / 100000) 29 * sCG cZ 29 ≤ (-146911351279 / 125000000000000 : ℝ) := by
  have h0 := eS_26
  have h1 := keS_27
  have h2 := keS_28
  have h3 := eS_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_6 : (21610242860887 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 31 * sCG cZ 31 + kappa * (ex (65083 / 100000) 32 * sCG cZ 32) - kappa * (ex (65083 / 100000) 33 * sCG cZ 33) - ex (65083 / 100000) 34 * sCG cZ 34 ∧ ex (65083 / 100000) 31 * sCG cZ 31 + kappa * (ex (65083 / 100000) 32 * sCG cZ 32) - kappa * (ex (65083 / 100000) 33 * sCG cZ 33) - ex (65083 / 100000) 34 * sCG cZ 34 ≤ (1350641458353 / 62500000000000 : ℝ) := by
  have h0 := eS_31
  have h1 := keS_32
  have h2 := keS_33
  have h3 := eS_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_7 : (67507713119461 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 36 * sCG cZ 36 + kappa * (ex (65083 / 100000) 37 * sCG cZ 37) - kappa * (ex (65083 / 100000) 38 * sCG cZ 38) - ex (65083 / 100000) 39 * sCG cZ 39 ∧ ex (65083 / 100000) 36 * sCG cZ 36 + kappa * (ex (65083 / 100000) 37 * sCG cZ 37) - kappa * (ex (65083 / 100000) 38 * sCG cZ 38) - ex (65083 / 100000) 39 * sCG cZ 39 ≤ (67507731764039 / 1000000000000000 : ℝ) := by
  have h0 := eS_36
  have h1 := keS_37
  have h2 := keS_38
  have h3 := eS_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_8 : (65575898341411 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 41 * sCG cZ 41 + kappa * (ex (65083 / 100000) 42 * sCG cZ 42) - kappa * (ex (65083 / 100000) 43 * sCG cZ 43) - ex (65083 / 100000) 44 * sCG cZ 44 ∧ ex (65083 / 100000) 41 * sCG cZ 41 + kappa * (ex (65083 / 100000) 42 * sCG cZ 42) - kappa * (ex (65083 / 100000) 43 * sCG cZ 43) - ex (65083 / 100000) 44 * sCG cZ 44 ≤ (8196989451983 / 125000000000000 : ℝ) := by
  have h0 := eS_41
  have h1 := keS_42
  have h2 := keS_43
  have h3 := eS_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_9 : (9299139994923 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 46 * sCG cZ 46 + kappa * (ex (65083 / 100000) 47 * sCG cZ 47) - kappa * (ex (65083 / 100000) 48 * sCG cZ 48) - ex (65083 / 100000) 49 * sCG cZ 49 ∧ ex (65083 / 100000) 46 * sCG cZ 46 + kappa * (ex (65083 / 100000) 47 * sCG cZ 47) - kappa * (ex (65083 / 100000) 48 * sCG cZ 48) - ex (65083 / 100000) 49 * sCG cZ 49 ≤ (18598296077253 / 1000000000000000 : ℝ) := by
  have h0 := eS_46
  have h1 := keS_47
  have h2 := keS_48
  have h3 := eS_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_10 : (-9441098733371 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 51 * sCG cZ 51 + kappa * (ex (65083 / 100000) 52 * sCG cZ 52) - kappa * (ex (65083 / 100000) 53 * sCG cZ 53) - ex (65083 / 100000) 54 * sCG cZ 54 ∧ ex (65083 / 100000) 51 * sCG cZ 51 + kappa * (ex (65083 / 100000) 52 * sCG cZ 52) - kappa * (ex (65083 / 100000) 53 * sCG cZ 53) - ex (65083 / 100000) 54 * sCG cZ 54 ≤ (-9441091193501 / 500000000000000 : ℝ) := by
  have h0 := eS_51
  have h1 := keS_52
  have h2 := keS_53
  have h3 := eS_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_11 : (11009278213149 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 56 * sCG cZ 56 + kappa * (ex (65083 / 100000) 57 * sCG cZ 57) - kappa * (ex (65083 / 100000) 58 * sCG cZ 58) - ex (65083 / 100000) 59 * sCG cZ 59 ∧ ex (65083 / 100000) 56 * sCG cZ 56 + kappa * (ex (65083 / 100000) 57 * sCG cZ 57) - kappa * (ex (65083 / 100000) 58 * sCG cZ 58) - ex (65083 / 100000) 59 * sCG cZ 59 ≤ (8807425759137 / 200000000000000 : ℝ) := by
  have h0 := eS_56
  have h1 := keS_57
  have h2 := keS_58
  have h3 := eS_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_12 : (-29023393038481 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 61 * sCG cZ 61 + kappa * (ex (65083 / 100000) 62 * sCG cZ 62) - kappa * (ex (65083 / 100000) 63 * sCG cZ 63) - ex (65083 / 100000) 64 * sCG cZ 64 ∧ ex (65083 / 100000) 61 * sCG cZ 61 + kappa * (ex (65083 / 100000) 62 * sCG cZ 62) - kappa * (ex (65083 / 100000) 63 * sCG cZ 63) - ex (65083 / 100000) 64 * sCG cZ 64 ≤ (-90698068221 / 1562500000000 : ℝ) := by
  have h0 := eS_61
  have h1 := keS_62
  have h2 := keS_63
  have h3 := eS_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_13 : (99219619167091 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 66 * sCG cZ 66 + kappa * (ex (65083 / 100000) 67 * sCG cZ 67) - kappa * (ex (65083 / 100000) 68 * sCG cZ 68) - ex (65083 / 100000) 69 * sCG cZ 69 ∧ ex (65083 / 100000) 66 * sCG cZ 66 + kappa * (ex (65083 / 100000) 67 * sCG cZ 67) - kappa * (ex (65083 / 100000) 68 * sCG cZ 68) - ex (65083 / 100000) 69 * sCG cZ 69 ≤ (19843929132577 / 200000000000000 : ℝ) := by
  have h0 := eS_66
  have h1 := keS_67
  have h2 := keS_68
  have h3 := eS_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_14 : (-51562125061449 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 71 * sCG cZ 71 + kappa * (ex (65083 / 100000) 72 * sCG cZ 72) - kappa * (ex (65083 / 100000) 73 * sCG cZ 73) - ex (65083 / 100000) 74 * sCG cZ 74 ∧ ex (65083 / 100000) 71 * sCG cZ 71 + kappa * (ex (65083 / 100000) 72 * sCG cZ 72) - kappa * (ex (65083 / 100000) 73 * sCG cZ 73) - ex (65083 / 100000) 74 * sCG cZ 74 ≤ (-6445262044099 / 125000000000000 : ℝ) := by
  have h0 := eS_71
  have h1 := keS_72
  have h2 := keS_73
  have h3 := eS_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_15 : (-56792529282111 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 76 * sCG cZ 76 + kappa * (ex (65083 / 100000) 77 * sCG cZ 77) - kappa * (ex (65083 / 100000) 78 * sCG cZ 78) - ex (65083 / 100000) 79 * sCG cZ 79 ∧ ex (65083 / 100000) 76 * sCG cZ 76 + kappa * (ex (65083 / 100000) 77 * sCG cZ 77) - kappa * (ex (65083 / 100000) 78 * sCG cZ 78) - ex (65083 / 100000) 79 * sCG cZ 79 ≤ (-113585028788609 / 1000000000000000 : ℝ) := by
  have h0 := eS_76
  have h1 := keS_77
  have h2 := keS_78
  have h3 := eS_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_16 : (-53768369464927 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 81 * sCG cZ 81 + kappa * (ex (65083 / 100000) 82 * sCG cZ 82) - kappa * (ex (65083 / 100000) 83 * sCG cZ 83) - ex (65083 / 100000) 84 * sCG cZ 84 ∧ ex (65083 / 100000) 81 * sCG cZ 81 + kappa * (ex (65083 / 100000) 82 * sCG cZ 82) - kappa * (ex (65083 / 100000) 83 * sCG cZ 83) - ex (65083 / 100000) 84 * sCG cZ 84 ≤ (-53768339235711 / 1000000000000000 : ℝ) := by
  have h0 := eS_81
  have h1 := keS_82
  have h2 := keS_83
  have h3 := eS_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_17 : (-3480810264479 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 86 * sCG cZ 86 + kappa * (ex (65083 / 100000) 87 * sCG cZ 87) - kappa * (ex (65083 / 100000) 88 * sCG cZ 88) - ex (65083 / 100000) 89 * sCG cZ 89 ∧ ex (65083 / 100000) 86 * sCG cZ 86 + kappa * (ex (65083 / 100000) 87 * sCG cZ 87) - kappa * (ex (65083 / 100000) 88 * sCG cZ 88) - ex (65083 / 100000) 89 * sCG cZ 89 ≤ (-3480780067717 / 1000000000000000 : ℝ) := by
  have h0 := eS_86
  have h1 := keS_87
  have h2 := keS_88
  have h3 := eS_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_18 : (811584746967 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 91 * sCG cZ 91 + kappa * (ex (65083 / 100000) 92 * sCG cZ 92) - kappa * (ex (65083 / 100000) 93 * sCG cZ 93) - ex (65083 / 100000) 94 * sCG cZ 94 ∧ ex (65083 / 100000) 91 * sCG cZ 91 + kappa * (ex (65083 / 100000) 92 * sCG cZ 92) - kappa * (ex (65083 / 100000) 93 * sCG cZ 93) - ex (65083 / 100000) 94 * sCG cZ 94 ≤ (811590734717 / 200000000000000 : ℝ) := by
  have h0 := eS_91
  have h1 := keS_92
  have h2 := keS_93
  have h3 := eS_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_19 : (-27136877962629 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 96 * sCG cZ 96 + kappa * (ex (65083 / 100000) 97 * sCG cZ 97) - kappa * (ex (65083 / 100000) 98 * sCG cZ 98) - ex (65083 / 100000) 99 * sCG cZ 99 ∧ ex (65083 / 100000) 96 * sCG cZ 96 + kappa * (ex (65083 / 100000) 97 * sCG cZ 97) - kappa * (ex (65083 / 100000) 98 * sCG cZ 98) - ex (65083 / 100000) 99 * sCG cZ 99 ≤ (-27136848427373 / 1000000000000000 : ℝ) := by
  have h0 := eS_96
  have h1 := keS_97
  have h2 := keS_98
  have h3 := eS_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_20 : (-10176201276471 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 101 * sCG cZ 101 + kappa * (ex (65083 / 100000) 102 * sCG cZ 102) - kappa * (ex (65083 / 100000) 103 * sCG cZ 103) - ex (65083 / 100000) 104 * sCG cZ 104 ∧ ex (65083 / 100000) 101 * sCG cZ 101 + kappa * (ex (65083 / 100000) 102 * sCG cZ 102) - kappa * (ex (65083 / 100000) 103 * sCG cZ 103) - ex (65083 / 100000) 104 * sCG cZ 104 ≤ (-81409581099219 / 1000000000000000 : ℝ) := by
  have h0 := eS_101
  have h1 := keS_102
  have h2 := keS_103
  have h3 := eS_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_21 : (-6786611416893 / 62500000000000 : ℝ) ≤ ex (65083 / 100000) 106 * sCG cZ 106 + kappa * (ex (65083 / 100000) 107 * sCG cZ 107) - kappa * (ex (65083 / 100000) 108 * sCG cZ 108) - ex (65083 / 100000) 109 * sCG cZ 109 ∧ ex (65083 / 100000) 106 * sCG cZ 106 + kappa * (ex (65083 / 100000) 107 * sCG cZ 107) - kappa * (ex (65083 / 100000) 108 * sCG cZ 108) - ex (65083 / 100000) 109 * sCG cZ 109 ≤ (-10858575407501 / 100000000000000 : ℝ) := by
  have h0 := eS_106
  have h1 := keS_107
  have h2 := keS_108
  have h3 := eS_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_22 : (-8129987918693 / 200000000000000 : ℝ) ≤ ex (65083 / 100000) 111 * sCG cZ 111 + kappa * (ex (65083 / 100000) 112 * sCG cZ 112) - kappa * (ex (65083 / 100000) 113 * sCG cZ 113) - ex (65083 / 100000) 114 * sCG cZ 114 ∧ ex (65083 / 100000) 111 * sCG cZ 111 + kappa * (ex (65083 / 100000) 112 * sCG cZ 112) - kappa * (ex (65083 / 100000) 113 * sCG cZ 113) - ex (65083 / 100000) 114 * sCG cZ 114 ≤ (-635154869657 / 15625000000000 : ℝ) := by
  have h0 := eS_111
  have h1 := keS_112
  have h2 := keS_113
  have h3 := eS_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_23 : (20151463654881 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 116 * sCG cZ 116 + kappa * (ex (65083 / 100000) 117 * sCG cZ 117) - kappa * (ex (65083 / 100000) 118 * sCG cZ 118) - ex (65083 / 100000) 119 * sCG cZ 119 ∧ ex (65083 / 100000) 116 * sCG cZ 116 + kappa * (ex (65083 / 100000) 117 * sCG cZ 117) - kappa * (ex (65083 / 100000) 118 * sCG cZ 118) - ex (65083 / 100000) 119 * sCG cZ 119 ≤ (80605882045751 / 1000000000000000 : ℝ) := by
  have h0 := eS_116
  have h1 := keS_117
  have h2 := keS_118
  have h3 := eS_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_24 : (499588073021 / 8000000000000 : ℝ) ≤ ex (65083 / 100000) 121 * sCG cZ 121 + kappa * (ex (65083 / 100000) 122 * sCG cZ 122) - kappa * (ex (65083 / 100000) 123 * sCG cZ 123) - ex (65083 / 100000) 124 * sCG cZ 124 ∧ ex (65083 / 100000) 121 * sCG cZ 121 + kappa * (ex (65083 / 100000) 122 * sCG cZ 122) - kappa * (ex (65083 / 100000) 123 * sCG cZ 123) - ex (65083 / 100000) 124 * sCG cZ 124 ≤ (62448535902109 / 1000000000000000 : ℝ) := by
  have h0 := eS_121
  have h1 := keS_122
  have h2 := keS_123
  have h3 := eS_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_25 : (-79653418272259 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 126 * sCG cZ 126 + kappa * (ex (65083 / 100000) 127 * sCG cZ 127) - kappa * (ex (65083 / 100000) 128 * sCG cZ 128) - ex (65083 / 100000) 129 * sCG cZ 129 ∧ ex (65083 / 100000) 126 * sCG cZ 126 + kappa * (ex (65083 / 100000) 127 * sCG cZ 127) - kappa * (ex (65083 / 100000) 128 * sCG cZ 128) - ex (65083 / 100000) 129 * sCG cZ 129 ≤ (-15930678429761 / 200000000000000 : ℝ) := by
  have h0 := eS_126
  have h1 := keS_127
  have h2 := keS_128
  have h3 := eS_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_26 : (-20629136719227 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 131 * sCG cZ 131 + kappa * (ex (65083 / 100000) 132 * sCG cZ 132) - kappa * (ex (65083 / 100000) 133 * sCG cZ 133) - ex (65083 / 100000) 134 * sCG cZ 134 ∧ ex (65083 / 100000) 131 * sCG cZ 131 + kappa * (ex (65083 / 100000) 132 * sCG cZ 132) - kappa * (ex (65083 / 100000) 133 * sCG cZ 133) - ex (65083 / 100000) 134 * sCG cZ 134 ≤ (-2062911132261 / 100000000000000 : ℝ) := by
  have h0 := eS_131
  have h1 := keS_132
  have h2 := keS_133
  have h3 := eS_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_27 : (41752535022809 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 136 * sCG cZ 136 + kappa * (ex (65083 / 100000) 137 * sCG cZ 137) - kappa * (ex (65083 / 100000) 138 * sCG cZ 138) - ex (65083 / 100000) 139 * sCG cZ 139 ∧ ex (65083 / 100000) 136 * sCG cZ 136 + kappa * (ex (65083 / 100000) 137 * sCG cZ 137) - kappa * (ex (65083 / 100000) 138 * sCG cZ 138) - ex (65083 / 100000) 139 * sCG cZ 139 ≤ (20876273729483 / 250000000000000 : ℝ) := by
  have h0 := eS_136
  have h1 := keS_137
  have h2 := keS_138
  have h3 := eS_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_0 : (-116053325530549 / 250000000000000 : ℝ) ≤ Real.log 1 * (ex (65083 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (65083 / 100000) 4 * cCG cZ 4) ∧ Real.log 1 * (ex (65083 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (65083 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (65083 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (65083 / 100000) 4 * cCG cZ 4) ≤ (-232106637592557 / 500000000000000 : ℝ) := by
  have h0 : Real.log 1 * (ex (65083 / 100000) 1 * cCG cZ 1) = (0 : ℝ) := by rw [Real.log_one]; norm_num
  have h1 := kleC_2
  have h2 := kleC_3
  have h3 := leC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_1 : (-558748184311937 / 500000000000000 : ℝ) ≤ Real.log 6 * (ex (65083 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (65083 / 100000) 9 * cCG cZ 9) ∧ Real.log 6 * (ex (65083 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (65083 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (65083 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (65083 / 100000) 9 * cCG cZ 9) ≤ (-279374076236947 / 250000000000000 : ℝ) := by
  have h0 := leC_6
  have h1 := kleC_7
  have h2 := kleC_8
  have h3 := leC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_2 : (-71704553260467 / 100000000000000 : ℝ) ≤ Real.log 11 * (ex (65083 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (65083 / 100000) 14 * cCG cZ 14) ∧ Real.log 11 * (ex (65083 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (65083 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (65083 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (65083 / 100000) 14 * cCG cZ 14) ≤ (-179261367060927 / 250000000000000 : ℝ) := by
  have h0 := leC_11
  have h1 := kleC_12
  have h2 := kleC_13
  have h3 := leC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_3 : (104885796121327 / 1000000000000000 : ℝ) ≤ Real.log 16 * (ex (65083 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (65083 / 100000) 19 * cCG cZ 19) ∧ Real.log 16 * (ex (65083 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (65083 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (65083 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (65083 / 100000) 19 * cCG cZ 19) ≤ (104885871135577 / 1000000000000000 : ℝ) := by
  have h0 := leC_16
  have h1 := kleC_17
  have h2 := kleC_18
  have h3 := leC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_4 : (-42382208787533 / 200000000000000 : ℝ) ≤ Real.log 21 * (ex (65083 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (65083 / 100000) 24 * cCG cZ 24) ∧ Real.log 21 * (ex (65083 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (65083 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (65083 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (65083 / 100000) 24 * cCG cZ 24) ≤ (-52977741280037 / 250000000000000 : ℝ) := by
  have h0 := leC_21
  have h1 := kleC_22
  have h2 := kleC_23
  have h3 := leC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_5 : (155478935434821 / 1000000000000000 : ℝ) ≤ Real.log 26 * (ex (65083 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (65083 / 100000) 29 * cCG cZ 29) ∧ Real.log 26 * (ex (65083 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (65083 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (65083 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (65083 / 100000) 29 * cCG cZ 29) ≤ (38869752741557 / 250000000000000 : ℝ) := by
  have h0 := leC_26
  have h1 := kleC_27
  have h2 := kleC_28
  have h3 := leC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_6 : (-101636689785947 / 250000000000000 : ℝ) ≤ Real.log 31 * (ex (65083 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (65083 / 100000) 34 * cCG cZ 34) ∧ Real.log 31 * (ex (65083 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (65083 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (65083 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (65083 / 100000) 34 * cCG cZ 34) ≤ (-203273343792379 / 500000000000000 : ℝ) := by
  have h0 := leC_31
  have h1 := kleC_32
  have h2 := kleC_33
  have h3 := leC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_7 : (13100271091987 / 31250000000000 : ℝ) ≤ Real.log 36 * (ex (65083 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (65083 / 100000) 39 * cCG cZ 39) ∧ Real.log 36 * (ex (65083 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (65083 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (65083 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (65083 / 100000) 39 * cCG cZ 39) ≤ (209604371374341 / 500000000000000 : ℝ) := by
  have h0 := leC_36
  have h1 := kleC_37
  have h2 := kleC_38
  have h3 := leC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_8 : (-10661638540133 / 50000000000000 : ℝ) ≤ Real.log 41 * (ex (65083 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (65083 / 100000) 44 * cCG cZ 44) ∧ Real.log 41 * (ex (65083 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (65083 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (65083 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (65083 / 100000) 44 * cCG cZ 44) ≤ (-213232705980759 / 1000000000000000 : ℝ) := by
  have h0 := leC_41
  have h1 := kleC_42
  have h2 := kleC_43
  have h3 := leC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_9 : (-43528112974043 / 500000000000000 : ℝ) ≤ Real.log 46 * (ex (65083 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (65083 / 100000) 49 * cCG cZ 49) ∧ Real.log 46 * (ex (65083 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (65083 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (65083 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (65083 / 100000) 49 * cCG cZ 49) ≤ (-87056163779459 / 1000000000000000 : ℝ) := by
  have h0 := leC_46
  have h1 := kleC_47
  have h2 := kleC_48
  have h3 := leC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_10 : (-20115898485209 / 1000000000000000 : ℝ) ≤ Real.log 51 * (ex (65083 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (65083 / 100000) 54 * cCG cZ 54) ∧ Real.log 51 * (ex (65083 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (65083 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (65083 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (65083 / 100000) 54 * cCG cZ 54) ≤ (-5028959626601 / 250000000000000 : ℝ) := by
  have h0 := leC_51
  have h1 := kleC_52
  have h2 := kleC_53
  have h3 := leC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_11 : (-150847157512401 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (65083 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (65083 / 100000) 59 * cCG cZ 59) ∧ Real.log 56 * (ex (65083 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (65083 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (65083 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (65083 / 100000) 59 * cCG cZ 59) ≤ (-150847092762123 / 1000000000000000 : ℝ) := by
  have h0 := leC_56
  have h1 := kleC_57
  have h2 := kleC_58
  have h3 := leC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_12 : (24975473803991 / 100000000000000 : ℝ) ≤ Real.log 61 * (ex (65083 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (65083 / 100000) 64 * cCG cZ 64) ∧ Real.log 61 * (ex (65083 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (65083 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (65083 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (65083 / 100000) 64 * cCG cZ 64) ≤ (249754830888323 / 1000000000000000 : ℝ) := by
  have h0 := leC_61
  have h1 := kleC_62
  have h2 := kleC_63
  have h3 := leC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_13 : (-14897986058149 / 200000000000000 : ℝ) ≤ Real.log 66 * (ex (65083 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (65083 / 100000) 69 * cCG cZ 69) ∧ Real.log 66 * (ex (65083 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (65083 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (65083 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (65083 / 100000) 69 * cCG cZ 69) ≤ (-74489818352717 / 1000000000000000 : ℝ) := by
  have h0 := leC_66
  have h1 := kleC_67
  have h2 := kleC_68
  have h3 := leC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_14 : (-421711263985727 / 1000000000000000 : ℝ) ≤ Real.log 71 * (ex (65083 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (65083 / 100000) 74 * cCG cZ 74) ∧ Real.log 71 * (ex (65083 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (65083 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (65083 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (65083 / 100000) 74 * cCG cZ 74) ≤ (-26356946303973 / 62500000000000 : ℝ) := by
  have h0 := leC_71
  have h1 := kleC_72
  have h2 := kleC_73
  have h3 := leC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_15 : (125332264379231 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (65083 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (65083 / 100000) 79 * cCG cZ 79) ∧ Real.log 76 * (ex (65083 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (65083 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (65083 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (65083 / 100000) 79 * cCG cZ 79) ≤ (3133309849283 / 25000000000000 : ℝ) := by
  have h0 := leC_76
  have h1 := kleC_77
  have h2 := kleC_78
  have h3 := leC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_16 : (117900831731403 / 250000000000000 : ℝ) ≤ Real.log 81 * (ex (65083 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (65083 / 100000) 84 * cCG cZ 84) ∧ Real.log 81 * (ex (65083 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (65083 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (65083 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (65083 / 100000) 84 * cCG cZ 84) ≤ (235801730348743 / 500000000000000 : ℝ) := by
  have h0 := leC_81
  have h1 := kleC_82
  have h2 := kleC_83
  have h3 := leC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_17 : (106988428217617 / 200000000000000 : ℝ) ≤ Real.log 86 * (ex (65083 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (65083 / 100000) 89 * cCG cZ 89) ∧ Real.log 86 * (ex (65083 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (65083 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (65083 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (65083 / 100000) 89 * cCG cZ 89) ≤ (106988455326607 / 200000000000000 : ℝ) := by
  have h0 := leC_86
  have h1 := kleC_87
  have h2 := kleC_88
  have h3 := leC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_18 : (534865098752207 / 1000000000000000 : ℝ) ≤ Real.log 91 * (ex (65083 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (65083 / 100000) 94 * cCG cZ 94) ∧ Real.log 91 * (ex (65083 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (65083 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (65083 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (65083 / 100000) 94 * cCG cZ 94) ≤ (133716308720907 / 250000000000000 : ℝ) := by
  have h0 := leC_91
  have h1 := kleC_92
  have h2 := kleC_93
  have h3 := leC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_19 : (515191277582191 / 1000000000000000 : ℝ) ≤ Real.log 96 * (ex (65083 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (65083 / 100000) 99 * cCG cZ 99) ∧ Real.log 96 * (ex (65083 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (65083 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (65083 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (65083 / 100000) 99 * cCG cZ 99) ≤ (64398926682253 / 125000000000000 : ℝ) := by
  have h0 := leC_96
  have h1 := kleC_97
  have h2 := kleC_98
  have h3 := leC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_20 : (179866668777441 / 500000000000000 : ℝ) ≤ Real.log 101 * (ex (65083 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (65083 / 100000) 104 * cCG cZ 104) ∧ Real.log 101 * (ex (65083 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (65083 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (65083 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (65083 / 100000) 104 * cCG cZ 104) ≤ (359733472493391 / 1000000000000000 : ℝ) := by
  have h0 := leC_101
  have h1 := kleC_102
  have h2 := kleC_103
  have h3 := leC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_21 : (-10477001309507 / 250000000000000 : ℝ) ≤ Real.log 106 * (ex (65083 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (65083 / 100000) 109 * cCG cZ 109) ∧ Real.log 106 * (ex (65083 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (65083 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (65083 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (65083 / 100000) 109 * cCG cZ 109) ≤ (-4190787190237 / 100000000000000 : ℝ) := by
  have h0 := leC_106
  have h1 := kleC_107
  have h2 := kleC_108
  have h3 := leC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_22 : (-229031669813659 / 500000000000000 : ℝ) ≤ Real.log 111 * (ex (65083 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (65083 / 100000) 114 * cCG cZ 114) ∧ Real.log 111 * (ex (65083 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (65083 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (65083 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (65083 / 100000) 114 * cCG cZ 114) ≤ (-458063207239797 / 1000000000000000 : ℝ) := by
  have h0 := leC_111
  have h1 := kleC_112
  have h2 := kleC_113
  have h3 := leC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_23 : (-291951677781047 / 1000000000000000 : ℝ) ≤ Real.log 116 * (ex (65083 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (65083 / 100000) 119 * cCG cZ 119) ∧ Real.log 116 * (ex (65083 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (65083 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (65083 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (65083 / 100000) 119 * cCG cZ 119) ≤ (-291951547010953 / 1000000000000000 : ℝ) := by
  have h0 := leC_116
  have h1 := kleC_117
  have h2 := kleC_118
  have h3 := leC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_24 : (35937258974117 / 100000000000000 : ℝ) ≤ Real.log 121 * (ex (65083 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (65083 / 100000) 124 * cCG cZ 124) ∧ Real.log 121 * (ex (65083 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (65083 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (65083 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (65083 / 100000) 124 * cCG cZ 124) ≤ (359372718687677 / 1000000000000000 : ℝ) := by
  have h0 := leC_121
  have h1 := kleC_122
  have h2 := kleC_123
  have h3 := leC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_25 : (23750351583751 / 100000000000000 : ℝ) ≤ Real.log 126 * (ex (65083 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (65083 / 100000) 129 * cCG cZ 129) ∧ Real.log 126 * (ex (65083 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (65083 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (65083 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (65083 / 100000) 129 * cCG cZ 129) ≤ (11875182122979 / 50000000000000 : ℝ) := by
  have h0 := leC_126
  have h1 := kleC_127
  have h2 := kleC_128
  have h3 := leC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_26 : (-213604980895689 / 500000000000000 : ℝ) ≤ Real.log 131 * (ex (65083 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (65083 / 100000) 134 * cCG cZ 134) ∧ Real.log 131 * (ex (65083 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (65083 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (65083 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (65083 / 100000) 134 * cCG cZ 134) ≤ (-427209837219263 / 1000000000000000 : ℝ) := by
  have h0 := leC_131
  have h1 := kleC_132
  have h2 := kleC_133
  have h3 := leC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_27 : (52918473822737 / 500000000000000 : ℝ) ≤ Real.log 136 * (ex (65083 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (65083 / 100000) 139 * cCG cZ 139) ∧ Real.log 136 * (ex (65083 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (65083 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (65083 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (65083 / 100000) 139 * cCG cZ 139) ≤ (105837069945931 / 1000000000000000 : ℝ) := by
  have h0 := leC_136
  have h1 := kleC_137
  have h2 := kleC_138
  have h3 := leC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReT_1 : (3285905848219 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (410738456123 / 31250000000000 : ℝ) := by
  have hc := cCB_141
  have hs := sCB_141
  have hin : (164611960212121 / 500000000000000 : ℝ) ≤ cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (16461205020133 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (3285905848219 / 250000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (410738456123 / 31250000000000 : ℝ) :=
    mul_bounds_of exB_141 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PReT_2 : (3170318317749 / 500000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (3170319329379 / 500000000000000 : ℝ) := by
  have hc := cCB_142
  have hs := sCB_142
  have hin : (280826117726131 / 500000000000000 : ℝ) ≤ cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (561652413912619 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (22319973165851 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 142 * (cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 142 * (cCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (22319980288019 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_142 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_3 : (197110475679 / 40000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (4927763873483 / 1000000000000000 : ℝ) := by
  have hc := cCB_143
  have hs := sCB_143
  have hin : (10962456411213 / 25000000000000 : ℝ) ≤ cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (438498432180501 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (17346446345913 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 143 * (cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 143 * (cCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (4336613330277 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_143 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_4 : (1861531476839 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (14543268229 / 7812500000000 : ℝ) := by
  have hc := cCB_144
  have hs := sCB_144
  have hin : (11817822262987 / 250000000000000 : ℝ) ≤ cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (4727146309967 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (1861531476839 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (14543268229 / 7812500000000 : ℝ) :=
    mul_bounds_of exB_144 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_1 : (9318431085377 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (18636869381233 / 1000000000000000 : ℝ) := by
  have hc := cCB_141
  have hs := sCB_141
  have hin : (93363917161343 / 200000000000000 : ℝ) ≤ cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (233409882892459 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (9318431085377 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (18636869381233 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_141 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_2 : (34852347803 / 40000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (871310710939 / 1000000000000000 : ℝ) := by
  have hc := cCB_142
  have hs := sCB_142
  have hin : (19295084409123 / 250000000000000 : ℝ) ≤ cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (77180516096849 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (3067134707637 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 142 * (cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 142 * (cCG cZ 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (766785450943 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_142 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_3 : (-3965713795627 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-3965711815419 / 1000000000000000 : ℝ) := by
  have hc := cCB_143
  have hs := sCB_143
  have hin : (-352890139727777 / 1000000000000000 : ℝ) ≤ cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-352889963995703 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-13959895605163 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 143 * (cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 143 * (cCG cZ 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-13959888634543 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_143 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_4 : (-21934916802817 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-21934909919201 / 1000000000000000 : ℝ) := by
  have hc := cCB_144
  have hs := sCB_144
  have hin : (-278505038462997 / 500000000000000 : ℝ) ≤ cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-8703279732473 / 15625000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-21934916802817 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-21934909919201 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_144 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_1 : (-32326541153279 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-4040815419249 / 62500000000000 : ℝ) := by
  have hc := cCB_141
  have hs := sCB_141
  have hl := lgB_141
  have hv1 : (-637656837859971 / 250000000000000 : ℝ) ≤ (5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-2550627350365361 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-1196843627408459 / 1000000000000000 : ℝ) ≤ (-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-59842181345337 / 50000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-1106919437321953 / 500000000000000 : ℝ) ≤ cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1106919134552359 / 500000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (118879292134429 / 200000000000000 : ℝ) ≤ sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (29719837231147 / 50000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-1619442413971761 / 1000000000000000 : ℝ) ≤ cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-809720762240889 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-32326541153279 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 141 * (cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 141 * (cCG cZ 141 * ((5568735573156876537295533669017927118854067263798009685844020739635455031442875154051693833174719039353512015904475346705722003728220517529319540398907385348024089360659028746369282626554459093 / 514949487597462574724235668186080932972839660157795778340535261790563170765159404229178353114112275251200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (426576830367060687702753780159676869029713839603729476139773572677902033784851317391997857871294698003432038938451867723436178321234695416918402304758360044728418453813087039737054117 / 824155584456986521299094132714614025803573145375669782266757997720496788668253093232640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 141 * ((-30284443675449958820507438629277403535478679979843002459568038902232456710023494873841075149548244968878045551773238476202000193111279298838149469637885455217632852800400626730451433707236451 / 35608209248760709954335445140526873024717636074741197438441268102538942659292937526485737183422657331200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 141 * (6018022984162980579593953062992540906922073423014747074870592346582086767901920246426216908131472790031157515903022041752611532754191435180187708244173320423064095494009847637949434367 / 24901272301807521322108344152734409493922245749564879849917045216840724400476504174100480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-4040815419249 / 62500000000000 : ℝ) :=
    mul_bounds_of exB_141 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_2 : (-1956928827287 / 62500000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (65083 / 100000) 142 * (cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-31310851223 / 1000000000000 : ℝ) := by
  have hc := cCB_142
  have hs := sCB_142
  have hl := lgB_142
  have hv1 : (-510123507608001 / 200000000000000 : ℝ) ≤ (83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1275308768483553 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-1155811636280667 / 1000000000000000 : ℝ) ≤ (-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1155811635796831 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-489244944532677 / 200000000000000 : ℝ) ≤ cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2446224114618127 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-13091386293219 / 40000000000000 : ℝ) ≤ sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-65456876424843 / 200000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-138675468999693 / 50000000000000 : ℝ) ≤ cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1386754248371171 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-110218834917583 / 1000000000000000 : ℝ) ≤ ex (65083 / 100000) 142 * (cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 142 * (cCG cZ 142 * ((83510271725791501211693010758417967295159910503535849921309631789392158735250466240613859254958712239356348476496117422704390380739353461862247518312631850112935345624683137054613689329207968209 / 7875902159831851580378654537623299531274912326666678861157599056606279399791313127994603851206022188236800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (23552134418052263348498504067870112665188285182095438454698770980823878655902229050165413832001767700400479597234705448731727269409977467354814914180913795827106669407311827779641543499 / 45572136907503783651086018428483316709438981537609620169215495779653769111482963056394240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 142 * ((-13012667205544386763274045509201417827494209977866340886534494409086984169923522545136293585930846808689590500758188356785849369588246634177041666967882186165722311712846403999705894679670357 / 16272525123619528058633583755420040353873785798898096820573551769847684710312630429740917047946326835200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 142 * (6827853713879577771507150119134068885354942560159861081144207967548834911321564763877458485625436670514435438410987736796943729387018161085032183328261176438056861350422468933949434367 / 29296373726252432347126726132596417884639345274177612965924247286920280143096190536253440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-110218799668271 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_142 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_3 : (-24408969894091 / 1000000000000000 : ℝ) ≤ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (65083 / 100000) 143 * (cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-24408960075741 / 1000000000000000 : ℝ) := by
  have hc := cCB_143
  have hs := sCB_143
  have hl := lgB_143
  have hv1 : (-2550805848356367 / 1000000000000000 : ℝ) ≤ (96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-255080584728499 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-69734907736333 / 62500000000000 : ℝ) ≤ (-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1115758523314911 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-236737264502141 / 200000000000000 : ℝ) ≤ cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-591842858435391 / 500000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-988352619390767 / 1000000000000000 : ℝ) ≤ sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-123544044284907 / 125000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-67876216934421 / 31250000000000 : ℝ) ≤ cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1086019035575019 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-10740395333333 / 125000000000000 : ℝ) ≤ ex (65083 / 100000) 143 * (cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 143 * (cCG cZ 143 * ((96285964063430001939196631198233680493146871907464059897200974252198236446698670030005929643200872309789827413112301264870656566569304267348801372981905399763540496732973335248104535009207968209 / 9255443910545288587020318351584056736829705658659776626102754371985004496018609955363064814728836756275200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (27638258695341357801741368679049099997463319914773536128018021448130880874817411344196111498298858062930589526132761893690266625076176761609987664585714761470301536521064372019641543499 / 53554545050378991243201562196589332333139376240329644771127053903295253742277608456847360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 143 * ((-1741983919496873556456332126491056148327001052554969097266138081775351957165383921130245245804970058104181787956394410081548472373458694031743338822899965430325681054854280625042366696240113197 / 2313860977636322146755079587896014184207426414664944156525688592996251124004652488840766203682209189068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 143 * (7734944594265427413533941323798449482115398019091198775254683329886001980535219370760682488019789582474032993620374003478958039036608577028410599511702578781320074664036592853949434367 / 34427921818100780084915289983521713642732456154497628781438820366404091691464176865116160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-42961564052317 / 500000000000000 : ℝ) :=
    mul_bounds_of exB_143 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_4 : (-4700965366047 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-9401896715687 / 1000000000000000 : ℝ) := by
  have hc := cCB_144
  have hs := sCB_144
  have hl := lgB_144
  have hv1 : (-2551174596296907 / 1000000000000000 : ℝ) ≤ (110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1275587297613479 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-215326820323953 / 200000000000000 : ℝ) ≤ (-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-538317050585163 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (392785386887549 / 500000000000000 : ℝ) ≤ cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (785571380796207 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-128040146720161 / 125000000000000 : ℝ) ≤ sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-512160458650337 / 500000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-23875039998619 / 100000000000000 : ℝ) ≤ cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-238749536504467 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-4700965366047 / 500000000000000 : ℝ) ≤ ex (65083 / 100000) 144 * (cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (65083 / 100000) 144 * (cCG cZ 144 * ((110959927258536740926149247767375781032268741527616651673333698003730615361440637688456226045086784063366811997097000870450575708630620550086552584158542450911255812353457064500873211185207968209 / 10864399071724777953103582869709091060033340692566439659300154285691882243967208472691575098479751882342400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (32399629742515816385296168433617865467762210456663792730306206667648246323631070768743155927234504923622380196894164524031427293703004657872214851191832962239712065201672723587641543499 / 62864402308035927916194106901268862943698188962232136911177037132720278685678563565240320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 144 * ((-175223928635226903805600898827040027893806808326098930474870372337333319001659087816271629416652785357727841843627868497527665967174894695026664495401953643350568580124776052760461609476373927 / 246918160721017680752354156129752069546212288467419083165912597402088232817436556197535797692721633689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 144 * (8749051449801397224600740204237306920123248762835512662894160829494127566944657186767722323607996656014715654982223550506724250133201573253209616905584647138337925284452219397949434367 / 40412830055165953660410497293672840463805978618577802300042381013891607726507648006225920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-9401896715687 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_144 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

/-- Lower end of the enclosure of `Re fEM(c)`. -/
theorem PReG_ge : (-67926137 / 500000000000000 : ℝ) ≤ PReG cZ 28 12 := by
  rw [PRe_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  have b0 := PReB_0
  have b1 := PReB_1
  have b2 := PReB_2
  have b3 := PReB_3
  have b4 := PReB_4
  have b5 := PReB_5
  have b6 := PReB_6
  have b7 := PReB_7
  have b8 := PReB_8
  have b9 := PReB_9
  have b10 := PReB_10
  have b11 := PReB_11
  have b12 := PReB_12
  have b13 := PReB_13
  have b14 := PReB_14
  have b15 := PReB_15
  have b16 := PReB_16
  have b17 := PReB_17
  have b18 := PReB_18
  have b19 := PReB_19
  have b20 := PReB_20
  have b21 := PReB_21
  have b22 := PReB_22
  have b23 := PReB_23
  have b24 := PReB_24
  have b25 := PReB_25
  have b26 := PReB_26
  have b27 := PReB_27
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Re fEM(c)`. -/
theorem PReG_le : PReG cZ 28 12 ≤ (23343429 / 40000000000000 : ℝ) := by
  rw [PRe_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  have b0 := PReB_0
  have b1 := PReB_1
  have b2 := PReB_2
  have b3 := PReB_3
  have b4 := PReB_4
  have b5 := PReB_5
  have b6 := PReB_6
  have b7 := PReB_7
  have b8 := PReB_8
  have b9 := PReB_9
  have b10 := PReB_10
  have b11 := PReB_11
  have b12 := PReB_12
  have b13 := PReB_13
  have b14 := PReB_14
  have b15 := PReB_15
  have b16 := PReB_16
  have b17 := PReB_17
  have b18 := PReB_18
  have b19 := PReB_19
  have b20 := PReB_20
  have b21 := PReB_21
  have b22 := PReB_22
  have b23 := PReB_23
  have b24 := PReB_24
  have b25 := PReB_25
  have b26 := PReB_26
  have b27 := PReB_27
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM(c)`**: `PReG cZ 28 12 ∈ [-1.3585227400e-07, 5.8358572500e-07]` (width `7.19e-07`). -/
theorem PReG_mem : (-67926137 / 500000000000000 : ℝ) ≤ PReG cZ 28 12 ∧ PReG cZ 28 12 ≤ (23343429 / 40000000000000 : ℝ) := ⟨PReG_ge, PReG_le⟩

/-- Open inequality `H1` of `DHLocate2Base`. -/
theorem H1 : |PReG cZ 28 12| ≤ (3 / 10000 : ℝ) := by
  have h := PReG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Im fEM(c)`. -/
theorem PImG_ge : (-2334563339 / 1000000000000000 : ℝ) ≤ PImG cZ 28 12 := by
  rw [PIm_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  have b0 := PImB_0
  have b1 := PImB_1
  have b2 := PImB_2
  have b3 := PImB_3
  have b4 := PImB_4
  have b5 := PImB_5
  have b6 := PImB_6
  have b7 := PImB_7
  have b8 := PImB_8
  have b9 := PImB_9
  have b10 := PImB_10
  have b11 := PImB_11
  have b12 := PImB_12
  have b13 := PImB_13
  have b14 := PImB_14
  have b15 := PImB_15
  have b16 := PImB_16
  have b17 := PImB_17
  have b18 := PImB_18
  have b19 := PImB_19
  have b20 := PImB_20
  have b21 := PImB_21
  have b22 := PImB_22
  have b23 := PImB_23
  have b24 := PImB_24
  have b25 := PImB_25
  have b26 := PImB_26
  have b27 := PImB_27
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Im fEM(c)`. -/
theorem PImG_le : PImG cZ 28 12 ≤ (-201937983 / 125000000000000 : ℝ) := by
  rw [PIm_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]
  have b0 := PImB_0
  have b1 := PImB_1
  have b2 := PImB_2
  have b3 := PImB_3
  have b4 := PImB_4
  have b5 := PImB_5
  have b6 := PImB_6
  have b7 := PImB_7
  have b8 := PImB_8
  have b9 := PImB_9
  have b10 := PImB_10
  have b11 := PImB_11
  have b12 := PImB_12
  have b13 := PImB_13
  have b14 := PImB_14
  have b15 := PImB_15
  have b16 := PImB_16
  have b17 := PImB_17
  have b18 := PImB_18
  have b19 := PImB_19
  have b20 := PImB_20
  have b21 := PImB_21
  have b22 := PImB_22
  have b23 := PImB_23
  have b24 := PImB_24
  have b25 := PImB_25
  have b26 := PImB_26
  have b27 := PImB_27
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Im fEM(c)`**: `PImG cZ 28 12 ∈ [-2.3345633390e-06, -1.6155038640e-06]` (width `7.19e-07`). -/
theorem PImG_mem : (-2334563339 / 1000000000000000 : ℝ) ≤ PImG cZ 28 12 ∧ PImG cZ 28 12 ≤ (-201937983 / 125000000000000 : ℝ) := ⟨PImG_ge, PImG_le⟩

/-- Open inequality `H2` of `DHLocate2Base`. -/
theorem H2 : |PImG cZ 28 12| ≤ (3 / 10000 : ℝ) := by
  have h := PImG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Re fEM′(c)`. -/
theorem AReG_ge : (34717387959133 / 40000000000000 : ℝ) ≤ AReG cZ 28 12 := by
  rw [ARe_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  have b0 := AReB_0
  have b1 := AReB_1
  have b2 := AReB_2
  have b3 := AReB_3
  have b4 := AReB_4
  have b5 := AReB_5
  have b6 := AReB_6
  have b7 := AReB_7
  have b8 := AReB_8
  have b9 := AReB_9
  have b10 := AReB_10
  have b11 := AReB_11
  have b12 := AReB_12
  have b13 := AReB_13
  have b14 := AReB_14
  have b15 := AReB_15
  have b16 := AReB_16
  have b17 := AReB_17
  have b18 := AReB_18
  have b19 := AReB_19
  have b20 := AReB_20
  have b21 := AReB_21
  have b22 := AReB_22
  have b23 := AReB_23
  have b24 := AReB_24
  have b25 := AReB_25
  have b26 := AReB_26
  have b27 := AReB_27
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Re fEM′(c)`. -/
theorem AReG_le : AReG cZ 28 12 ≤ (867937596543989 / 1000000000000000 : ℝ) := by
  rw [ARe_Z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  have b0 := AReB_0
  have b1 := AReB_1
  have b2 := AReB_2
  have b3 := AReB_3
  have b4 := AReB_4
  have b5 := AReB_5
  have b6 := AReB_6
  have b7 := AReB_7
  have b8 := AReB_8
  have b9 := AReB_9
  have b10 := AReB_10
  have b11 := AReB_11
  have b12 := AReB_12
  have b13 := AReB_13
  have b14 := AReB_14
  have b15 := AReB_15
  have b16 := AReB_16
  have b17 := AReB_17
  have b18 := AReB_18
  have b19 := AReB_19
  have b20 := AReB_20
  have b21 := AReB_21
  have b22 := AReB_22
  have b23 := AReB_23
  have b24 := AReB_24
  have b25 := AReB_25
  have b26 := AReB_26
  have b27 := AReB_27
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM′(c)`**: `AReG cZ 28 12 ∈ [8.6793469898e-01, 8.6793759654e-01]` (width `2.90e-06`). -/
theorem AReG_mem : (34717387959133 / 40000000000000 : ℝ) ≤ AReG cZ 28 12 ∧ AReG cZ 28 12 ≤ (867937596543989 / 1000000000000000 : ℝ) := ⟨AReG_ge, AReG_le⟩

/-- Open inequality `H3` of `DHLocate2Base`. -/
theorem H3 : (17 / 20 : ℝ) ≤ AReG cZ 28 12 := by
  have h := AReG_mem
  linarith [h.1]

/-- **The located zero**: within `1 / 200` of `cZ = 65083 / 100000 + (11416334 / 100000) i` (`dh_zero_near_of_center'` with
its three open inequalities discharged). -/
theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < (1 / 200 : ℝ) :=
  dh_zero_near_of_center' H1 H2 H3

/-- The located zero in coordinates: `0.64583 < Re ρ < 0.65583` (off the critical line)
and `114.15834 < Im ρ < 114.16834`. -/
theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ 64583 / 100000 < ρ.re ∧ ρ.re < 65583 / 100000 ∧
    5707917 / 50000 < ρ.im ∧ ρ.im < 5708417 / 50000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located
  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cZ)).trans_lt hρ)
  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cZ)).trans_lt hρ)
  rw [Complex.sub_re, cZ_re] at hre
  rw [Complex.sub_im, cZ_im] at him
  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

end PsiOmega.Locate.Z2

namespace PsiOmega.Locate

/-- **Zero 2** (`ρ ≈ 0.65083008060973708 + 114.16334273075698 i`): a kernel-checked zero of `dh` within `1 / 200` of
`65083 / 100000 + (11416334 / 100000) i`. -/
theorem dh_zero_located_2 : ∃ ρ, dh ρ = 0 ∧ ‖ρ - Z2.cZ‖ < (1 / 200 : ℝ) := Z2.dh_zero_located

/-- **Zero 2** in coordinates. -/
theorem dh_zero_located_box_2 : ∃ ρ : ℂ, dh ρ = 0 ∧ 64583 / 100000 < ρ.re ∧ ρ.re < 65583 / 100000 ∧
    5707917 / 50000 < ρ.im ∧ ρ.im < 5708417 / 50000 := Z2.dh_zero_located_box

end PsiOmega.Locate

#print axioms PsiOmega.Locate.Z2.PReG_mem
#print axioms PsiOmega.Locate.Z2.PImG_mem
#print axioms PsiOmega.Locate.Z2.AReG_mem
#print axioms PsiOmega.Locate.Z2.H1
#print axioms PsiOmega.Locate.Z2.H2
#print axioms PsiOmega.Locate.Z2.H3
#print axioms PsiOmega.Locate.Z2.dh_zero_located
#print axioms PsiOmega.Locate.Z2.dh_zero_located_box
#print axioms PsiOmega.Locate.dh_zero_located_2
#print axioms PsiOmega.Locate.dh_zero_located_box_2
